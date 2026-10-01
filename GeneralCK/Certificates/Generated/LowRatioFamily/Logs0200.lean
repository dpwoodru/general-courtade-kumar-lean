import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12800_neg : (150307871 / 250000000) ≤ -Real.log (125000000000 / 228045511803) ∧
    -Real.log (125000000000 / 228045511803) ≤ (120246297 / 200000000) := by
  have h := checkLog_sound (w := (103045511803 / 353045511803)) (n := 12)
    (lo := (150307871 / 250000000)) (hi := (120246297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228045511803 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228045511803 / 125000000000) = 1/(125000000000 / 228045511803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12800 : Bounds (150307871 / 250000000) (120246297 / 200000000) (Real.log (228045511803 / 125000000000)) := by
  have h := reflection_log_12800_neg
  have he : Real.log (228045511803 / 125000000000) = -Real.log (125000000000 / 228045511803) := by
    rw [show ((228045511803 / 125000000000) : ℝ) = ((125000000000 / 228045511803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12801_neg : (303142729 / 500000000) ≤ -Real.log (125000000000 / 229200965127) ∧
    -Real.log (125000000000 / 229200965127) ≤ (606285459 / 1000000000) := by
  have h := checkLog_sound (w := (104200965127 / 354200965127)) (n := 12)
    (lo := (303142729 / 500000000)) (hi := (606285459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229200965127 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229200965127 / 125000000000) = 1/(125000000000 / 229200965127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12801 : Bounds (303142729 / 500000000) (606285459 / 1000000000) (Real.log (229200965127 / 125000000000)) := by
  have h := reflection_log_12801_neg
  have he : Real.log (229200965127 / 125000000000) = -Real.log (125000000000 / 229200965127) := by
    rw [show ((229200965127 / 125000000000) : ℝ) = ((125000000000 / 229200965127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12802_neg : (619816137 / 500000000) ≤ -Real.log (125000000000 / 431792873051) ∧
    -Real.log (125000000000 / 431792873051) ≤ (309908069 / 250000000) := by
  have h := checkLog_sound (w := (181792873051 / 681792873051)) (n := 12)
    (lo := (273242547 / 500000000)) (hi := (109297019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431792873051 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(431792873051 / 250000000000) = 1/(125000000000 / 431792873051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12802 : Bounds (619816137 / 500000000) (309908069 / 250000000) (Real.log (431792873051 / 125000000000)) := by
  have h := reflection_log_12802_neg
  have he : Real.log (431792873051 / 125000000000) = -Real.log (125000000000 / 431792873051) := by
    rw [show ((431792873051 / 125000000000) : ℝ) = ((125000000000 / 431792873051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12803_neg : (624134289 / 500000000) ≤ -Real.log (7812500000 / 27221132287) ∧
    -Real.log (7812500000 / 27221132287) ≤ (62413429 / 50000000) := by
  have h := checkLog_sound (w := (11596132287 / 42846132287)) (n := 12)
    (lo := (277560699 / 500000000)) (hi := (555121399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27221132287 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(27221132287 / 15625000000) = 1/(7812500000 / 27221132287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12803 : Bounds (624134289 / 500000000) (62413429 / 50000000) (Real.log (27221132287 / 7812500000)) := by
  have h := reflection_log_12803_neg
  have he : Real.log (27221132287 / 7812500000) = -Real.log (7812500000 / 27221132287) := by
    rw [show ((27221132287 / 7812500000) : ℝ) = ((7812500000 / 27221132287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12804_neg : (110690223 / 250000000) ≤ -Real.log (1000 / 1557) ∧
    -Real.log (1000 / 1557) ≤ (442760893 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2557)) (n := 12)
    (lo := (110690223 / 250000000)) (hi := (442760893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1000) = 1/(1000 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12804 : Bounds (110690223 / 250000000) (442760893 / 1000000000) (Real.log (1557 / 1000)) := by
  have h := reflection_log_12804_neg
  have he : Real.log (1557 / 1000) = -Real.log (1000 / 1557) := by
    rw [show ((1557 / 1000) : ℝ) = ((1000 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12805_neg : (203546377 / 250000000) ≤ -Real.log (443 / 1000) ∧
    -Real.log (443 / 1000) ≤ (81418551 / 100000000) := by
  have h := checkLog_sound (w := (57 / 943)) (n := 12)
    (lo := (15129791 / 125000000)) (hi := (121038329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 443) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 443) = 1/(443 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12805 : Bounds (-81418551 / 100000000) (-203546377 / 250000000) (Real.log (443 / 1000)) := by
  have h := reflection_log_12805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12806_neg : (139211 / 250000000) ≤ -Real.log (1000000 / 1000557) ∧
    -Real.log (1000000 / 1000557) ≤ (111369 / 200000000) := by
  have h := checkLog_sound (w := (557 / 2000557)) (n := 12)
    (lo := (139211 / 250000000)) (hi := (111369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000557 / 1000000) = 1/(1000000 / 1000557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12806 : Bounds (139211 / 250000000) (111369 / 200000000) (Real.log (1000557 / 1000000)) := by
  have h := reflection_log_12806_neg
  have he : Real.log (1000557 / 1000000) = -Real.log (1000000 / 1000557) := by
    rw [show ((1000557 / 1000000) : ℝ) = ((1000000 / 1000557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12807_neg : (111431 / 200000000) ≤ -Real.log (999443 / 1000000) ∧
    -Real.log (999443 / 1000000) ≤ (139289 / 250000000) := by
  have h := checkLog_sound (w := (557 / 1999443)) (n := 12)
    (lo := (111431 / 200000000)) (hi := (139289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999443) = 1/(999443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12807 : Bounds (-139289 / 250000000) (-111431 / 200000000) (Real.log (999443 / 1000000)) := by
  have h := reflection_log_12807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12808_neg : (128740797 / 500000000) ≤ -Real.log (250000 / 323417) ∧
    -Real.log (250000 / 323417) ≤ (51496319 / 200000000) := by
  have h := checkLog_sound (w := (73417 / 573417)) (n := 12)
    (lo := (128740797 / 500000000)) (hi := (51496319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323417 / 250000) = 1/(250000 / 323417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12808 : Bounds (128740797 / 500000000) (51496319 / 200000000) (Real.log (323417 / 250000)) := by
  have h := reflection_log_12808_neg
  have he : Real.log (323417 / 250000) = -Real.log (250000 / 323417) := by
    rw [show ((323417 / 250000) : ℝ) = ((250000 / 323417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12809_neg : (347669897 / 1000000000) ≤ -Real.log (176583 / 250000) ∧
    -Real.log (176583 / 250000) ≤ (173834949 / 500000000) := by
  have h := checkLog_sound (w := (73417 / 426583)) (n := 12)
    (lo := (347669897 / 1000000000)) (hi := (173834949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 176583) = 1/(176583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12809 : Bounds (-173834949 / 500000000) (-347669897 / 1000000000) (Real.log (176583 / 250000)) := by
  have h := reflection_log_12809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12810_neg : (64817563 / 250000000) ≤ -Real.log (62500 / 80999) ∧
    -Real.log (62500 / 80999) ≤ (259270253 / 1000000000) := by
  have h := checkLog_sound (w := (18499 / 143499)) (n := 12)
    (lo := (64817563 / 250000000)) (hi := (259270253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80999 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80999 / 62500) = 1/(62500 / 80999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12810 : Bounds (64817563 / 250000000) (259270253 / 1000000000) (Real.log (80999 / 62500)) := by
  have h := reflection_log_12810_neg
  have he : Real.log (80999 / 62500) = -Real.log (62500 / 80999) := by
    rw [show ((80999 / 62500) : ℝ) = ((62500 / 80999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12811_neg : (70190839 / 200000000) ≤ -Real.log (44001 / 62500) ∧
    -Real.log (44001 / 62500) ≤ (87738549 / 250000000) := by
  have h := checkLog_sound (w := (18499 / 106501)) (n := 12)
    (lo := (70190839 / 200000000)) (hi := (87738549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44001) = 1/(44001 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12811 : Bounds (-87738549 / 250000000) (-70190839 / 200000000) (Real.log (44001 / 62500)) := by
  have h := reflection_log_12811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12812_neg : (91683943 / 1000000000) ≤ -Real.log (3564036999 / 3906250000) ∧
    -Real.log (3564036999 / 3906250000) ≤ (11460493 / 125000000) := by
  have h := checkLog_sound (w := (342213001 / 7470286999)) (n := 12)
    (lo := (91683943 / 1000000000)) (hi := (11460493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3564036999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3564036999) = 1/(3564036999 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12812 : Bounds (-11460493 / 125000000) (-91683943 / 1000000000) (Real.log (3564036999 / 3906250000)) := by
  have h := reflection_log_12812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12813_neg : (45094151 / 500000000) ≤ -Real.log (57109944111 / 62500000000) ∧
    -Real.log (57109944111 / 62500000000) ≤ (90188303 / 1000000000) := by
  have h := checkLog_sound (w := (5390055889 / 119609944111)) (n := 12)
    (lo := (45094151 / 500000000)) (hi := (90188303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57109944111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57109944111) = 1/(57109944111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12813 : Bounds (-90188303 / 1000000000) (-45094151 / 500000000) (Real.log (57109944111 / 62500000000)) := by
  have h := reflection_log_12813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12814_neg : (605151491 / 1000000000) ≤ -Real.log (500000000000 / 915764824473) ∧
    -Real.log (500000000000 / 915764824473) ≤ (151287873 / 250000000) := by
  have h := checkLog_sound (w := (415764824473 / 1415764824473)) (n := 12)
    (lo := (605151491 / 1000000000)) (hi := (151287873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915764824473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915764824473 / 500000000000) = 1/(500000000000 / 915764824473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12814 : Bounds (605151491 / 1000000000) (151287873 / 250000000) (Real.log (915764824473 / 500000000000)) := by
  have h := reflection_log_12814_neg
  have he : Real.log (915764824473 / 500000000000) = -Real.log (500000000000 / 915764824473) := by
    rw [show ((915764824473 / 500000000000) : ℝ) = ((500000000000 / 915764824473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12815_neg : (610224447 / 1000000000) ≤ -Real.log (500000000000 / 920422263131) ∧
    -Real.log (500000000000 / 920422263131) ≤ (9534757 / 15625000) := by
  have h := checkLog_sound (w := (420422263131 / 1420422263131)) (n := 12)
    (lo := (610224447 / 1000000000)) (hi := (9534757 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920422263131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(920422263131 / 500000000000) = 1/(500000000000 / 920422263131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12815 : Bounds (610224447 / 1000000000) (9534757 / 15625000) (Real.log (920422263131 / 500000000000)) := by
  have h := reflection_log_12815_neg
  have he : Real.log (920422263131 / 500000000000) = -Real.log (500000000000 / 920422263131) := by
    rw [show ((920422263131 / 500000000000) : ℝ) = ((500000000000 / 920422263131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12816_neg : (624134289 / 500000000) ≤ -Real.log (500000000000 / 1742152466367) ∧
    -Real.log (500000000000 / 1742152466367) ≤ (62413429 / 50000000) := by
  have h := checkLog_sound (w := (742152466367 / 2742152466367)) (n := 12)
    (lo := (277560699 / 500000000)) (hi := (555121399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1742152466367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1742152466367 / 1000000000000) = 1/(500000000000 / 1742152466367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12816 : Bounds (624134289 / 500000000) (62413429 / 50000000) (Real.log (1742152466367 / 500000000000)) := by
  have h := reflection_log_12816_neg
  have he : Real.log (1742152466367 / 500000000000) = -Real.log (500000000000 / 1742152466367) := by
    rw [show ((1742152466367 / 500000000000) : ℝ) = ((500000000000 / 1742152466367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12817_neg : (1256946401 / 1000000000) ≤ -Real.log (125000000000 / 439334085779) ∧
    -Real.log (125000000000 / 439334085779) ≤ (1256946403 / 1000000000) := by
  have h := checkLog_sound (w := (189334085779 / 689334085779)) (n := 12)
    (lo := (563799221 / 1000000000)) (hi := (281899611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439334085779 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(439334085779 / 250000000000) = 1/(125000000000 / 439334085779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12817 : Bounds (1256946401 / 1000000000) (1256946403 / 1000000000) (Real.log (439334085779 / 125000000000)) := by
  have h := reflection_log_12817_neg
  have he : Real.log (439334085779 / 125000000000) = -Real.log (125000000000 / 439334085779) := by
    rw [show ((439334085779 / 125000000000) : ℝ) = ((125000000000 / 439334085779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12818_neg : (444685821 / 1000000000) ≤ -Real.log (25 / 39) ∧
    -Real.log (25 / 39) ≤ (222342911 / 500000000) := by
  have h := checkLog_sound (w := (7 / 32)) (n := 12)
    (lo := (444685821 / 1000000000)) (hi := (222342911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 25) = 1/(25 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12818 : Bounds (444685821 / 1000000000) (222342911 / 500000000) (Real.log (39 / 25)) := by
  have h := reflection_log_12818_neg
  have he : Real.log (39 / 25) = -Real.log (25 / 39) := by
    rw [show ((39 / 25) : ℝ) = ((25 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12819_neg : (820980551 / 1000000000) ≤ -Real.log (11 / 25) ∧
    -Real.log (11 / 25) ≤ (820980553 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 47)) (n := 12)
    (lo := (127833371 / 1000000000)) (hi := (31958343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 22) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 22) = 1/(11 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12819 : Bounds (-820980553 / 1000000000) (-820980551 / 1000000000) (Real.log (11 / 25)) := by
  have h := reflection_log_12819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12820_neg : (559843 / 1000000000) ≤ -Real.log (12500 / 12507) ∧
    -Real.log (12500 / 12507) ≤ (139961 / 250000000) := by
  have h := checkLog_sound (w := (7 / 25007)) (n := 12)
    (lo := (559843 / 1000000000)) (hi := (139961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12507 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12507 / 12500) = 1/(12500 / 12507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12820 : Bounds (559843 / 1000000000) (139961 / 250000000) (Real.log (12507 / 12500)) := by
  have h := reflection_log_12820_neg
  have he : Real.log (12507 / 12500) = -Real.log (12500 / 12507) := by
    rw [show ((12507 / 12500) : ℝ) = ((12500 / 12507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12821_neg : (140039 / 250000000) ≤ -Real.log (12493 / 12500) ∧
    -Real.log (12493 / 12500) ≤ (560157 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 24993)) (n := 12)
    (lo := (140039 / 250000000)) (hi := (560157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 12493) = 1/(12493 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12821 : Bounds (-560157 / 1000000000) (-140039 / 250000000) (Real.log (12493 / 12500)) := by
  have h := reflection_log_12821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12822_neg : (64717233 / 250000000) ≤ -Real.log (125000 / 161933) ∧
    -Real.log (125000 / 161933) ≤ (258868933 / 1000000000) := by
  have h := checkLog_sound (w := (36933 / 286933)) (n := 12)
    (lo := (64717233 / 250000000)) (hi := (258868933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161933 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161933 / 125000) = 1/(125000 / 161933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12822 : Bounds (64717233 / 250000000) (258868933 / 1000000000) (Real.log (161933 / 125000)) := by
  have h := reflection_log_12822_neg
  have he : Real.log (161933 / 125000) = -Real.log (125000 / 161933) := by
    rw [show ((161933 / 125000) : ℝ) = ((125000 / 161933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12823_neg : (43776981 / 125000000) ≤ -Real.log (88067 / 125000) ∧
    -Real.log (88067 / 125000) ≤ (350215849 / 1000000000) := by
  have h := checkLog_sound (w := (36933 / 213067)) (n := 12)
    (lo := (43776981 / 125000000)) (hi := (350215849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88067) = 1/(88067 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12823 : Bounds (-350215849 / 1000000000) (-43776981 / 125000000) (Real.log (88067 / 125000)) := by
  have h := reflection_log_12823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12824_neg : (130330253 / 500000000) ≤ -Real.log (1000000 / 1297787) ∧
    -Real.log (1000000 / 1297787) ≤ (260660507 / 1000000000) := by
  have h := checkLog_sound (w := (297787 / 2297787)) (n := 12)
    (lo := (130330253 / 500000000)) (hi := (260660507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297787 / 1000000) = 1/(1000000 / 1297787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12824 : Bounds (130330253 / 500000000) (260660507 / 1000000000) (Real.log (1297787 / 1000000)) := by
  have h := reflection_log_12824_neg
  have he : Real.log (1297787 / 1000000) = -Real.log (1000000 / 1297787) := by
    rw [show ((1297787 / 1000000) : ℝ) = ((1000000 / 1297787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12825_neg : (176759251 / 500000000) ≤ -Real.log (702213 / 1000000) ∧
    -Real.log (702213 / 1000000) ≤ (353518503 / 1000000000) := by
  have h := checkLog_sound (w := (297787 / 1702213)) (n := 12)
    (lo := (176759251 / 500000000)) (hi := (353518503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702213) = 1/(702213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12825 : Bounds (-353518503 / 1000000000) (-176759251 / 500000000) (Real.log (702213 / 1000000)) := by
  have h := reflection_log_12825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12826_neg : (18571599 / 200000000) ≤ -Real.log (911322902631 / 1000000000000) ∧
    -Real.log (911322902631 / 1000000000000) ≤ (23214499 / 250000000) := by
  have h := checkLog_sound (w := (88677097369 / 1911322902631)) (n := 12)
    (lo := (18571599 / 200000000)) (hi := (23214499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 911322902631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 911322902631) = 1/(911322902631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12826 : Bounds (-23214499 / 250000000) (-18571599 / 200000000) (Real.log (911322902631 / 1000000000000)) := by
  have h := reflection_log_12826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12827_neg : (22836729 / 250000000) ≤ -Real.log (14260953511 / 15625000000) ∧
    -Real.log (14260953511 / 15625000000) ≤ (91346917 / 1000000000) := by
  have h := checkLog_sound (w := (1364046489 / 29885953511)) (n := 12)
    (lo := (22836729 / 250000000)) (hi := (91346917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14260953511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14260953511) = 1/(14260953511 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12827 : Bounds (-91346917 / 1000000000) (-22836729 / 250000000) (Real.log (14260953511 / 15625000000)) := by
  have h := reflection_log_12827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12828_neg : (609084781 / 1000000000) ≤ -Real.log (500000000000 / 919373885791) ∧
    -Real.log (500000000000 / 919373885791) ≤ (304542391 / 500000000) := by
  have h := checkLog_sound (w := (419373885791 / 1419373885791)) (n := 12)
    (lo := (609084781 / 1000000000)) (hi := (304542391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919373885791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919373885791 / 500000000000) = 1/(500000000000 / 919373885791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12828 : Bounds (609084781 / 1000000000) (304542391 / 500000000) (Real.log (919373885791 / 500000000000)) := by
  have h := reflection_log_12828_neg
  have he : Real.log (919373885791 / 500000000000) = -Real.log (500000000000 / 919373885791) := by
    rw [show ((919373885791 / 500000000000) : ℝ) = ((500000000000 / 919373885791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12829_neg : (9596547 / 15625000) ≤ -Real.log (31250000000 / 57754333443) ∧
    -Real.log (31250000000 / 57754333443) ≤ (614179009 / 1000000000) := by
  have h := checkLog_sound (w := (26504333443 / 89004333443)) (n := 12)
    (lo := (9596547 / 15625000)) (hi := (614179009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57754333443 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57754333443 / 31250000000) = 1/(31250000000 / 57754333443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12829 : Bounds (9596547 / 15625000) (614179009 / 1000000000) (Real.log (57754333443 / 31250000000)) := by
  have h := reflection_log_12829_neg
  have he : Real.log (57754333443 / 31250000000) = -Real.log (31250000000 / 57754333443) := by
    rw [show ((57754333443 / 31250000000) : ℝ) = ((31250000000 / 57754333443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12830_neg : (1256946401 / 1000000000) ≤ -Real.log (100000000000 / 351467268623) ∧
    -Real.log (100000000000 / 351467268623) ≤ (1256946403 / 1000000000) := by
  have h := checkLog_sound (w := (151467268623 / 551467268623)) (n := 12)
    (lo := (563799221 / 1000000000)) (hi := (281899611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351467268623 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(351467268623 / 200000000000) = 1/(100000000000 / 351467268623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12830 : Bounds (1256946401 / 1000000000) (1256946403 / 1000000000) (Real.log (351467268623 / 100000000000)) := by
  have h := reflection_log_12830_neg
  have he : Real.log (351467268623 / 100000000000) = -Real.log (100000000000 / 351467268623) := by
    rw [show ((351467268623 / 100000000000) : ℝ) = ((100000000000 / 351467268623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12831_neg : (316416593 / 250000000) ≤ -Real.log (62500000000 / 221590909091) ∧
    -Real.log (62500000000 / 221590909091) ≤ (632833187 / 500000000) := by
  have h := checkLog_sound (w := (96590909091 / 346590909091)) (n := 12)
    (lo := (71564899 / 125000000)) (hi := (572519193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221590909091 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221590909091 / 125000000000) = 1/(62500000000 / 221590909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12831 : Bounds (316416593 / 250000000) (632833187 / 500000000) (Real.log (221590909091 / 62500000000)) := by
  have h := reflection_log_12831_neg
  have he : Real.log (221590909091 / 62500000000) = -Real.log (62500000000 / 221590909091) := by
    rw [show ((221590909091 / 62500000000) : ℝ) = ((62500000000 / 221590909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12832_neg : (446607051 / 1000000000) ≤ -Real.log (1000 / 1563) ∧
    -Real.log (1000 / 1563) ≤ (111651763 / 250000000) := by
  have h := checkLog_sound (w := (563 / 2563)) (n := 12)
    (lo := (446607051 / 1000000000)) (hi := (111651763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1000) = 1/(1000 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12832 : Bounds (446607051 / 1000000000) (111651763 / 250000000) (Real.log (1563 / 1000)) := by
  have h := reflection_log_12832_neg
  have he : Real.log (1563 / 1000) = -Real.log (1000 / 1563) := by
    rw [show ((1563 / 1000) : ℝ) = ((1000 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12833_neg : (827822083 / 1000000000) ≤ -Real.log (437 / 1000) ∧
    -Real.log (437 / 1000) ≤ (165564417 / 200000000) := by
  have h := checkLog_sound (w := (63 / 937)) (n := 12)
    (lo := (134674903 / 1000000000)) (hi := (16834363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 437) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 437) = 1/(437 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12833 : Bounds (-165564417 / 200000000) (-827822083 / 1000000000) (Real.log (437 / 1000)) := by
  have h := reflection_log_12833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12834_neg : (562841 / 1000000000) ≤ -Real.log (1000000 / 1000563) ∧
    -Real.log (1000000 / 1000563) ≤ (281421 / 500000000) := by
  have h := checkLog_sound (w := (563 / 2000563)) (n := 12)
    (lo := (562841 / 1000000000)) (hi := (281421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000563 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000563 / 1000000) = 1/(1000000 / 1000563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12834 : Bounds (562841 / 1000000000) (281421 / 500000000) (Real.log (1000563 / 1000000)) := by
  have h := reflection_log_12834_neg
  have he : Real.log (1000563 / 1000000) = -Real.log (1000000 / 1000563) := by
    rw [show ((1000563 / 1000000) : ℝ) = ((1000000 / 1000563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12835_neg : (281579 / 500000000) ≤ -Real.log (999437 / 1000000) ∧
    -Real.log (999437 / 1000000) ≤ (563159 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1999437)) (n := 12)
    (lo := (281579 / 500000000)) (hi := (563159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999437) = 1/(999437 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12835 : Bounds (-563159 / 1000000000) (-281579 / 500000000) (Real.log (999437 / 1000000)) := by
  have h := reflection_log_12835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12836_neg : (260257431 / 1000000000) ≤ -Real.log (62500 / 81079) ∧
    -Real.log (62500 / 81079) ≤ (32532179 / 125000000) := by
  have h := checkLog_sound (w := (18579 / 143579)) (n := 12)
    (lo := (260257431 / 1000000000)) (hi := (32532179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81079 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81079 / 62500) = 1/(62500 / 81079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12836 : Bounds (260257431 / 1000000000) (32532179 / 125000000) (Real.log (81079 / 62500)) := by
  have h := reflection_log_12836_neg
  have he : Real.log (81079 / 62500) = -Real.log (62500 / 81079) := by
    rw [show ((81079 / 62500) : ℝ) = ((62500 / 81079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12837_neg : (352773991 / 1000000000) ≤ -Real.log (43921 / 62500) ∧
    -Real.log (43921 / 62500) ≤ (44096749 / 125000000) := by
  have h := checkLog_sound (w := (18579 / 106421)) (n := 12)
    (lo := (352773991 / 1000000000)) (hi := (44096749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43921) = 1/(43921 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12837 : Bounds (-44096749 / 125000000) (-352773991 / 1000000000) (Real.log (43921 / 62500)) := by
  have h := reflection_log_12837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12838_neg : (131025569 / 500000000) ≤ -Real.log (1000000 / 1299593) ∧
    -Real.log (1000000 / 1299593) ≤ (262051139 / 1000000000) := by
  have h := checkLog_sound (w := (299593 / 2299593)) (n := 12)
    (lo := (131025569 / 500000000)) (hi := (262051139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299593 / 1000000) = 1/(1000000 / 1299593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12838 : Bounds (131025569 / 500000000) (262051139 / 1000000000) (Real.log (1299593 / 1000000)) := by
  have h := reflection_log_12838_neg
  have he : Real.log (1299593 / 1000000) = -Real.log (1000000 / 1299593) := by
    rw [show ((1299593 / 1000000) : ℝ) = ((1000000 / 1299593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12839_neg : (89023421 / 250000000) ≤ -Real.log (700407 / 1000000) ∧
    -Real.log (700407 / 1000000) ≤ (71218737 / 200000000) := by
  have h := checkLog_sound (w := (299593 / 1700407)) (n := 12)
    (lo := (89023421 / 250000000)) (hi := (71218737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 700407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 700407) = 1/(700407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12839 : Bounds (-71218737 / 200000000) (-89023421 / 250000000) (Real.log (700407 / 1000000)) := by
  have h := reflection_log_12839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12840_neg : (18808509 / 200000000) ≤ -Real.log (910244034351 / 1000000000000) ∧
    -Real.log (910244034351 / 1000000000000) ≤ (47021273 / 500000000) := by
  have h := checkLog_sound (w := (89755965649 / 1910244034351)) (n := 12)
    (lo := (18808509 / 200000000)) (hi := (47021273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 910244034351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 910244034351) = 1/(910244034351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12840 : Bounds (-47021273 / 500000000) (-18808509 / 200000000) (Real.log (910244034351 / 1000000000000)) := by
  have h := reflection_log_12840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12841_neg : (92516559 / 1000000000) ≤ -Real.log (3561070759 / 3906250000) ∧
    -Real.log (3561070759 / 3906250000) ≤ (1156457 / 12500000) := by
  have h := checkLog_sound (w := (345179241 / 7467320759)) (n := 12)
    (lo := (92516559 / 1000000000)) (hi := (1156457 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3561070759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3561070759) = 1/(3561070759 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12841 : Bounds (-1156457 / 12500000) (-92516559 / 1000000000) (Real.log (3561070759 / 3906250000)) := by
  have h := reflection_log_12841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12842_neg : (306515711 / 500000000) ≤ -Real.log (500000000000 / 923009494319) ∧
    -Real.log (500000000000 / 923009494319) ≤ (613031423 / 1000000000) := by
  have h := checkLog_sound (w := (423009494319 / 1423009494319)) (n := 12)
    (lo := (306515711 / 500000000)) (hi := (613031423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923009494319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923009494319 / 500000000000) = 1/(500000000000 / 923009494319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12842 : Bounds (306515711 / 500000000) (613031423 / 1000000000) (Real.log (923009494319 / 500000000000)) := by
  have h := reflection_log_12842_neg
  have he : Real.log (923009494319 / 500000000000) = -Real.log (500000000000 / 923009494319) := by
    rw [show ((923009494319 / 500000000000) : ℝ) = ((500000000000 / 923009494319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12843_neg : (309072411 / 500000000) ≤ -Real.log (125000000000 / 231935324747) ∧
    -Real.log (125000000000 / 231935324747) ≤ (618144823 / 1000000000) := by
  have h := checkLog_sound (w := (106935324747 / 356935324747)) (n := 12)
    (lo := (309072411 / 500000000)) (hi := (618144823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231935324747 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231935324747 / 125000000000) = 1/(125000000000 / 231935324747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12843 : Bounds (309072411 / 500000000) (618144823 / 1000000000) (Real.log (231935324747 / 125000000000)) := by
  have h := reflection_log_12843_neg
  have he : Real.log (231935324747 / 125000000000) = -Real.log (125000000000 / 231935324747) := by
    rw [show ((231935324747 / 125000000000) : ℝ) = ((125000000000 / 231935324747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12844_neg : (316416593 / 250000000) ≤ -Real.log (500000000000 / 1772727272727) ∧
    -Real.log (500000000000 / 1772727272727) ≤ (632833187 / 500000000) := by
  have h := checkLog_sound (w := (772727272727 / 2772727272727)) (n := 12)
    (lo := (71564899 / 125000000)) (hi := (572519193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1772727272727 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1772727272727 / 1000000000000) = 1/(500000000000 / 1772727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12844 : Bounds (316416593 / 250000000) (632833187 / 500000000) (Real.log (1772727272727 / 500000000000)) := by
  have h := reflection_log_12844_neg
  have he : Real.log (1772727272727 / 500000000000) = -Real.log (500000000000 / 1772727272727) := by
    rw [show ((1772727272727 / 500000000000) : ℝ) = ((500000000000 / 1772727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12845_neg : (637214567 / 500000000) ≤ -Real.log (500000000000 / 1788329519451) ∧
    -Real.log (500000000000 / 1788329519451) ≤ (79651821 / 62500000) := by
  have h := checkLog_sound (w := (788329519451 / 2788329519451)) (n := 12)
    (lo := (290640977 / 500000000)) (hi := (116256391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1788329519451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1788329519451 / 1000000000000) = 1/(500000000000 / 1788329519451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12845 : Bounds (637214567 / 500000000) (79651821 / 62500000) (Real.log (1788329519451 / 500000000000)) := by
  have h := reflection_log_12845_neg
  have he : Real.log (1788329519451 / 500000000000) = -Real.log (500000000000 / 1788329519451) := by
    rw [show ((1788329519451 / 500000000000) : ℝ) = ((500000000000 / 1788329519451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12846_neg : (448524597 / 1000000000) ≤ -Real.log (500 / 783) ∧
    -Real.log (500 / 783) ≤ (224262299 / 500000000) := by
  have h := checkLog_sound (w := (283 / 1283)) (n := 12)
    (lo := (448524597 / 1000000000)) (hi := (224262299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 500) = 1/(500 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12846 : Bounds (448524597 / 1000000000) (224262299 / 500000000) (Real.log (783 / 500)) := by
  have h := reflection_log_12846_neg
  have he : Real.log (783 / 500) = -Real.log (500 / 783) := by
    rw [show ((783 / 500) : ℝ) = ((500 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12847_neg : (104338843 / 125000000) ≤ -Real.log (217 / 500) ∧
    -Real.log (217 / 500) ≤ (417355373 / 500000000) := by
  have h := checkLog_sound (w := (33 / 467)) (n := 12)
    (lo := (35390891 / 250000000)) (hi := (28312713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 217) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 217) = 1/(217 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12847 : Bounds (-417355373 / 500000000) (-104338843 / 125000000) (Real.log (217 / 500)) := by
  have h := reflection_log_12847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12848_neg : (565839 / 1000000000) ≤ -Real.log (500000 / 500283) ∧
    -Real.log (500000 / 500283) ≤ (7073 / 12500000) := by
  have h := checkLog_sound (w := (283 / 1000283)) (n := 12)
    (lo := (565839 / 1000000000)) (hi := (7073 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500283 / 500000) = 1/(500000 / 500283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12848 : Bounds (565839 / 1000000000) (7073 / 12500000) (Real.log (500283 / 500000)) := by
  have h := reflection_log_12848_neg
  have he : Real.log (500283 / 500000) = -Real.log (500000 / 500283) := by
    rw [show ((500283 / 500000) : ℝ) = ((500000 / 500283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12849_neg : (7077 / 12500000) ≤ -Real.log (499717 / 500000) ∧
    -Real.log (499717 / 500000) ≤ (566161 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 999717)) (n := 12)
    (lo := (7077 / 12500000)) (hi := (566161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499717) = 1/(499717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12849 : Bounds (-566161 / 1000000000) (-7077 / 12500000) (Real.log (499717 / 500000)) := by
  have h := reflection_log_12849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12850_neg : (65411771 / 250000000) ≤ -Real.log (250000 / 324767) ∧
    -Real.log (250000 / 324767) ≤ (52329417 / 200000000) := by
  have h := checkLog_sound (w := (74767 / 574767)) (n := 12)
    (lo := (65411771 / 250000000)) (hi := (52329417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324767 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324767 / 250000) = 1/(250000 / 324767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12850 : Bounds (65411771 / 250000000) (52329417 / 200000000) (Real.log (324767 / 250000)) := by
  have h := reflection_log_12850_neg
  have he : Real.log (324767 / 250000) = -Real.log (250000 / 324767) := by
    rw [show ((324767 / 250000) : ℝ) = ((250000 / 324767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12851_neg : (888361 / 2500000) ≤ -Real.log (175233 / 250000) ∧
    -Real.log (175233 / 250000) ≤ (355344401 / 1000000000) := by
  have h := checkLog_sound (w := (74767 / 425233)) (n := 12)
    (lo := (888361 / 2500000)) (hi := (355344401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175233) = 1/(175233 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12851 : Bounds (-355344401 / 1000000000) (-888361 / 2500000) (Real.log (175233 / 250000)) := by
  have h := reflection_log_12851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12852_neg : (263442913 / 1000000000) ≤ -Real.log (1000000 / 1301403) ∧
    -Real.log (1000000 / 1301403) ≤ (131721457 / 500000000) := by
  have h := checkLog_sound (w := (301403 / 2301403)) (n := 12)
    (lo := (263442913 / 1000000000)) (hi := (131721457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301403 / 1000000) = 1/(1000000 / 1301403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12852 : Bounds (263442913 / 1000000000) (131721457 / 500000000) (Real.log (1301403 / 1000000)) := by
  have h := reflection_log_12852_neg
  have he : Real.log (1301403 / 1000000) = -Real.log (1000000 / 1301403) := by
    rw [show ((1301403 / 1000000) : ℝ) = ((1000000 / 1301403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12853_neg : (8967031 / 25000000) ≤ -Real.log (698597 / 1000000) ∧
    -Real.log (698597 / 1000000) ≤ (358681241 / 1000000000) := by
  have h := checkLog_sound (w := (301403 / 1698597)) (n := 12)
    (lo := (8967031 / 25000000)) (hi := (358681241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 698597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 698597) = 1/(698597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12853 : Bounds (-358681241 / 1000000000) (-8967031 / 25000000) (Real.log (698597 / 1000000)) := by
  have h := reflection_log_12853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12854_neg : (95238327 / 1000000000) ≤ -Real.log (909156231591 / 1000000000000) ∧
    -Real.log (909156231591 / 1000000000000) ≤ (11904791 / 125000000) := by
  have h := checkLog_sound (w := (90843768409 / 1909156231591)) (n := 12)
    (lo := (95238327 / 1000000000)) (hi := (11904791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 909156231591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 909156231591) = 1/(909156231591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12854 : Bounds (-11904791 / 125000000) (-95238327 / 1000000000) (Real.log (909156231591 / 1000000000000)) := by
  have h := reflection_log_12854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12855_neg : (23424329 / 250000000) ≤ -Real.log (56909895711 / 62500000000) ∧
    -Real.log (56909895711 / 62500000000) ≤ (93697317 / 1000000000) := by
  have h := checkLog_sound (w := (5590104289 / 119409895711)) (n := 12)
    (lo := (23424329 / 250000000)) (hi := (93697317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56909895711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56909895711) = 1/(56909895711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12855 : Bounds (-93697317 / 1000000000) (-23424329 / 250000000) (Real.log (56909895711 / 62500000000)) := by
  have h := reflection_log_12855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12856_neg : (123398297 / 200000000) ≤ -Real.log (500000000000 / 926671916819) ∧
    -Real.log (500000000000 / 926671916819) ≤ (308495743 / 500000000) := by
  have h := checkLog_sound (w := (426671916819 / 1426671916819)) (n := 12)
    (lo := (123398297 / 200000000)) (hi := (308495743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926671916819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926671916819 / 500000000000) = 1/(500000000000 / 926671916819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12856 : Bounds (123398297 / 200000000) (308495743 / 500000000) (Real.log (926671916819 / 500000000000)) := by
  have h := reflection_log_12856_neg
  have he : Real.log (926671916819 / 500000000000) = -Real.log (500000000000 / 926671916819) := by
    rw [show ((926671916819 / 500000000000) : ℝ) = ((500000000000 / 926671916819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12857_neg : (311062077 / 500000000) ≤ -Real.log (100000000000 / 186288088841) ∧
    -Real.log (100000000000 / 186288088841) ≤ (124424831 / 200000000) := by
  have h := checkLog_sound (w := (86288088841 / 286288088841)) (n := 12)
    (lo := (311062077 / 500000000)) (hi := (124424831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186288088841 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186288088841 / 100000000000) = 1/(100000000000 / 186288088841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12857 : Bounds (311062077 / 500000000) (124424831 / 200000000) (Real.log (186288088841 / 100000000000)) := by
  have h := reflection_log_12857_neg
  have he : Real.log (186288088841 / 100000000000) = -Real.log (100000000000 / 186288088841) := by
    rw [show ((186288088841 / 100000000000) : ℝ) = ((100000000000 / 186288088841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12858_neg : (637214567 / 500000000) ≤ -Real.log (10000000000 / 35766590389) ∧
    -Real.log (10000000000 / 35766590389) ≤ (79651821 / 62500000) := by
  have h := checkLog_sound (w := (15766590389 / 55766590389)) (n := 12)
    (lo := (290640977 / 500000000)) (hi := (116256391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35766590389 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(35766590389 / 20000000000) = 1/(10000000000 / 35766590389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12858 : Bounds (637214567 / 500000000) (79651821 / 62500000) (Real.log (35766590389 / 10000000000)) := by
  have h := reflection_log_12858_neg
  have he : Real.log (35766590389 / 10000000000) = -Real.log (10000000000 / 35766590389) := by
    rw [show ((35766590389 / 10000000000) : ℝ) = ((10000000000 / 35766590389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12859_neg : (1283235341 / 1000000000) ≤ -Real.log (250000000000 / 902073732719) ∧
    -Real.log (250000000000 / 902073732719) ≤ (1283235343 / 1000000000) := by
  have h := checkLog_sound (w := (402073732719 / 1402073732719)) (n := 12)
    (lo := (590088161 / 1000000000)) (hi := (295044081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902073732719 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(902073732719 / 500000000000) = 1/(250000000000 / 902073732719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12859 : Bounds (1283235341 / 1000000000) (1283235343 / 1000000000) (Real.log (902073732719 / 250000000000)) := by
  have h := reflection_log_12859_neg
  have he : Real.log (902073732719 / 250000000000) = -Real.log (250000000000 / 902073732719) := by
    rw [show ((902073732719 / 250000000000) : ℝ) = ((250000000000 / 902073732719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12860_neg : (450438473 / 1000000000) ≤ -Real.log (1000 / 1569) ∧
    -Real.log (1000 / 1569) ≤ (225219237 / 500000000) := by
  have h := checkLog_sound (w := (569 / 2569)) (n := 12)
    (lo := (450438473 / 1000000000)) (hi := (225219237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1000) = 1/(1000 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12860 : Bounds (450438473 / 1000000000) (225219237 / 500000000) (Real.log (1569 / 1000)) := by
  have h := reflection_log_12860_neg
  have he : Real.log (1569 / 1000) = -Real.log (1000 / 1569) := by
    rw [show ((1569 / 1000) : ℝ) = ((1000 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12861_neg : (210411797 / 250000000) ≤ -Real.log (431 / 1000) ∧
    -Real.log (431 / 1000) ≤ (84164719 / 100000000) := by
  have h := checkLog_sound (w := (69 / 931)) (n := 12)
    (lo := (18562501 / 125000000)) (hi := (148500009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 431) = 1/(431 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12861 : Bounds (-84164719 / 100000000) (-210411797 / 250000000) (Real.log (431 / 1000)) := by
  have h := reflection_log_12861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12862_neg : (284419 / 500000000) ≤ -Real.log (1000000 / 1000569) ∧
    -Real.log (1000000 / 1000569) ≤ (568839 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 2000569)) (n := 12)
    (lo := (284419 / 500000000)) (hi := (568839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000569 / 1000000) = 1/(1000000 / 1000569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12862 : Bounds (284419 / 500000000) (568839 / 1000000000) (Real.log (1000569 / 1000000)) := by
  have h := reflection_log_12862_neg
  have he : Real.log (1000569 / 1000000) = -Real.log (1000000 / 1000569) := by
    rw [show ((1000569 / 1000000) : ℝ) = ((1000000 / 1000569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12863_neg : (569161 / 1000000000) ≤ -Real.log (999431 / 1000000) ∧
    -Real.log (999431 / 1000000) ≤ (284581 / 500000000) := by
  have h := checkLog_sound (w := (569 / 1999431)) (n := 12)
    (lo := (569161 / 1000000000)) (hi := (284581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999431) = 1/(999431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12863 : Bounds (-284581 / 500000000) (-569161 / 1000000000) (Real.log (999431 / 1000000)) := by
  have h := reflection_log_12863_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
