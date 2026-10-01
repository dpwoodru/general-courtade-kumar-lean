import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12864_neg : (131518557 / 500000000) ≤ -Real.log (8000 / 10407) ∧
    -Real.log (8000 / 10407) ≤ (52607423 / 200000000) := by
  have h := checkLog_sound (w := (2407 / 18407)) (n := 12)
    (lo := (131518557 / 500000000)) (hi := (52607423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10407 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10407 / 8000) = 1/(8000 / 10407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12864 : Bounds (131518557 / 500000000) (52607423 / 200000000) (Real.log (10407 / 8000)) := by
  have h := reflection_log_12864_neg
  have he : Real.log (10407 / 8000) = -Real.log (8000 / 10407) := by
    rw [show ((10407 / 8000) : ℝ) = ((8000 / 10407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12865_neg : (14317029 / 40000000) ≤ -Real.log (5593 / 8000) ∧
    -Real.log (5593 / 8000) ≤ (178962863 / 500000000) := by
  have h := checkLog_sound (w := (2407 / 13593)) (n := 12)
    (lo := (14317029 / 40000000)) (hi := (178962863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5593) = 1/(5593 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12865 : Bounds (-178962863 / 500000000) (-14317029 / 40000000) (Real.log (5593 / 8000)) := by
  have h := reflection_log_12865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12866_neg : (264835823 / 1000000000) ≤ -Real.log (1000000 / 1303217) ∧
    -Real.log (1000000 / 1303217) ≤ (16552239 / 62500000) := by
  have h := checkLog_sound (w := (303217 / 2303217)) (n := 12)
    (lo := (264835823 / 1000000000)) (hi := (16552239 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303217 / 1000000) = 1/(1000000 / 1303217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12866 : Bounds (264835823 / 1000000000) (16552239 / 62500000) (Real.log (1303217 / 1000000)) := by
  have h := reflection_log_12866_neg
  have he : Real.log (1303217 / 1000000) = -Real.log (1000000 / 1303217) := by
    rw [show ((1303217 / 1000000) : ℝ) = ((1000000 / 1303217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12867_neg : (11561 / 32000) ≤ -Real.log (696783 / 1000000) ∧
    -Real.log (696783 / 1000000) ≤ (361281251 / 1000000000) := by
  have h := checkLog_sound (w := (303217 / 1696783)) (n := 12)
    (lo := (11561 / 32000)) (hi := (361281251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696783) = 1/(696783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12867 : Bounds (-361281251 / 1000000000) (-11561 / 32000) (Real.log (696783 / 1000000)) := by
  have h := reflection_log_12867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12868_neg : (96445427 / 1000000000) ≤ -Real.log (908059450911 / 1000000000000) ∧
    -Real.log (908059450911 / 1000000000000) ≤ (24111357 / 250000000) := by
  have h := checkLog_sound (w := (91940549089 / 1908059450911)) (n := 12)
    (lo := (96445427 / 1000000000)) (hi := (24111357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 908059450911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 908059450911) = 1/(908059450911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12868 : Bounds (-24111357 / 250000000) (-96445427 / 1000000000) (Real.log (908059450911 / 1000000000000)) := by
  have h := reflection_log_12868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12869_neg : (9488861 / 100000000) ≤ -Real.log (58206351 / 64000000) ∧
    -Real.log (58206351 / 64000000) ≤ (94888611 / 1000000000) := by
  have h := checkLog_sound (w := (5793649 / 122206351)) (n := 12)
    (lo := (9488861 / 100000000)) (hi := (94888611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 58206351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 58206351) = 1/(58206351 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12869 : Bounds (-94888611 / 1000000000) (-9488861 / 100000000) (Real.log (58206351 / 64000000)) := by
  have h := reflection_log_12869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12870_neg : (15524071 / 25000000) ≤ -Real.log (500000000000 / 930359377793) ∧
    -Real.log (500000000000 / 930359377793) ≤ (620962841 / 1000000000) := by
  have h := checkLog_sound (w := (430359377793 / 1430359377793)) (n := 12)
    (lo := (15524071 / 25000000)) (hi := (620962841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930359377793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930359377793 / 500000000000) = 1/(500000000000 / 930359377793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12870 : Bounds (15524071 / 25000000) (620962841 / 1000000000) (Real.log (930359377793 / 500000000000)) := by
  have h := reflection_log_12870_neg
  have he : Real.log (930359377793 / 500000000000) = -Real.log (500000000000 / 930359377793) := by
    rw [show ((930359377793 / 500000000000) : ℝ) = ((500000000000 / 930359377793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12871_neg : (313058537 / 500000000) ≤ -Real.log (500000000000 / 935167046269) ∧
    -Real.log (500000000000 / 935167046269) ≤ (25044683 / 40000000) := by
  have h := checkLog_sound (w := (435167046269 / 1435167046269)) (n := 12)
    (lo := (313058537 / 500000000)) (hi := (25044683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935167046269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935167046269 / 500000000000) = 1/(500000000000 / 935167046269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12871 : Bounds (313058537 / 500000000) (25044683 / 40000000) (Real.log (935167046269 / 500000000000)) := by
  have h := reflection_log_12871_neg
  have he : Real.log (935167046269 / 500000000000) = -Real.log (500000000000 / 935167046269) := by
    rw [show ((935167046269 / 500000000000) : ℝ) = ((500000000000 / 935167046269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12872_neg : (1283235341 / 1000000000) ≤ -Real.log (500000000000 / 1804147465437) ∧
    -Real.log (500000000000 / 1804147465437) ≤ (1283235343 / 1000000000) := by
  have h := checkLog_sound (w := (804147465437 / 2804147465437)) (n := 12)
    (lo := (590088161 / 1000000000)) (hi := (295044081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1804147465437 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1804147465437 / 1000000000000) = 1/(500000000000 / 1804147465437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12872 : Bounds (1283235341 / 1000000000) (1283235343 / 1000000000) (Real.log (1804147465437 / 500000000000)) := by
  have h := reflection_log_12872_neg
  have he : Real.log (1804147465437 / 500000000000) = -Real.log (500000000000 / 1804147465437) := by
    rw [show ((1804147465437 / 500000000000) : ℝ) = ((500000000000 / 1804147465437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12873_neg : (646042831 / 500000000) ≤ -Real.log (10000000000 / 36403712297) ∧
    -Real.log (10000000000 / 36403712297) ≤ (40377677 / 31250000) := by
  have h := checkLog_sound (w := (16403712297 / 56403712297)) (n := 12)
    (lo := (299469241 / 500000000)) (hi := (598938483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36403712297 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(36403712297 / 20000000000) = 1/(10000000000 / 36403712297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12873 : Bounds (646042831 / 500000000) (40377677 / 31250000) (Real.log (36403712297 / 10000000000)) := by
  have h := reflection_log_12873_neg
  have he : Real.log (36403712297 / 10000000000) = -Real.log (10000000000 / 36403712297) := by
    rw [show ((36403712297 / 10000000000) : ℝ) = ((10000000000 / 36403712297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12874_neg : (226174347 / 500000000) ≤ -Real.log (250 / 393) ∧
    -Real.log (250 / 393) ≤ (90469739 / 200000000) := by
  have h := checkLog_sound (w := (143 / 643)) (n := 12)
    (lo := (226174347 / 500000000)) (hi := (90469739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 250) = 1/(250 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12874 : Bounds (226174347 / 500000000) (90469739 / 200000000) (Real.log (393 / 250)) := by
  have h := reflection_log_12874_neg
  have he : Real.log (393 / 250) = -Real.log (250 / 393) := by
    rw [show ((393 / 250) : ℝ) = ((250 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12875_neg : (424316041 / 500000000) ≤ -Real.log (107 / 250) ∧
    -Real.log (107 / 250) ≤ (212158021 / 250000000) := by
  have h := checkLog_sound (w := (9 / 116)) (n := 12)
    (lo := (77742451 / 500000000)) (hi := (155484903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 107) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 107) = 1/(107 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12875 : Bounds (-212158021 / 250000000) (-424316041 / 500000000) (Real.log (107 / 250)) := by
  have h := reflection_log_12875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12876_neg : (142959 / 250000000) ≤ -Real.log (250000 / 250143) ∧
    -Real.log (250000 / 250143) ≤ (571837 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 500143)) (n := 12)
    (lo := (142959 / 250000000)) (hi := (571837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250143 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250143 / 250000) = 1/(250000 / 250143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12876 : Bounds (142959 / 250000000) (571837 / 1000000000) (Real.log (250143 / 250000)) := by
  have h := reflection_log_12876_neg
  have he : Real.log (250143 / 250000) = -Real.log (250000 / 250143) := by
    rw [show ((250143 / 250000) : ℝ) = ((250000 / 250143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12877_neg : (572163 / 1000000000) ≤ -Real.log (249857 / 250000) ∧
    -Real.log (249857 / 250000) ≤ (143041 / 250000000) := by
  have h := checkLog_sound (w := (143 / 499857)) (n := 12)
    (lo := (572163 / 1000000000)) (hi := (143041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249857) = 1/(249857 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12877 : Bounds (-143041 / 250000000) (-572163 / 1000000000) (Real.log (249857 / 250000)) := by
  have h := reflection_log_12877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12878_neg : (132214527 / 500000000) ≤ -Real.log (1000000 / 1302687) ∧
    -Real.log (1000000 / 1302687) ≤ (52885811 / 200000000) := by
  have h := checkLog_sound (w := (302687 / 2302687)) (n := 12)
    (lo := (132214527 / 500000000)) (hi := (52885811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302687 / 1000000) = 1/(1000000 / 1302687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12878 : Bounds (132214527 / 500000000) (52885811 / 200000000) (Real.log (1302687 / 1000000)) := by
  have h := reflection_log_12878_neg
  have he : Real.log (1302687 / 1000000) = -Real.log (1000000 / 1302687) := by
    rw [show ((1302687 / 1000000) : ℝ) = ((1000000 / 1302687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12879_neg : (360520901 / 1000000000) ≤ -Real.log (697313 / 1000000) ∧
    -Real.log (697313 / 1000000) ≤ (180260451 / 500000000) := by
  have h := checkLog_sound (w := (302687 / 1697313)) (n := 12)
    (lo := (360520901 / 1000000000)) (hi := (180260451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697313) = 1/(697313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12879 : Bounds (-180260451 / 500000000) (-360520901 / 1000000000) (Real.log (697313 / 1000000)) := by
  have h := reflection_log_12879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12880_neg : (13311493 / 50000000) ≤ -Real.log (200000 / 261007) ∧
    -Real.log (200000 / 261007) ≤ (266229861 / 1000000000) := by
  have h := checkLog_sound (w := (61007 / 461007)) (n := 12)
    (lo := (13311493 / 50000000)) (hi := (266229861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261007 / 200000) = 1/(200000 / 261007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12880 : Bounds (13311493 / 50000000) (266229861 / 1000000000) (Real.log (261007 / 200000)) := by
  have h := reflection_log_12880_neg
  have he : Real.log (261007 / 200000) = -Real.log (200000 / 261007) := by
    rw [show ((261007 / 200000) : ℝ) = ((200000 / 261007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12881_neg : (181946897 / 500000000) ≤ -Real.log (138993 / 200000) ∧
    -Real.log (138993 / 200000) ≤ (72778759 / 200000000) := by
  have h := checkLog_sound (w := (61007 / 338993)) (n := 12)
    (lo := (181946897 / 500000000)) (hi := (72778759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138993) = 1/(138993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12881 : Bounds (-72778759 / 200000000) (-181946897 / 500000000) (Real.log (138993 / 200000)) := by
  have h := reflection_log_12881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12882_neg : (48831967 / 500000000) ≤ -Real.log (36278145951 / 40000000000) ∧
    -Real.log (36278145951 / 40000000000) ≤ (19532787 / 200000000) := by
  have h := checkLog_sound (w := (3721854049 / 76278145951)) (n := 12)
    (lo := (48831967 / 500000000)) (hi := (19532787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36278145951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36278145951) = 1/(36278145951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12882 : Bounds (-19532787 / 200000000) (-48831967 / 500000000) (Real.log (36278145951 / 40000000000)) := by
  have h := reflection_log_12882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12883_neg : (96091847 / 1000000000) ≤ -Real.log (908380580031 / 1000000000000) ∧
    -Real.log (908380580031 / 1000000000000) ≤ (12011481 / 125000000) := by
  have h := checkLog_sound (w := (91619419969 / 1908380580031)) (n := 12)
    (lo := (96091847 / 1000000000)) (hi := (12011481 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 908380580031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 908380580031) = 1/(908380580031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12883 : Bounds (-12011481 / 125000000) (-96091847 / 1000000000) (Real.log (908380580031 / 1000000000000)) := by
  have h := reflection_log_12883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12884_neg : (124989991 / 200000000) ≤ -Real.log (31250000000 / 58379764539) ∧
    -Real.log (31250000000 / 58379764539) ≤ (156237489 / 250000000) := by
  have h := checkLog_sound (w := (27129764539 / 89629764539)) (n := 12)
    (lo := (124989991 / 200000000)) (hi := (156237489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58379764539 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58379764539 / 31250000000) = 1/(31250000000 / 58379764539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12884 : Bounds (124989991 / 200000000) (156237489 / 250000000) (Real.log (58379764539 / 31250000000)) := by
  have h := reflection_log_12884_neg
  have he : Real.log (58379764539 / 31250000000) = -Real.log (31250000000 / 58379764539) := by
    rw [show ((58379764539 / 31250000000) : ℝ) = ((31250000000 / 58379764539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12885_neg : (315061827 / 500000000) ≤ -Real.log (500000000000 / 938921384531) ∧
    -Real.log (500000000000 / 938921384531) ≤ (126024731 / 200000000) := by
  have h := checkLog_sound (w := (438921384531 / 1438921384531)) (n := 12)
    (lo := (315061827 / 500000000)) (hi := (126024731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938921384531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938921384531 / 500000000000) = 1/(500000000000 / 938921384531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12885 : Bounds (315061827 / 500000000) (126024731 / 200000000) (Real.log (938921384531 / 500000000000)) := by
  have h := reflection_log_12885_neg
  have he : Real.log (938921384531 / 500000000000) = -Real.log (500000000000 / 938921384531) := by
    rw [show ((938921384531 / 500000000000) : ℝ) = ((500000000000 / 938921384531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12886_neg : (646042831 / 500000000) ≤ -Real.log (500000000000 / 1820185614849) ∧
    -Real.log (500000000000 / 1820185614849) ≤ (40377677 / 31250000) := by
  have h := checkLog_sound (w := (820185614849 / 2820185614849)) (n := 12)
    (lo := (299469241 / 500000000)) (hi := (598938483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1820185614849 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1820185614849 / 1000000000000) = 1/(500000000000 / 1820185614849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12886 : Bounds (646042831 / 500000000) (40377677 / 31250000) (Real.log (1820185614849 / 500000000000)) := by
  have h := reflection_log_12886_neg
  have he : Real.log (1820185614849 / 500000000000) = -Real.log (500000000000 / 1820185614849) := by
    rw [show ((1820185614849 / 500000000000) : ℝ) = ((500000000000 / 1820185614849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12887_neg : (162622597 / 125000000) ≤ -Real.log (500000000000 / 1836448598131) ∧
    -Real.log (500000000000 / 1836448598131) ≤ (650490389 / 500000000) := by
  have h := checkLog_sound (w := (836448598131 / 2836448598131)) (n := 12)
    (lo := (151958399 / 250000000)) (hi := (607833597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1836448598131 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1836448598131 / 1000000000000) = 1/(500000000000 / 1836448598131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12887 : Bounds (162622597 / 125000000) (650490389 / 500000000) (Real.log (1836448598131 / 500000000000)) := by
  have h := reflection_log_12887_neg
  have he : Real.log (1836448598131 / 500000000000) = -Real.log (500000000000 / 1836448598131) := by
    rw [show ((1836448598131 / 500000000000) : ℝ) = ((500000000000 / 1836448598131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12888_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12888 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_12888_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12889_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12889 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_12889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12890_neg : (287417 / 500000000) ≤ -Real.log (40000 / 40023) ∧
    -Real.log (40000 / 40023) ≤ (114967 / 200000000) := by
  have h := checkLog_sound (w := (23 / 80023)) (n := 12)
    (lo := (287417 / 500000000)) (hi := (114967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40023 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40023 / 40000) = 1/(40000 / 40023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12890 : Bounds (287417 / 500000000) (114967 / 200000000) (Real.log (40023 / 40000)) := by
  have h := reflection_log_12890_neg
  have he : Real.log (40023 / 40000) = -Real.log (40000 / 40023) := by
    rw [show ((40023 / 40000) : ℝ) = ((40000 / 40023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12891_neg : (115033 / 200000000) ≤ -Real.log (39977 / 40000) ∧
    -Real.log (39977 / 40000) ≤ (287583 / 500000000) := by
  have h := checkLog_sound (w := (23 / 79977)) (n := 12)
    (lo := (115033 / 200000000)) (hi := (287583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39977) = 1/(39977 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12891 : Bounds (-287583 / 500000000) (-115033 / 200000000) (Real.log (39977 / 40000)) := by
  have h := reflection_log_12891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12892_neg : (2126577 / 8000000) ≤ -Real.log (1000000 / 1304503) ∧
    -Real.log (1000000 / 1304503) ≤ (132911063 / 500000000) := by
  have h := checkLog_sound (w := (304503 / 2304503)) (n := 12)
    (lo := (2126577 / 8000000)) (hi := (132911063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304503 / 1000000) = 1/(1000000 / 1304503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12892 : Bounds (2126577 / 8000000) (132911063 / 500000000) (Real.log (1304503 / 1000000)) := by
  have h := reflection_log_12892_neg
  have he : Real.log (1304503 / 1000000) = -Real.log (1000000 / 1304503) := by
    rw [show ((1304503 / 1000000) : ℝ) = ((1000000 / 1304503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12893_neg : (363128581 / 1000000000) ≤ -Real.log (695497 / 1000000) ∧
    -Real.log (695497 / 1000000) ≤ (181564291 / 500000000) := by
  have h := checkLog_sound (w := (304503 / 1695497)) (n := 12)
    (lo := (363128581 / 1000000000)) (hi := (181564291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695497) = 1/(695497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12893 : Bounds (-181564291 / 500000000) (-363128581 / 1000000000) (Real.log (695497 / 1000000)) := by
  have h := reflection_log_12893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12894_neg : (267625017 / 1000000000) ≤ -Real.log (1000000 / 1306857) ∧
    -Real.log (1000000 / 1306857) ≤ (133812509 / 500000000) := by
  have h := checkLog_sound (w := (306857 / 2306857)) (n := 12)
    (lo := (267625017 / 1000000000)) (hi := (133812509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306857 / 1000000) = 1/(1000000 / 1306857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12894 : Bounds (267625017 / 1000000000) (133812509 / 500000000) (Real.log (1306857 / 1000000)) := by
  have h := reflection_log_12894_neg
  have he : Real.log (1306857 / 1000000) = -Real.log (1000000 / 1306857) := by
    rw [show ((1306857 / 1000000) : ℝ) = ((1000000 / 1306857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12895_neg : (366518951 / 1000000000) ≤ -Real.log (693143 / 1000000) ∧
    -Real.log (693143 / 1000000) ≤ (45814869 / 125000000) := by
  have h := checkLog_sound (w := (306857 / 1693143)) (n := 12)
    (lo := (366518951 / 1000000000)) (hi := (45814869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693143) = 1/(693143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12895 : Bounds (-45814869 / 125000000) (-366518951 / 1000000000) (Real.log (693143 / 1000000)) := by
  have h := reflection_log_12895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12896_neg : (49446967 / 500000000) ≤ -Real.log (905838781551 / 1000000000000) ∧
    -Real.log (905838781551 / 1000000000000) ≤ (19778787 / 200000000) := by
  have h := checkLog_sound (w := (94161218449 / 1905838781551)) (n := 12)
    (lo := (49446967 / 500000000)) (hi := (19778787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 905838781551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 905838781551) = 1/(905838781551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12896 : Bounds (-19778787 / 200000000) (-49446967 / 500000000) (Real.log (905838781551 / 1000000000000)) := by
  have h := reflection_log_12896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12897_neg : (19461291 / 200000000) ≤ -Real.log (907277922991 / 1000000000000) ∧
    -Real.log (907277922991 / 1000000000000) ≤ (12163307 / 125000000) := by
  have h := checkLog_sound (w := (92722077009 / 1907277922991)) (n := 12)
    (lo := (19461291 / 200000000)) (hi := (12163307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 907277922991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 907277922991) = 1/(907277922991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12897 : Bounds (-12163307 / 125000000) (-19461291 / 200000000) (Real.log (907277922991 / 1000000000000)) := by
  have h := reflection_log_12897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12898_neg : (314475353 / 500000000) ≤ -Real.log (100000000000 / 187564144777) ∧
    -Real.log (100000000000 / 187564144777) ≤ (628950707 / 1000000000) := by
  have h := checkLog_sound (w := (87564144777 / 287564144777)) (n := 12)
    (lo := (314475353 / 500000000)) (hi := (628950707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187564144777 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187564144777 / 100000000000) = 1/(100000000000 / 187564144777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12898 : Bounds (314475353 / 500000000) (628950707 / 1000000000) (Real.log (187564144777 / 100000000000)) := by
  have h := reflection_log_12898_neg
  have he : Real.log (187564144777 / 100000000000) = -Real.log (100000000000 / 187564144777) := by
    rw [show ((187564144777 / 100000000000) : ℝ) = ((100000000000 / 187564144777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12899_neg : (634143969 / 1000000000) ≤ -Real.log (50000000000 / 94270374223) ∧
    -Real.log (50000000000 / 94270374223) ≤ (63414397 / 100000000) := by
  have h := checkLog_sound (w := (44270374223 / 144270374223)) (n := 12)
    (lo := (634143969 / 1000000000)) (hi := (63414397 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94270374223 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94270374223 / 50000000000) = 1/(50000000000 / 94270374223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12899 : Bounds (634143969 / 1000000000) (63414397 / 100000000) (Real.log (94270374223 / 50000000000)) := by
  have h := reflection_log_12899_neg
  have he : Real.log (94270374223 / 50000000000) = -Real.log (50000000000 / 94270374223) := by
    rw [show ((94270374223 / 50000000000) : ℝ) = ((50000000000 / 94270374223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12900_neg : (162622597 / 125000000) ≤ -Real.log (50000000000 / 183644859813) ∧
    -Real.log (50000000000 / 183644859813) ≤ (650490389 / 500000000) := by
  have h := checkLog_sound (w := (83644859813 / 283644859813)) (n := 12)
    (lo := (151958399 / 250000000)) (hi := (607833597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183644859813 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(183644859813 / 100000000000) = 1/(50000000000 / 183644859813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12900 : Bounds (162622597 / 125000000) (650490389 / 500000000) (Real.log (183644859813 / 50000000000)) := by
  have h := reflection_log_12900_neg
  have he : Real.log (183644859813 / 50000000000) = -Real.log (50000000000 / 183644859813) := by
    rw [show ((183644859813 / 50000000000) : ℝ) = ((50000000000 / 183644859813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12901_neg : (1309921381 / 1000000000) ≤ -Real.log (500000000000 / 1852941176471) ∧
    -Real.log (500000000000 / 1852941176471) ≤ (1309921383 / 1000000000) := by
  have h := checkLog_sound (w := (852941176471 / 2852941176471)) (n := 12)
    (lo := (616774201 / 1000000000)) (hi := (308387101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1852941176471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1852941176471 / 1000000000000) = 1/(500000000000 / 1852941176471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12901 : Bounds (1309921381 / 1000000000) (1309921383 / 1000000000) (Real.log (1852941176471 / 500000000000)) := by
  have h := reflection_log_12901_neg
  have he : Real.log (1852941176471 / 500000000000) = -Real.log (500000000000 / 1852941176471) := by
    rw [show ((1852941176471 / 500000000000) : ℝ) = ((500000000000 / 1852941176471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12902_neg : (228079111 / 500000000) ≤ -Real.log (500 / 789) ∧
    -Real.log (500 / 789) ≤ (456158223 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1289)) (n := 12)
    (lo := (228079111 / 500000000)) (hi := (456158223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 500) = 1/(500 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12902 : Bounds (228079111 / 500000000) (456158223 / 1000000000) (Real.log (789 / 500)) := by
  have h := reflection_log_12902_neg
  have he : Real.log (789 / 500) = -Real.log (500 / 789) := by
    rw [show ((789 / 500) : ℝ) = ((500 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12903_neg : (215687491 / 250000000) ≤ -Real.log (211 / 500) ∧
    -Real.log (211 / 500) ≤ (431374983 / 500000000) := by
  have h := checkLog_sound (w := (39 / 461)) (n := 12)
    (lo := (5300087 / 31250000)) (hi := (33920557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 211) = 1/(211 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12903 : Bounds (-431374983 / 500000000) (-215687491 / 250000000) (Real.log (211 / 500)) := by
  have h := reflection_log_12903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12904_neg : (577833 / 1000000000) ≤ -Real.log (500000 / 500289) ∧
    -Real.log (500000 / 500289) ≤ (288917 / 500000000) := by
  have h := checkLog_sound (w := (289 / 1000289)) (n := 12)
    (lo := (577833 / 1000000000)) (hi := (288917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500289 / 500000) = 1/(500000 / 500289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12904 : Bounds (577833 / 1000000000) (288917 / 500000000) (Real.log (500289 / 500000)) := by
  have h := reflection_log_12904_neg
  have he : Real.log (500289 / 500000) = -Real.log (500000 / 500289) := by
    rw [show ((500289 / 500000) : ℝ) = ((500000 / 500289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12905_neg : (578167 / 1000000000) ≤ -Real.log (499711 / 500000) ∧
    -Real.log (499711 / 500000) ≤ (72271 / 125000000) := by
  have h := checkLog_sound (w := (289 / 999711)) (n := 12)
    (lo := (578167 / 1000000000)) (hi := (72271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499711) = 1/(499711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12905 : Bounds (-72271 / 125000000) (-578167 / 1000000000) (Real.log (499711 / 500000)) := by
  have h := reflection_log_12905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12906_neg : (835051 / 3125000) ≤ -Real.log (1000000 / 1306323) ∧
    -Real.log (1000000 / 1306323) ≤ (267216321 / 1000000000) := by
  have h := checkLog_sound (w := (306323 / 2306323)) (n := 12)
    (lo := (835051 / 3125000)) (hi := (267216321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306323 / 1000000) = 1/(1000000 / 1306323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12906 : Bounds (835051 / 3125000) (267216321 / 1000000000) (Real.log (1306323 / 1000000)) := by
  have h := reflection_log_12906_neg
  have he : Real.log (1306323 / 1000000) = -Real.log (1000000 / 1306323) := by
    rw [show ((1306323 / 1000000) : ℝ) = ((1000000 / 1306323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12907_neg : (91437211 / 250000000) ≤ -Real.log (693677 / 1000000) ∧
    -Real.log (693677 / 1000000) ≤ (73149769 / 200000000) := by
  have h := checkLog_sound (w := (306323 / 1693677)) (n := 12)
    (lo := (91437211 / 250000000)) (hi := (73149769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693677) = 1/(693677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12907 : Bounds (-73149769 / 200000000) (-91437211 / 250000000) (Real.log (693677 / 1000000)) := by
  have h := reflection_log_12907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12908_neg : (33627661 / 125000000) ≤ -Real.log (1000000 / 1308683) ∧
    -Real.log (1000000 / 1308683) ≤ (269021289 / 1000000000) := by
  have h := checkLog_sound (w := (308683 / 2308683)) (n := 12)
    (lo := (33627661 / 125000000)) (hi := (269021289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308683 / 1000000) = 1/(1000000 / 1308683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12908 : Bounds (33627661 / 125000000) (269021289 / 1000000000) (Real.log (1308683 / 1000000)) := by
  have h := reflection_log_12908_neg
  have he : Real.log (1308683 / 1000000) = -Real.log (1000000 / 1308683) := by
    rw [show ((1308683 / 1000000) : ℝ) = ((1000000 / 1308683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12909_neg : (92289201 / 250000000) ≤ -Real.log (691317 / 1000000) ∧
    -Real.log (691317 / 1000000) ≤ (73831361 / 200000000) := by
  have h := checkLog_sound (w := (308683 / 1691317)) (n := 12)
    (lo := (92289201 / 250000000)) (hi := (73831361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691317) = 1/(691317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12909 : Bounds (-73831361 / 200000000) (-92289201 / 250000000) (Real.log (691317 / 1000000)) := by
  have h := reflection_log_12909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12910_neg : (25033879 / 250000000) ≤ -Real.log (904714805511 / 1000000000000) ∧
    -Real.log (904714805511 / 1000000000000) ≤ (100135517 / 1000000000) := by
  have h := checkLog_sound (w := (95285194489 / 1904714805511)) (n := 12)
    (lo := (25033879 / 250000000)) (hi := (100135517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 904714805511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 904714805511) = 1/(904714805511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12910 : Bounds (-100135517 / 1000000000) (-25033879 / 250000000) (Real.log (904714805511 / 1000000000000)) := by
  have h := reflection_log_12910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12911_neg : (24633131 / 250000000) ≤ -Real.log (906166219671 / 1000000000000) ∧
    -Real.log (906166219671 / 1000000000000) ≤ (3941301 / 40000000) := by
  have h := checkLog_sound (w := (93833780329 / 1906166219671)) (n := 12)
    (lo := (24633131 / 250000000)) (hi := (3941301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 906166219671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 906166219671) = 1/(906166219671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12911 : Bounds (-3941301 / 40000000) (-24633131 / 250000000) (Real.log (906166219671 / 1000000000000)) := by
  have h := reflection_log_12911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12912_neg : (126593033 / 200000000) ≤ -Real.log (500000000000 / 941593133403) ∧
    -Real.log (500000000000 / 941593133403) ≤ (316482583 / 500000000) := by
  have h := checkLog_sound (w := (441593133403 / 1441593133403)) (n := 12)
    (lo := (126593033 / 200000000)) (hi := (316482583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941593133403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941593133403 / 500000000000) = 1/(500000000000 / 941593133403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12912 : Bounds (126593033 / 200000000) (316482583 / 500000000) (Real.log (941593133403 / 500000000000)) := by
  have h := reflection_log_12912_neg
  have he : Real.log (941593133403 / 500000000000) = -Real.log (500000000000 / 941593133403) := by
    rw [show ((941593133403 / 500000000000) : ℝ) = ((500000000000 / 941593133403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12913_neg : (159544523 / 250000000) ≤ -Real.log (500000000000 / 946514406561) ∧
    -Real.log (500000000000 / 946514406561) ≤ (638178093 / 1000000000) := by
  have h := checkLog_sound (w := (446514406561 / 1446514406561)) (n := 12)
    (lo := (159544523 / 250000000)) (hi := (638178093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946514406561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946514406561 / 500000000000) = 1/(500000000000 / 946514406561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12913 : Bounds (159544523 / 250000000) (638178093 / 1000000000) (Real.log (946514406561 / 500000000000)) := by
  have h := reflection_log_12913_neg
  have he : Real.log (946514406561 / 500000000000) = -Real.log (500000000000 / 946514406561) := by
    rw [show ((946514406561 / 500000000000) : ℝ) = ((500000000000 / 946514406561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12914_neg : (1309921381 / 1000000000) ≤ -Real.log (50000000000 / 185294117647) ∧
    -Real.log (50000000000 / 185294117647) ≤ (1309921383 / 1000000000) := by
  have h := checkLog_sound (w := (85294117647 / 285294117647)) (n := 12)
    (lo := (616774201 / 1000000000)) (hi := (308387101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185294117647 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(185294117647 / 100000000000) = 1/(50000000000 / 185294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12914 : Bounds (1309921381 / 1000000000) (1309921383 / 1000000000) (Real.log (185294117647 / 50000000000)) := by
  have h := reflection_log_12914_neg
  have he : Real.log (185294117647 / 50000000000) = -Real.log (50000000000 / 185294117647) := by
    rw [show ((185294117647 / 50000000000) : ℝ) = ((50000000000 / 185294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12915_neg : (659454093 / 500000000) ≤ -Real.log (250000000000 / 934834123223) ∧
    -Real.log (250000000000 / 934834123223) ≤ (329727047 / 250000000) := by
  have h := checkLog_sound (w := (434834123223 / 1434834123223)) (n := 12)
    (lo := (312880503 / 500000000)) (hi := (625761007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934834123223 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(934834123223 / 500000000000) = 1/(250000000000 / 934834123223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12915 : Bounds (659454093 / 500000000) (329727047 / 250000000) (Real.log (934834123223 / 250000000000)) := by
  have h := reflection_log_12915_neg
  have he : Real.log (934834123223 / 250000000000) = -Real.log (250000000000 / 934834123223) := by
    rw [show ((934834123223 / 250000000000) : ℝ) = ((250000000000 / 934834123223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12916_neg : (229028779 / 500000000) ≤ -Real.log (1000 / 1581) ∧
    -Real.log (1000 / 1581) ≤ (458057559 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 2581)) (n := 12)
    (lo := (229028779 / 500000000)) (hi := (458057559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1000) = 1/(1000 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12916 : Bounds (229028779 / 500000000) (458057559 / 1000000000) (Real.log (1581 / 1000)) := by
  have h := reflection_log_12916_neg
  have he : Real.log (1581 / 1000) = -Real.log (1000 / 1581) := by
    rw [show ((1581 / 1000) : ℝ) = ((1000 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12917_neg : (434942179 / 500000000) ≤ -Real.log (419 / 1000) ∧
    -Real.log (419 / 1000) ≤ (21747109 / 25000000) := by
  have h := checkLog_sound (w := (81 / 919)) (n := 12)
    (lo := (88368589 / 500000000)) (hi := (176737179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 419) = 1/(419 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12917 : Bounds (-21747109 / 25000000) (-434942179 / 500000000) (Real.log (419 / 1000)) := by
  have h := reflection_log_12917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12918_neg : (580831 / 1000000000) ≤ -Real.log (1000000 / 1000581) ∧
    -Real.log (1000000 / 1000581) ≤ (18151 / 31250000) := by
  have h := checkLog_sound (w := (581 / 2000581)) (n := 12)
    (lo := (580831 / 1000000000)) (hi := (18151 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000581 / 1000000) = 1/(1000000 / 1000581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12918 : Bounds (580831 / 1000000000) (18151 / 31250000) (Real.log (1000581 / 1000000)) := by
  have h := reflection_log_12918_neg
  have he : Real.log (1000581 / 1000000) = -Real.log (1000000 / 1000581) := by
    rw [show ((1000581 / 1000000) : ℝ) = ((1000000 / 1000581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12919_neg : (36323 / 62500000) ≤ -Real.log (999419 / 1000000) ∧
    -Real.log (999419 / 1000000) ≤ (581169 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 1999419)) (n := 12)
    (lo := (36323 / 62500000)) (hi := (581169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999419) = 1/(999419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12919 : Bounds (-581169 / 1000000000) (-36323 / 62500000) (Real.log (999419 / 1000000)) := by
  have h := reflection_log_12919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12920_neg : (268610867 / 1000000000) ≤ -Real.log (500000 / 654073) ∧
    -Real.log (500000 / 654073) ≤ (67152717 / 250000000) := by
  have h := checkLog_sound (w := (154073 / 1154073)) (n := 12)
    (lo := (268610867 / 1000000000)) (hi := (67152717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654073 / 500000) = 1/(500000 / 654073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12920 : Bounds (268610867 / 1000000000) (67152717 / 250000000) (Real.log (654073 / 500000)) := by
  have h := reflection_log_12920_neg
  have he : Real.log (654073 / 500000) = -Real.log (500000 / 654073) := by
    rw [show ((654073 / 500000) : ℝ) = ((500000 / 654073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12921_neg : (46047541 / 125000000) ≤ -Real.log (345927 / 500000) ∧
    -Real.log (345927 / 500000) ≤ (368380329 / 1000000000) := by
  have h := checkLog_sound (w := (154073 / 845927)) (n := 12)
    (lo := (46047541 / 125000000)) (hi := (368380329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345927) = 1/(345927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12921 : Bounds (-368380329 / 1000000000) (-46047541 / 125000000) (Real.log (345927 / 500000)) := by
  have h := reflection_log_12921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12922_neg : (54084343 / 200000000) ≤ -Real.log (1000000 / 1310517) ∧
    -Real.log (1000000 / 1310517) ≤ (67605429 / 250000000) := by
  have h := checkLog_sound (w := (310517 / 2310517)) (n := 12)
    (lo := (54084343 / 200000000)) (hi := (67605429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310517 / 1000000) = 1/(1000000 / 1310517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12922 : Bounds (54084343 / 200000000) (67605429 / 250000000) (Real.log (1310517 / 1000000)) := by
  have h := reflection_log_12922_neg
  have he : Real.log (1310517 / 1000000) = -Real.log (1000000 / 1310517) := by
    rw [show ((1310517 / 1000000) : ℝ) = ((1000000 / 1310517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12923_neg : (371813237 / 1000000000) ≤ -Real.log (689483 / 1000000) ∧
    -Real.log (689483 / 1000000) ≤ (185906619 / 500000000) := by
  have h := checkLog_sound (w := (310517 / 1689483)) (n := 12)
    (lo := (371813237 / 1000000000)) (hi := (185906619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689483) = 1/(689483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12923 : Bounds (-185906619 / 500000000) (-371813237 / 1000000000) (Real.log (689483 / 1000000)) := by
  have h := reflection_log_12923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12924_neg : (101391521 / 1000000000) ≤ -Real.log (903579192711 / 1000000000000) ∧
    -Real.log (903579192711 / 1000000000000) ≤ (50695761 / 500000000) := by
  have h := checkLog_sound (w := (96420807289 / 1903579192711)) (n := 12)
    (lo := (101391521 / 1000000000)) (hi := (50695761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 903579192711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 903579192711) = 1/(903579192711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12924 : Bounds (-50695761 / 500000000) (-101391521 / 1000000000) (Real.log (903579192711 / 1000000000000)) := by
  have h := reflection_log_12924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12925_neg : (4988473 / 50000000) ≤ -Real.log (226261510671 / 250000000000) ∧
    -Real.log (226261510671 / 250000000000) ≤ (99769461 / 1000000000) := by
  have h := checkLog_sound (w := (23738489329 / 476261510671)) (n := 12)
    (lo := (4988473 / 50000000)) (hi := (99769461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 226261510671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 226261510671) = 1/(226261510671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12925 : Bounds (-99769461 / 1000000000) (-4988473 / 50000000) (Real.log (226261510671 / 250000000000)) := by
  have h := reflection_log_12925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12926_neg : (127398239 / 200000000) ≤ -Real.log (500000000000 / 945391657777) ∧
    -Real.log (500000000000 / 945391657777) ≤ (159247799 / 250000000) := by
  have h := checkLog_sound (w := (445391657777 / 1445391657777)) (n := 12)
    (lo := (127398239 / 200000000)) (hi := (159247799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945391657777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945391657777 / 500000000000) = 1/(500000000000 / 945391657777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12926 : Bounds (127398239 / 200000000) (159247799 / 250000000) (Real.log (945391657777 / 500000000000)) := by
  have h := reflection_log_12926_neg
  have he : Real.log (945391657777 / 500000000000) = -Real.log (500000000000 / 945391657777) := by
    rw [show ((945391657777 / 500000000000) : ℝ) = ((500000000000 / 945391657777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12927_neg : (642234953 / 1000000000) ≤ -Real.log (250000000000 / 475181041447) ∧
    -Real.log (250000000000 / 475181041447) ≤ (321117477 / 500000000) := by
  have h := checkLog_sound (w := (225181041447 / 725181041447)) (n := 12)
    (lo := (642234953 / 1000000000)) (hi := (321117477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475181041447 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475181041447 / 250000000000) = 1/(250000000000 / 475181041447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12927 : Bounds (642234953 / 1000000000) (321117477 / 500000000) (Real.log (475181041447 / 250000000000)) := by
  have h := reflection_log_12927_neg
  have he : Real.log (475181041447 / 250000000000) = -Real.log (250000000000 / 475181041447) := by
    rw [show ((475181041447 / 250000000000) : ℝ) = ((250000000000 / 475181041447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
