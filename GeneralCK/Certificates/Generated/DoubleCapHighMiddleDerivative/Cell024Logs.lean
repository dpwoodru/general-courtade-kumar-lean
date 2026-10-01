import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell024
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

theorem reflection_log_1_neg : (29349271 / 125000000) ≤ -Real.log (1024 / 1295) ∧
    -Real.log (1024 / 1295) ≤ (234794169 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2319)) (n := 12)
    (lo := (29349271 / 125000000)) (hi := (234794169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295 / 1024) = 1/(1024 / 1295) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (29349271 / 125000000) (234794169 / 1000000000) (Real.log (1295 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1295 / 1024) = -Real.log (1024 / 1295) := by
    rw [show ((1295 / 1024) : ℝ) = ((1024 / 1295) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307406577 / 1000000000) ≤ -Real.log (753 / 1024) ∧
    -Real.log (753 / 1024) ≤ (153703289 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1777)) (n := 12)
    (lo := (307406577 / 1000000000)) (hi := (153703289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 753) = 1/(753 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-153703289 / 500000000) (-307406577 / 1000000000) (Real.log (753 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11716537 / 50000000) ≤ -Real.log (640 / 809) ∧
    -Real.log (640 / 809) ≤ (234330741 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1449)) (n := 12)
    (lo := (11716537 / 50000000)) (hi := (234330741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809 / 640) = 1/(640 / 809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11716537 / 50000000) (234330741 / 1000000000) (Real.log (809 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (809 / 640) = -Real.log (640 / 809) := by
    rw [show ((809 / 640) : ℝ) = ((640 / 809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (153305041 / 500000000) ≤ -Real.log (471 / 640) ∧
    -Real.log (471 / 640) ≤ (306610083 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 471) = 1/(471 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-306610083 / 1000000000) (-153305041 / 500000000) (Real.log (471 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42915823 / 250000000) ≤ -Real.log (500000 / 593639) ∧
    -Real.log (500000 / 593639) ≤ (171663293 / 1000000000) := by
  have h := checkLog_sound (w := (93639 / 1093639)) (n := 12)
    (lo := (42915823 / 250000000)) (hi := (171663293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593639 / 500000) = 1/(500000 / 593639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42915823 / 250000000) (171663293 / 1000000000) (Real.log (593639 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593639 / 500000) = -Real.log (500000 / 593639) := by
    rw [show ((593639 / 500000) : ℝ) = ((500000 / 593639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (207366171 / 1000000000) ≤ -Real.log (406361 / 500000) ∧
    -Real.log (406361 / 500000) ≤ (51841543 / 250000000) := by
  have h := checkLog_sound (w := (93639 / 906361)) (n := 12)
    (lo := (207366171 / 1000000000)) (hi := (51841543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406361) = 1/(406361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-51841543 / 250000000) (-207366171 / 1000000000) (Real.log (406361 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172016979 / 1000000000) ≤ -Real.log (500000 / 593849) ∧
    -Real.log (500000 / 593849) ≤ (8600849 / 50000000) := by
  have h := checkLog_sound (w := (93849 / 1093849)) (n := 12)
    (lo := (172016979 / 1000000000)) (hi := (8600849 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593849 / 500000) = 1/(500000 / 593849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172016979 / 1000000000) (8600849 / 50000000) (Real.log (593849 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593849 / 500000) = -Real.log (500000 / 593849) := by
    rw [show ((593849 / 500000) : ℝ) = ((500000 / 593849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103941543 / 500000000) ≤ -Real.log (406151 / 500000) ∧
    -Real.log (406151 / 500000) ≤ (207883087 / 1000000000) := by
  have h := checkLog_sound (w := (93849 / 906151)) (n := 12)
    (lo := (103941543 / 500000000)) (hi := (207883087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406151) = 1/(406151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-207883087 / 1000000000) (-103941543 / 500000000) (Real.log (406151 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125509553 / 1000000000) ≤ -Real.log (500000 / 566863) ∧
    -Real.log (500000 / 566863) ≤ (62754777 / 500000000) := by
  have h := checkLog_sound (w := (66863 / 1066863)) (n := 12)
    (lo := (125509553 / 1000000000)) (hi := (62754777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566863 / 500000) = 1/(500000 / 566863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125509553 / 1000000000) (62754777 / 500000000) (Real.log (566863 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (566863 / 500000) = -Real.log (500000 / 566863) := by
    rw [show ((566863 / 500000) : ℝ) = ((500000 / 566863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143554023 / 1000000000) ≤ -Real.log (433137 / 500000) ∧
    -Real.log (433137 / 500000) ≤ (17944253 / 125000000) := by
  have h := checkLog_sound (w := (66863 / 933137)) (n := 12)
    (lo := (143554023 / 1000000000)) (hi := (17944253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433137) = 1/(433137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17944253 / 125000000) (-143554023 / 1000000000) (Real.log (433137 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125778541 / 1000000000) ≤ -Real.log (1000000 / 1134031) ∧
    -Real.log (1000000 / 1134031) ≤ (62889271 / 500000000) := by
  have h := checkLog_sound (w := (134031 / 2134031)) (n := 12)
    (lo := (125778541 / 1000000000)) (hi := (62889271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134031 / 1000000) = 1/(1000000 / 1134031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125778541 / 1000000000) (62889271 / 500000000) (Real.log (1134031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1134031 / 1000000) = -Real.log (1000000 / 1134031) := by
    rw [show ((1134031 / 1000000) : ℝ) = ((1000000 / 1134031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (143906167 / 1000000000) ≤ -Real.log (865969 / 1000000) ∧
    -Real.log (865969 / 1000000) ≤ (17988271 / 125000000) := by
  have h := checkLog_sound (w := (134031 / 1865969)) (n := 12)
    (lo := (143906167 / 1000000000)) (hi := (17988271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865969) = 1/(865969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17988271 / 125000000) (-143906167 / 1000000000) (Real.log (865969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (540940823 / 1000000000) ≤ -Real.log (500000000000 / 858811040339) ∧
    -Real.log (500000000000 / 858811040339) ≤ (67617603 / 125000000) := by
  have h := checkLog_sound (w := (358811040339 / 1358811040339)) (n := 12)
    (lo := (540940823 / 1000000000)) (hi := (67617603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858811040339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858811040339 / 500000000000) = 1/(500000000000 / 858811040339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (540940823 / 1000000000) (67617603 / 125000000) (Real.log (858811040339 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (858811040339 / 500000000000) = -Real.log (500000000000 / 858811040339) := by
    rw [show ((858811040339 / 500000000000) : ℝ) = ((500000000000 / 858811040339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (271100373 / 500000000) ≤ -Real.log (500000000000 / 859893758301) ∧
    -Real.log (500000000000 / 859893758301) ≤ (542200747 / 1000000000) := by
  have h := checkLog_sound (w := (359893758301 / 1359893758301)) (n := 12)
    (lo := (271100373 / 500000000)) (hi := (542200747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859893758301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859893758301 / 500000000000) = 1/(500000000000 / 859893758301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (271100373 / 500000000) (542200747 / 1000000000) (Real.log (859893758301 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (859893758301 / 500000000000) = -Real.log (500000000000 / 859893758301) := by
    rw [show ((859893758301 / 500000000000) : ℝ) = ((500000000000 / 859893758301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (379029463 / 1000000000) ≤ -Real.log (500000000000 / 730433038603) ∧
    -Real.log (500000000000 / 730433038603) ≤ (47378683 / 125000000) := by
  have h := checkLog_sound (w := (230433038603 / 1230433038603)) (n := 12)
    (lo := (379029463 / 1000000000)) (hi := (47378683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730433038603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730433038603 / 500000000000) = 1/(500000000000 / 730433038603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (379029463 / 1000000000) (47378683 / 125000000) (Real.log (730433038603 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (730433038603 / 500000000000) = -Real.log (500000000000 / 730433038603) := by
    rw [show ((730433038603 / 500000000000) : ℝ) = ((500000000000 / 730433038603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (189950033 / 500000000) ≤ -Real.log (62500000000 / 91383654109) ∧
    -Real.log (62500000000 / 91383654109) ≤ (379900067 / 1000000000) := by
  have h := checkLog_sound (w := (28883654109 / 153883654109)) (n := 12)
    (lo := (189950033 / 500000000)) (hi := (379900067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91383654109 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91383654109 / 62500000000) = 1/(62500000000 / 91383654109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (189950033 / 500000000) (379900067 / 1000000000) (Real.log (91383654109 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (91383654109 / 62500000000) = -Real.log (62500000000 / 91383654109) := by
    rw [show ((91383654109 / 62500000000) : ℝ) = ((62500000000 / 91383654109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (33632947 / 125000000) ≤ -Real.log (250000000000 / 327184585939) ∧
    -Real.log (250000000000 / 327184585939) ≤ (269063577 / 1000000000) := by
  have h := checkLog_sound (w := (77184585939 / 577184585939)) (n := 12)
    (lo := (33632947 / 125000000)) (hi := (269063577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327184585939 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327184585939 / 250000000000) = 1/(250000000000 / 327184585939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33632947 / 125000000) (269063577 / 1000000000) (Real.log (327184585939 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (327184585939 / 250000000000) = -Real.log (250000000000 / 327184585939) := by
    rw [show ((327184585939 / 250000000000) : ℝ) = ((250000000000 / 327184585939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269684709 / 1000000000) ≤ -Real.log (125000000000 / 163693937081) ∧
    -Real.log (125000000000 / 163693937081) ≤ (26968471 / 100000000) := by
  have h := checkLog_sound (w := (38693937081 / 288693937081)) (n := 12)
    (lo := (269684709 / 1000000000)) (hi := (26968471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163693937081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163693937081 / 125000000000) = 1/(125000000000 / 163693937081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269684709 / 1000000000) (26968471 / 100000000) (Real.log (163693937081 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (163693937081 / 125000000000) = -Real.log (125000000000 / 163693937081) := by
    rw [show ((163693937081 / 125000000000) : ℝ) = ((125000000000 / 163693937081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9063813 / 500000000) ≤ -Real.log (982035691039 / 1000000000000) ∧
    -Real.log (982035691039 / 1000000000000) ≤ (18127627 / 1000000000) := by
  have h := checkLog_sound (w := (17964308961 / 1982035691039)) (n := 12)
    (lo := (9063813 / 500000000)) (hi := (18127627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982035691039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982035691039) = 1/(982035691039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18127627 / 1000000000) (-9063813 / 500000000) (Real.log (982035691039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18044469 / 1000000000) ≤ -Real.log (245529339231 / 250000000000) ∧
    -Real.log (245529339231 / 250000000000) ≤ (1804447 / 100000000) := by
  have h := checkLog_sound (w := (4470660769 / 495529339231)) (n := 12)
    (lo := (18044469 / 1000000000)) (hi := (1804447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245529339231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245529339231) = 1/(245529339231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1804447 / 100000000) (-18044469 / 1000000000) (Real.log (245529339231 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell024
