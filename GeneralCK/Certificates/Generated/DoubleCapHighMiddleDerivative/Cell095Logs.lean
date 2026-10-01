import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell095
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

theorem reflection_log_1_neg : (66790109 / 250000000) ≤ -Real.log (160 / 209) ∧
    -Real.log (160 / 209) ≤ (267160437 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 369)) (n := 12)
    (lo := (66790109 / 250000000)) (hi := (267160437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209 / 160) = 1/(160 / 209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66790109 / 250000000) (267160437 / 1000000000) (Real.log (209 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (209 / 160) = -Real.log (160 / 209) := by
    rw [show ((209 / 160) : ℝ) = ((160 / 209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (365643613 / 1000000000) ≤ -Real.log (111 / 160) ∧
    -Real.log (111 / 160) ≤ (182821807 / 500000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 111) = 1/(111 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-182821807 / 500000000) (-365643613 / 1000000000) (Real.log (111 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266711771 / 1000000000) ≤ -Real.log (1024 / 1337) ∧
    -Real.log (1024 / 1337) ≤ (66677943 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2361)) (n := 12)
    (lo := (266711771 / 1000000000)) (hi := (66677943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 1024) = 1/(1024 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266711771 / 1000000000) (66677943 / 250000000) (Real.log (1337 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1337 / 1024) = -Real.log (1024 / 1337) := by
    rw [show ((1337 / 1024) : ℝ) = ((1024 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (583679 / 1600000) ≤ -Real.log (711 / 1024) ∧
    -Real.log (711 / 1024) ≤ (22799961 / 62500000) := by
  have h := checkLog_sound (w := (313 / 1735)) (n := 12)
    (lo := (583679 / 1600000)) (hi := (22799961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 711) = 1/(711 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22799961 / 62500000) (-583679 / 1600000) (Real.log (711 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98199337 / 500000000) ≤ -Real.log (250000 / 304253) ∧
    -Real.log (250000 / 304253) ≤ (7855947 / 40000000) := by
  have h := checkLog_sound (w := (54253 / 554253)) (n := 12)
    (lo := (98199337 / 500000000)) (hi := (7855947 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304253 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304253 / 250000) = 1/(250000 / 304253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98199337 / 500000000) (7855947 / 40000000) (Real.log (304253 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (304253 / 250000) = -Real.log (250000 / 304253) := by
    rw [show ((304253 / 250000) : ℝ) = ((250000 / 304253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (61159477 / 250000000) ≤ -Real.log (195747 / 250000) ∧
    -Real.log (195747 / 250000) ≤ (244637909 / 1000000000) := by
  have h := checkLog_sound (w := (54253 / 445747)) (n := 12)
    (lo := (61159477 / 250000000)) (hi := (244637909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195747) = 1/(195747 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-244637909 / 1000000000) (-61159477 / 250000000) (Real.log (195747 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196744543 / 1000000000) ≤ -Real.log (1000000 / 1217433) ∧
    -Real.log (1000000 / 1217433) ≤ (6148267 / 31250000) := by
  have h := checkLog_sound (w := (217433 / 2217433)) (n := 12)
    (lo := (196744543 / 1000000000)) (hi := (6148267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217433 / 1000000) = 1/(1000000 / 1217433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196744543 / 1000000000) (6148267 / 31250000) (Real.log (1217433 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217433 / 1000000) = -Real.log (1000000 / 1217433) := by
    rw [show ((1217433 / 1000000) : ℝ) = ((1000000 / 1217433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245175737 / 1000000000) ≤ -Real.log (782567 / 1000000) ∧
    -Real.log (782567 / 1000000) ≤ (122587869 / 500000000) := by
  have h := checkLog_sound (w := (217433 / 1782567)) (n := 12)
    (lo := (245175737 / 1000000000)) (hi := (122587869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782567) = 1/(782567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122587869 / 500000000) (-245175737 / 1000000000) (Real.log (782567 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72257921 / 500000000) ≤ -Real.log (25000 / 28887) ∧
    -Real.log (25000 / 28887) ≤ (144515843 / 1000000000) := by
  have h := checkLog_sound (w := (3887 / 53887)) (n := 12)
    (lo := (72257921 / 500000000)) (hi := (144515843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28887 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28887 / 25000) = 1/(25000 / 28887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72257921 / 500000000) (144515843 / 1000000000) (Real.log (28887 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (28887 / 25000) = -Real.log (25000 / 28887) := by
    rw [show ((28887 / 25000) : ℝ) = ((25000 / 28887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8449343 / 50000000) ≤ -Real.log (21113 / 25000) ∧
    -Real.log (21113 / 25000) ≤ (168986861 / 1000000000) := by
  have h := checkLog_sound (w := (3887 / 46113)) (n := 12)
    (lo := (8449343 / 50000000)) (hi := (168986861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21113) = 1/(21113 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168986861 / 1000000000) (-8449343 / 50000000) (Real.log (21113 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144783227 / 1000000000) ≤ -Real.log (1000000 / 1155789) ∧
    -Real.log (1000000 / 1155789) ≤ (36195807 / 250000000) := by
  have h := checkLog_sound (w := (155789 / 2155789)) (n := 12)
    (lo := (144783227 / 1000000000)) (hi := (36195807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155789 / 1000000) = 1/(1000000 / 1155789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144783227 / 1000000000) (36195807 / 250000000) (Real.log (1155789 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1155789 / 1000000) = -Real.log (1000000 / 1155789) := by
    rw [show ((1155789 / 1000000) : ℝ) = ((1000000 / 1155789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33870563 / 200000000) ≤ -Real.log (844211 / 1000000) ∧
    -Real.log (844211 / 1000000) ≤ (10584551 / 62500000) := by
  have h := checkLog_sound (w := (155789 / 1844211)) (n := 12)
    (lo := (33870563 / 200000000)) (hi := (10584551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844211) = 1/(844211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10584551 / 62500000) (-33870563 / 200000000) (Real.log (844211 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (631511147 / 1000000000) ≤ -Real.log (500000000000 / 940225035161) ∧
    -Real.log (500000000000 / 940225035161) ≤ (157877787 / 250000000) := by
  have h := checkLog_sound (w := (440225035161 / 1440225035161)) (n := 12)
    (lo := (631511147 / 1000000000)) (hi := (157877787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940225035161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940225035161 / 500000000000) = 1/(500000000000 / 940225035161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (631511147 / 1000000000) (157877787 / 250000000) (Real.log (940225035161 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (940225035161 / 500000000000) = -Real.log (500000000000 / 940225035161) := by
    rw [show ((940225035161 / 500000000000) : ℝ) = ((500000000000 / 940225035161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (12656081 / 20000000) ≤ -Real.log (250000000000 / 470720720721) ∧
    -Real.log (250000000000 / 470720720721) ≤ (632804051 / 1000000000) := by
  have h := checkLog_sound (w := (220720720721 / 720720720721)) (n := 12)
    (lo := (12656081 / 20000000)) (hi := (632804051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470720720721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470720720721 / 250000000000) = 1/(250000000000 / 470720720721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (12656081 / 20000000) (632804051 / 1000000000) (Real.log (470720720721 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (470720720721 / 250000000000) = -Real.log (250000000000 / 470720720721) := by
    rw [show ((470720720721 / 250000000000) : ℝ) = ((250000000000 / 470720720721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (441036583 / 1000000000) ≤ -Real.log (31250000000 / 48572423843) ∧
    -Real.log (31250000000 / 48572423843) ≤ (55129573 / 125000000) := by
  have h := checkLog_sound (w := (17322423843 / 79822423843)) (n := 12)
    (lo := (441036583 / 1000000000)) (hi := (55129573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48572423843 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48572423843 / 31250000000) = 1/(31250000000 / 48572423843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (441036583 / 1000000000) (55129573 / 125000000) (Real.log (48572423843 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48572423843 / 31250000000) = -Real.log (31250000000 / 48572423843) := by
    rw [show ((48572423843 / 31250000000) : ℝ) = ((31250000000 / 48572423843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11048007 / 25000000) ≤ -Real.log (250000000000 / 388922929283) ∧
    -Real.log (250000000000 / 388922929283) ≤ (441920281 / 1000000000) := by
  have h := checkLog_sound (w := (138922929283 / 638922929283)) (n := 12)
    (lo := (11048007 / 25000000)) (hi := (441920281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388922929283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388922929283 / 250000000000) = 1/(250000000000 / 388922929283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (11048007 / 25000000) (441920281 / 1000000000) (Real.log (388922929283 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (388922929283 / 250000000000) = -Real.log (250000000000 / 388922929283) := by
    rw [show ((388922929283 / 250000000000) : ℝ) = ((250000000000 / 388922929283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (156751351 / 500000000) ≤ -Real.log (125000000000 / 171026145029) ∧
    -Real.log (125000000000 / 171026145029) ≤ (313502703 / 1000000000) := by
  have h := checkLog_sound (w := (46026145029 / 296026145029)) (n := 12)
    (lo := (156751351 / 500000000)) (hi := (313502703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171026145029 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171026145029 / 125000000000) = 1/(125000000000 / 171026145029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (156751351 / 500000000) (313502703 / 1000000000) (Real.log (171026145029 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171026145029 / 125000000000) = -Real.log (125000000000 / 171026145029) := by
    rw [show ((171026145029 / 125000000000) : ℝ) = ((125000000000 / 171026145029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (314136043 / 1000000000) ≤ -Real.log (250000000000 / 342268994363) ∧
    -Real.log (250000000000 / 342268994363) ≤ (78534011 / 250000000) := by
  have h := checkLog_sound (w := (92268994363 / 592268994363)) (n := 12)
    (lo := (314136043 / 1000000000)) (hi := (78534011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342268994363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342268994363 / 250000000000) = 1/(250000000000 / 342268994363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (314136043 / 1000000000) (78534011 / 250000000) (Real.log (342268994363 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342268994363 / 250000000000) = -Real.log (250000000000 / 342268994363) := by
    rw [show ((342268994363 / 250000000000) : ℝ) = ((250000000000 / 342268994363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24569587 / 1000000000) ≤ -Real.log (975729787479 / 1000000000000) ∧
    -Real.log (975729787479 / 1000000000000) ≤ (6142397 / 250000000) := by
  have h := checkLog_sound (w := (24270212521 / 1975729787479)) (n := 12)
    (lo := (24569587 / 1000000000)) (hi := (6142397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975729787479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975729787479) = 1/(975729787479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6142397 / 250000000) (-24569587 / 1000000000) (Real.log (975729787479 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12235509 / 500000000) ≤ -Real.log (609891231 / 625000000) ∧
    -Real.log (609891231 / 625000000) ≤ (24471019 / 1000000000) := by
  have h := checkLog_sound (w := (15108769 / 1234891231)) (n := 12)
    (lo := (12235509 / 500000000)) (hi := (24471019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 609891231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 609891231) = 1/(609891231 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24471019 / 1000000000) (-12235509 / 500000000) (Real.log (609891231 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell095
