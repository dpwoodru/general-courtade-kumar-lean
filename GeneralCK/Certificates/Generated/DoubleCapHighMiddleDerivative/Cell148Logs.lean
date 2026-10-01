import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell148
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

theorem reflection_log_1_neg : (290656161 / 1000000000) ≤ -Real.log (5120 / 6847) ∧
    -Real.log (5120 / 6847) ≤ (145328081 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 11967)) (n := 12)
    (lo := (290656161 / 1000000000)) (hi := (145328081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6847 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6847 / 5120) = 1/(5120 / 6847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (290656161 / 1000000000) (145328081 / 500000000) (Real.log (6847 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6847 / 5120) = -Real.log (5120 / 6847) := by
    rw [show ((6847 / 5120) : ℝ) = ((5120 / 6847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (411439953 / 1000000000) ≤ -Real.log (3393 / 5120) ∧
    -Real.log (3393 / 5120) ≤ (205719977 / 500000000) := by
  have h := checkLog_sound (w := (1727 / 8513)) (n := 12)
    (lo := (411439953 / 1000000000)) (hi := (205719977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3393) = 1/(3393 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-205719977 / 500000000) (-411439953 / 1000000000) (Real.log (3393 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72554479 / 250000000) ≤ -Real.log (1280 / 1711) ∧
    -Real.log (1280 / 1711) ≤ (290217917 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2991)) (n := 12)
    (lo := (72554479 / 250000000)) (hi := (290217917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711 / 1280) = 1/(1280 / 1711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72554479 / 250000000) (290217917 / 1000000000) (Real.log (1711 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1711 / 1280) = -Real.log (1280 / 1711) := by
    rw [show ((1711 / 1280) : ℝ) = ((1280 / 1711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41055617 / 100000000) ≤ -Real.log (849 / 1280) ∧
    -Real.log (849 / 1280) ≤ (410556171 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2129)) (n := 12)
    (lo := (41055617 / 100000000)) (hi := (410556171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 849) = 1/(849 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-410556171 / 1000000000) (-41055617 / 100000000) (Real.log (849 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42905629 / 200000000) ≤ -Real.log (1000000 / 1239277) ∧
    -Real.log (1000000 / 1239277) ≤ (107264073 / 500000000) := by
  have h := checkLog_sound (w := (239277 / 2239277)) (n := 12)
    (lo := (42905629 / 200000000)) (hi := (107264073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239277 / 1000000) = 1/(1000000 / 1239277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42905629 / 200000000) (107264073 / 500000000) (Real.log (1239277 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1239277 / 1000000) = -Real.log (1000000 / 1239277) := by
    rw [show ((1239277 / 1000000) : ℝ) = ((1000000 / 1239277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136742991 / 500000000) ≤ -Real.log (760723 / 1000000) ∧
    -Real.log (760723 / 1000000) ≤ (273485983 / 1000000000) := by
  have h := checkLog_sound (w := (239277 / 1760723)) (n := 12)
    (lo := (136742991 / 500000000)) (hi := (273485983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760723) = 1/(760723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-273485983 / 1000000000) (-136742991 / 500000000) (Real.log (760723 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214867801 / 1000000000) ≤ -Real.log (500000 / 619849) ∧
    -Real.log (500000 / 619849) ≤ (107433901 / 500000000) := by
  have h := checkLog_sound (w := (119849 / 1119849)) (n := 12)
    (lo := (214867801 / 1000000000)) (hi := (107433901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619849 / 500000) = 1/(500000 / 619849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214867801 / 1000000000) (107433901 / 500000000) (Real.log (619849 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619849 / 500000) = -Real.log (500000 / 619849) := by
    rw [show ((619849 / 500000) : ℝ) = ((500000 / 619849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68509889 / 250000000) ≤ -Real.log (380151 / 500000) ∧
    -Real.log (380151 / 500000) ≤ (274039557 / 1000000000) := by
  have h := checkLog_sound (w := (119849 / 880151)) (n := 12)
    (lo := (68509889 / 250000000)) (hi := (274039557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380151) = 1/(380151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-274039557 / 1000000000) (-68509889 / 250000000) (Real.log (380151 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79322141 / 500000000) ≤ -Real.log (1000000 / 1171921) ∧
    -Real.log (1000000 / 1171921) ≤ (158644283 / 1000000000) := by
  have h := checkLog_sound (w := (171921 / 2171921)) (n := 12)
    (lo := (79322141 / 500000000)) (hi := (158644283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171921 / 1000000) = 1/(1000000 / 1171921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79322141 / 500000000) (158644283 / 1000000000) (Real.log (1171921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171921 / 1000000) = -Real.log (1000000 / 1171921) := by
    rw [show ((1171921 / 1000000) : ℝ) = ((1000000 / 1171921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (94323359 / 500000000) ≤ -Real.log (828079 / 1000000) ∧
    -Real.log (828079 / 1000000) ≤ (188646719 / 1000000000) := by
  have h := checkLog_sound (w := (171921 / 1828079)) (n := 12)
    (lo := (94323359 / 500000000)) (hi := (188646719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828079) = 1/(828079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-188646719 / 1000000000) (-94323359 / 500000000) (Real.log (828079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (158911329 / 1000000000) ≤ -Real.log (500000 / 586117) ∧
    -Real.log (500000 / 586117) ≤ (15891133 / 100000000) := by
  have h := checkLog_sound (w := (86117 / 1086117)) (n := 12)
    (lo := (158911329 / 1000000000)) (hi := (15891133 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586117 / 500000) = 1/(500000 / 586117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (158911329 / 1000000000) (15891133 / 100000000) (Real.log (586117 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586117 / 500000) = -Real.log (500000 / 586117) := by
    rw [show ((586117 / 500000) : ℝ) = ((500000 / 586117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (189024773 / 1000000000) ≤ -Real.log (413883 / 500000) ∧
    -Real.log (413883 / 500000) ≤ (94512387 / 500000000) := by
  have h := checkLog_sound (w := (86117 / 913883)) (n := 12)
    (lo := (189024773 / 1000000000)) (hi := (94512387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413883) = 1/(413883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-94512387 / 500000000) (-189024773 / 1000000000) (Real.log (413883 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (700774087 / 1000000000) ≤ -Real.log (500000000000 / 1007656065959) ∧
    -Real.log (500000000000 / 1007656065959) ≤ (700774089 / 1000000000) := by
  have h := checkLog_sound (w := (7656065959 / 2007656065959)) (n := 12)
    (lo := (7626907 / 1000000000)) (hi := (1906727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007656065959 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1007656065959 / 1000000000000) = 1/(500000000000 / 1007656065959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (700774087 / 1000000000) (700774089 / 1000000000) (Real.log (1007656065959 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1007656065959 / 500000000000) = -Real.log (500000000000 / 1007656065959) := by
    rw [show ((1007656065959 / 500000000000) : ℝ) = ((500000000000 / 1007656065959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (702096113 / 1000000000) ≤ -Real.log (125000000000 / 252247273799) ∧
    -Real.log (125000000000 / 252247273799) ≤ (140419223 / 200000000) := by
  have h := checkLog_sound (w := (2247273799 / 502247273799)) (n := 12)
    (lo := (8948933 / 1000000000)) (hi := (4474467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252247273799 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252247273799 / 250000000000) = 1/(125000000000 / 252247273799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (702096113 / 1000000000) (140419223 / 200000000) (Real.log (252247273799 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (252247273799 / 125000000000) = -Real.log (125000000000 / 252247273799) := by
    rw [show ((252247273799 / 125000000000) : ℝ) = ((125000000000 / 252247273799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (488014127 / 1000000000) ≤ -Real.log (250000000000 / 407269466021) ∧
    -Real.log (250000000000 / 407269466021) ≤ (30500883 / 62500000) := by
  have h := checkLog_sound (w := (157269466021 / 657269466021)) (n := 12)
    (lo := (488014127 / 1000000000)) (hi := (30500883 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407269466021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407269466021 / 250000000000) = 1/(250000000000 / 407269466021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (488014127 / 1000000000) (30500883 / 62500000) (Real.log (407269466021 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (407269466021 / 250000000000) = -Real.log (250000000000 / 407269466021) := by
    rw [show ((407269466021 / 250000000000) : ℝ) = ((250000000000 / 407269466021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (488907357 / 1000000000) ≤ -Real.log (250000000000 / 407633414091) ∧
    -Real.log (250000000000 / 407633414091) ≤ (244453679 / 500000000) := by
  have h := checkLog_sound (w := (157633414091 / 657633414091)) (n := 12)
    (lo := (488907357 / 1000000000)) (hi := (244453679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407633414091 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407633414091 / 250000000000) = 1/(250000000000 / 407633414091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (488907357 / 1000000000) (244453679 / 500000000) (Real.log (407633414091 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (407633414091 / 250000000000) = -Real.log (250000000000 / 407633414091) := by
    rw [show ((407633414091 / 250000000000) : ℝ) = ((250000000000 / 407633414091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (347291001 / 1000000000) ≤ -Real.log (100000000000 / 141522849873) ∧
    -Real.log (100000000000 / 141522849873) ≤ (173645501 / 500000000) := by
  have h := checkLog_sound (w := (41522849873 / 241522849873)) (n := 12)
    (lo := (347291001 / 1000000000)) (hi := (173645501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141522849873 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141522849873 / 100000000000) = 1/(100000000000 / 141522849873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (347291001 / 1000000000) (173645501 / 500000000) (Real.log (141522849873 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (141522849873 / 100000000000) = -Real.log (100000000000 / 141522849873) := by
    rw [show ((141522849873 / 100000000000) : ℝ) = ((100000000000 / 141522849873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (347936103 / 1000000000) ≤ -Real.log (100000000000 / 141614175987) ∧
    -Real.log (100000000000 / 141614175987) ≤ (43492013 / 125000000) := by
  have h := checkLog_sound (w := (41614175987 / 241614175987)) (n := 12)
    (lo := (347936103 / 1000000000)) (hi := (43492013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141614175987 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141614175987 / 100000000000) = 1/(100000000000 / 141614175987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (347936103 / 1000000000) (43492013 / 125000000) (Real.log (141614175987 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141614175987 / 100000000000) = -Real.log (100000000000 / 141614175987) := by
    rw [show ((141614175987 / 100000000000) : ℝ) = ((100000000000 / 141614175987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30113443 / 1000000000) ≤ -Real.log (242583862311 / 250000000000) ∧
    -Real.log (242583862311 / 250000000000) ≤ (7528361 / 250000000) := by
  have h := checkLog_sound (w := (7416137689 / 492583862311)) (n := 12)
    (lo := (30113443 / 1000000000)) (hi := (7528361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242583862311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242583862311) = 1/(242583862311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7528361 / 250000000) (-30113443 / 1000000000) (Real.log (242583862311 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6000487 / 200000000) ≤ -Real.log (970443169759 / 1000000000000) ∧
    -Real.log (970443169759 / 1000000000000) ≤ (7500609 / 250000000) := by
  have h := checkLog_sound (w := (29556830241 / 1970443169759)) (n := 12)
    (lo := (6000487 / 200000000)) (hi := (7500609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970443169759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970443169759) = 1/(970443169759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7500609 / 250000000) (-6000487 / 200000000) (Real.log (970443169759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell148
