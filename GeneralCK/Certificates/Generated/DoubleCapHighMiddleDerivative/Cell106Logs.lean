import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell106
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

theorem reflection_log_1_neg : (272082513 / 1000000000) ≤ -Real.log (5120 / 6721) ∧
    -Real.log (5120 / 6721) ≤ (136041257 / 500000000) := by
  have h := checkLog_sound (w := (1601 / 11841)) (n := 12)
    (lo := (272082513 / 1000000000)) (hi := (136041257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6721 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6721 / 5120) = 1/(5120 / 6721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272082513 / 1000000000) (136041257 / 500000000) (Real.log (6721 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6721 / 5120) = -Real.log (5120 / 6721) := by
    rw [show ((6721 / 5120) : ℝ) = ((5120 / 6721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (18748879 / 50000000) ≤ -Real.log (3519 / 5120) ∧
    -Real.log (3519 / 5120) ≤ (374977581 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 8639)) (n := 12)
    (lo := (18748879 / 50000000)) (hi := (374977581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3519) = 1/(3519 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-374977581 / 1000000000) (-18748879 / 50000000) (Real.log (3519 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67909013 / 250000000) ≤ -Real.log (2560 / 3359) ∧
    -Real.log (2560 / 3359) ≤ (271636053 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 5919)) (n := 12)
    (lo := (67909013 / 250000000)) (hi := (271636053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3359 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3359 / 2560) = 1/(2560 / 3359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67909013 / 250000000) (271636053 / 1000000000) (Real.log (3359 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3359 / 2560) = -Real.log (2560 / 3359) := by
    rw [show ((3359 / 2560) : ℝ) = ((2560 / 3359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (93531357 / 250000000) ≤ -Real.log (1761 / 2560) ∧
    -Real.log (1761 / 2560) ≤ (374125429 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 4321)) (n := 12)
    (lo := (93531357 / 250000000)) (hi := (374125429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1761) = 1/(1761 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-374125429 / 1000000000) (-93531357 / 250000000) (Real.log (1761 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40036879 / 200000000) ≤ -Real.log (250000 / 305407) ∧
    -Real.log (250000 / 305407) ≤ (50046099 / 250000000) := by
  have h := checkLog_sound (w := (55407 / 555407)) (n := 12)
    (lo := (40036879 / 200000000)) (hi := (50046099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305407 / 250000) = 1/(250000 / 305407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40036879 / 200000000) (50046099 / 250000000) (Real.log (305407 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (305407 / 250000) = -Real.log (250000 / 305407) := by
    rw [show ((305407 / 250000) : ℝ) = ((250000 / 305407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (250550719 / 1000000000) ≤ -Real.log (194593 / 250000) ∧
    -Real.log (194593 / 250000) ≤ (782971 / 3125000) := by
  have h := checkLog_sound (w := (55407 / 444593)) (n := 12)
    (lo := (250550719 / 1000000000)) (hi := (782971 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194593) = 1/(194593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-782971 / 3125000) (-250550719 / 1000000000) (Real.log (194593 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100264479 / 500000000) ≤ -Real.log (1000000 / 1222049) ∧
    -Real.log (1000000 / 1222049) ≤ (200528959 / 1000000000) := by
  have h := checkLog_sound (w := (222049 / 2222049)) (n := 12)
    (lo := (100264479 / 500000000)) (hi := (200528959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222049 / 1000000) = 1/(1000000 / 1222049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100264479 / 500000000) (200528959 / 1000000000) (Real.log (1222049 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1222049 / 1000000) = -Real.log (1000000 / 1222049) := by
    rw [show ((1222049 / 1000000) : ℝ) = ((1000000 / 1222049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (125545869 / 500000000) ≤ -Real.log (777951 / 1000000) ∧
    -Real.log (777951 / 1000000) ≤ (251091739 / 1000000000) := by
  have h := checkLog_sound (w := (222049 / 1777951)) (n := 12)
    (lo := (125545869 / 500000000)) (hi := (251091739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777951) = 1/(777951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-251091739 / 1000000000) (-125545869 / 500000000) (Real.log (777951 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18431429 / 125000000) ≤ -Real.log (1000000 / 1158877) ∧
    -Real.log (1000000 / 1158877) ≤ (147451433 / 1000000000) := by
  have h := checkLog_sound (w := (158877 / 2158877)) (n := 12)
    (lo := (18431429 / 125000000)) (hi := (147451433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158877 / 1000000) = 1/(1000000 / 1158877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18431429 / 125000000) (147451433 / 1000000000) (Real.log (1158877 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1158877 / 1000000) = -Real.log (1000000 / 1158877) := by
    rw [show ((1158877 / 1000000) : ℝ) = ((1000000 / 1158877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1384139 / 8000000) ≤ -Real.log (841123 / 1000000) ∧
    -Real.log (841123 / 1000000) ≤ (5406793 / 31250000) := by
  have h := checkLog_sound (w := (158877 / 1841123)) (n := 12)
    (lo := (1384139 / 8000000)) (hi := (5406793 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841123) = 1/(841123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5406793 / 31250000) (-1384139 / 8000000) (Real.log (841123 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147718897 / 1000000000) ≤ -Real.log (1000000 / 1159187) ∧
    -Real.log (1000000 / 1159187) ≤ (73859449 / 500000000) := by
  have h := checkLog_sound (w := (159187 / 2159187)) (n := 12)
    (lo := (147718897 / 1000000000)) (hi := (73859449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159187 / 1000000) = 1/(1000000 / 1159187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147718897 / 1000000000) (73859449 / 500000000) (Real.log (1159187 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1159187 / 1000000) = -Real.log (1000000 / 1159187) := by
    rw [show ((1159187 / 1000000) : ℝ) = ((1000000 / 1159187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (86692999 / 500000000) ≤ -Real.log (840813 / 1000000) ∧
    -Real.log (840813 / 1000000) ≤ (173385999 / 1000000000) := by
  have h := checkLog_sound (w := (159187 / 1840813)) (n := 12)
    (lo := (86692999 / 500000000)) (hi := (173385999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840813) = 1/(840813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-173385999 / 1000000000) (-86692999 / 500000000) (Real.log (840813 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (645761481 / 1000000000) ≤ -Real.log (500000000000 / 953719477569) ∧
    -Real.log (500000000000 / 953719477569) ≤ (322880741 / 500000000) := by
  have h := checkLog_sound (w := (453719477569 / 1453719477569)) (n := 12)
    (lo := (645761481 / 1000000000)) (hi := (322880741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953719477569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953719477569 / 500000000000) = 1/(500000000000 / 953719477569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (645761481 / 1000000000) (322880741 / 500000000) (Real.log (953719477569 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (953719477569 / 500000000000) = -Real.log (500000000000 / 953719477569) := by
    rw [show ((953719477569 / 500000000000) : ℝ) = ((500000000000 / 953719477569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (323530047 / 500000000) ≤ -Real.log (500000000000 / 954958795113) ∧
    -Real.log (500000000000 / 954958795113) ≤ (129412019 / 200000000) := by
  have h := checkLog_sound (w := (454958795113 / 1454958795113)) (n := 12)
    (lo := (323530047 / 500000000)) (hi := (129412019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((954958795113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(954958795113 / 500000000000) = 1/(500000000000 / 954958795113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (323530047 / 500000000) (129412019 / 200000000) (Real.log (954958795113 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (954958795113 / 500000000000) = -Real.log (500000000000 / 954958795113) := by
    rw [show ((954958795113 / 500000000000) : ℝ) = ((500000000000 / 954958795113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90147023 / 200000000) ≤ -Real.log (500000000000 / 784732749893) ∧
    -Real.log (500000000000 / 784732749893) ≤ (112683779 / 250000000) := by
  have h := checkLog_sound (w := (284732749893 / 1284732749893)) (n := 12)
    (lo := (90147023 / 200000000)) (hi := (112683779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784732749893 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784732749893 / 500000000000) = 1/(500000000000 / 784732749893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90147023 / 200000000) (112683779 / 250000000) (Real.log (784732749893 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (784732749893 / 500000000000) = -Real.log (500000000000 / 784732749893) := by
    rw [show ((784732749893 / 500000000000) : ℝ) = ((500000000000 / 784732749893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (56452587 / 125000000) ≤ -Real.log (100000000000 / 157085600507) ∧
    -Real.log (100000000000 / 157085600507) ≤ (451620697 / 1000000000) := by
  have h := checkLog_sound (w := (57085600507 / 257085600507)) (n := 12)
    (lo := (56452587 / 125000000)) (hi := (451620697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157085600507 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157085600507 / 100000000000) = 1/(100000000000 / 157085600507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (56452587 / 125000000) (451620697 / 1000000000) (Real.log (157085600507 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (157085600507 / 100000000000) = -Real.log (100000000000 / 157085600507) := by
    rw [show ((157085600507 / 100000000000) : ℝ) = ((100000000000 / 157085600507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (320468807 / 1000000000) ≤ -Real.log (250000000000 / 344443381051) ∧
    -Real.log (250000000000 / 344443381051) ≤ (40058601 / 125000000) := by
  have h := checkLog_sound (w := (94443381051 / 594443381051)) (n := 12)
    (lo := (320468807 / 1000000000)) (hi := (40058601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344443381051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344443381051 / 250000000000) = 1/(250000000000 / 344443381051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (320468807 / 1000000000) (40058601 / 125000000) (Real.log (344443381051 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (344443381051 / 250000000000) = -Real.log (250000000000 / 344443381051) := by
    rw [show ((344443381051 / 250000000000) : ℝ) = ((250000000000 / 344443381051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64220979 / 200000000) ≤ -Real.log (50000000000 / 68932509369) ∧
    -Real.log (50000000000 / 68932509369) ≤ (627158 / 1953125) := by
  have h := checkLog_sound (w := (18932509369 / 118932509369)) (n := 12)
    (lo := (64220979 / 200000000)) (hi := (627158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68932509369 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68932509369 / 50000000000) = 1/(50000000000 / 68932509369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64220979 / 200000000) (627158 / 1953125) (Real.log (68932509369 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68932509369 / 50000000000) = -Real.log (50000000000 / 68932509369) := by
    rw [show ((68932509369 / 50000000000) : ℝ) = ((50000000000 / 68932509369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256671 / 10000000) ≤ -Real.log (974659499031 / 1000000000000) ∧
    -Real.log (974659499031 / 1000000000000) ≤ (25667101 / 1000000000) := by
  have h := checkLog_sound (w := (25340500969 / 1974659499031)) (n := 12)
    (lo := (256671 / 10000000)) (hi := (25667101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974659499031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974659499031) = 1/(974659499031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25667101 / 1000000000) (-256671 / 10000000) (Real.log (974659499031 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12782971 / 500000000) ≤ -Real.log (974758098871 / 1000000000000) ∧
    -Real.log (974758098871 / 1000000000000) ≤ (25565943 / 1000000000) := by
  have h := checkLog_sound (w := (25241901129 / 1974758098871)) (n := 12)
    (lo := (12782971 / 500000000)) (hi := (25565943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974758098871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974758098871) = 1/(974758098871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-25565943 / 1000000000) (-12782971 / 500000000) (Real.log (974758098871 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell106
