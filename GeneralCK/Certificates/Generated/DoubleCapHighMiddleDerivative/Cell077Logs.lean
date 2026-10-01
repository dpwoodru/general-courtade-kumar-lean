import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell077
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

theorem reflection_log_1_neg : (259053501 / 1000000000) ≤ -Real.log (2560 / 3317) ∧
    -Real.log (2560 / 3317) ≤ (129526751 / 500000000) := by
  have h := checkLog_sound (w := (757 / 5877)) (n := 12)
    (lo := (259053501 / 1000000000)) (hi := (129526751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3317 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3317 / 2560) = 1/(2560 / 3317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (259053501 / 1000000000) (129526751 / 500000000) (Real.log (3317 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3317 / 2560) = -Real.log (2560 / 3317) := by
    rw [show ((3317 / 2560) : ℝ) = ((2560 / 3317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (175277657 / 500000000) ≤ -Real.log (1803 / 2560) ∧
    -Real.log (1803 / 2560) ≤ (70111063 / 200000000) := by
  have h := checkLog_sound (w := (757 / 4363)) (n := 12)
    (lo := (175277657 / 500000000)) (hi := (70111063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1803) = 1/(1803 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-70111063 / 200000000) (-175277657 / 500000000) (Real.log (1803 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (258601183 / 1000000000) ≤ -Real.log (5120 / 6631) ∧
    -Real.log (5120 / 6631) ≤ (8081287 / 31250000) := by
  have h := checkLog_sound (w := (1511 / 11751)) (n := 12)
    (lo := (258601183 / 1000000000)) (hi := (8081287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6631 / 5120) = 1/(5120 / 6631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (258601183 / 1000000000) (8081287 / 31250000) (Real.log (6631 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6631 / 5120) = -Real.log (5120 / 6631) := by
    rw [show ((6631 / 5120) : ℝ) = ((5120 / 6631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (349723713 / 1000000000) ≤ -Real.log (3609 / 5120) ∧
    -Real.log (3609 / 5120) ≤ (174861857 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 8729)) (n := 12)
    (lo := (349723713 / 1000000000)) (hi := (174861857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3609) = 1/(3609 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-174861857 / 500000000) (-349723713 / 1000000000) (Real.log (3609 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190178113 / 1000000000) ≤ -Real.log (200000 / 241893) ∧
    -Real.log (200000 / 241893) ≤ (95089057 / 500000000) := by
  have h := checkLog_sound (w := (41893 / 441893)) (n := 12)
    (lo := (190178113 / 1000000000)) (hi := (95089057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241893 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241893 / 200000) = 1/(200000 / 241893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190178113 / 1000000000) (95089057 / 500000000) (Real.log (241893 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241893 / 200000) = -Real.log (200000 / 241893) := by
    rw [show ((241893 / 200000) : ℝ) = ((200000 / 241893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (235045347 / 1000000000) ≤ -Real.log (158107 / 200000) ∧
    -Real.log (158107 / 200000) ≤ (58761337 / 250000000) := by
  have h := checkLog_sound (w := (41893 / 358107)) (n := 12)
    (lo := (235045347 / 1000000000)) (hi := (58761337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158107) = 1/(158107 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-58761337 / 250000000) (-235045347 / 1000000000) (Real.log (158107 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190525313 / 1000000000) ≤ -Real.log (200000 / 241977) ∧
    -Real.log (200000 / 241977) ≤ (95262657 / 500000000) := by
  have h := checkLog_sound (w := (41977 / 441977)) (n := 12)
    (lo := (190525313 / 1000000000)) (hi := (95262657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241977 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241977 / 200000) = 1/(200000 / 241977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190525313 / 1000000000) (95262657 / 500000000) (Real.log (241977 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241977 / 200000) = -Real.log (200000 / 241977) := by
    rw [show ((241977 / 200000) : ℝ) = ((200000 / 241977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (117788387 / 500000000) ≤ -Real.log (158023 / 200000) ∧
    -Real.log (158023 / 200000) ≤ (9423071 / 40000000) := by
  have h := checkLog_sound (w := (41977 / 358023)) (n := 12)
    (lo := (117788387 / 500000000)) (hi := (9423071 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158023) = 1/(158023 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9423071 / 40000000) (-117788387 / 500000000) (Real.log (158023 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (69853579 / 500000000) ≤ -Real.log (1000000 / 1149937) ∧
    -Real.log (1000000 / 1149937) ≤ (139707159 / 1000000000) := by
  have h := checkLog_sound (w := (149937 / 2149937)) (n := 12)
    (lo := (69853579 / 500000000)) (hi := (139707159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149937 / 1000000) = 1/(1000000 / 1149937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (69853579 / 500000000) (139707159 / 1000000000) (Real.log (1149937 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1149937 / 1000000) = -Real.log (1000000 / 1149937) := by
    rw [show ((1149937 / 1000000) : ℝ) = ((1000000 / 1149937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81222407 / 500000000) ≤ -Real.log (850063 / 1000000) ∧
    -Real.log (850063 / 1000000) ≤ (32488963 / 200000000) := by
  have h := checkLog_sound (w := (149937 / 1850063)) (n := 12)
    (lo := (81222407 / 500000000)) (hi := (32488963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850063) = 1/(850063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32488963 / 200000000) (-81222407 / 500000000) (Real.log (850063 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139974963 / 1000000000) ≤ -Real.log (200000 / 230049) ∧
    -Real.log (200000 / 230049) ≤ (34993741 / 250000000) := by
  have h := checkLog_sound (w := (30049 / 430049)) (n := 12)
    (lo := (139974963 / 1000000000)) (hi := (34993741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230049 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230049 / 200000) = 1/(200000 / 230049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139974963 / 1000000000) (34993741 / 250000000) (Real.log (230049 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (230049 / 200000) = -Real.log (200000 / 230049) := by
    rw [show ((230049 / 200000) : ℝ) = ((200000 / 230049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81403603 / 500000000) ≤ -Real.log (169951 / 200000) ∧
    -Real.log (169951 / 200000) ≤ (162807207 / 1000000000) := by
  have h := checkLog_sound (w := (30049 / 369951)) (n := 12)
    (lo := (81403603 / 500000000)) (hi := (162807207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169951) = 1/(169951 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162807207 / 1000000000) (-81403603 / 500000000) (Real.log (169951 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19010153 / 31250000) ≤ -Real.log (125000000000 / 229668883347) ∧
    -Real.log (125000000000 / 229668883347) ≤ (608324897 / 1000000000) := by
  have h := checkLog_sound (w := (104668883347 / 354668883347)) (n := 12)
    (lo := (19010153 / 31250000)) (hi := (608324897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229668883347 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229668883347 / 125000000000) = 1/(125000000000 / 229668883347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19010153 / 31250000) (608324897 / 1000000000) (Real.log (229668883347 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (229668883347 / 125000000000) = -Real.log (125000000000 / 229668883347) := by
    rw [show ((229668883347 / 125000000000) : ℝ) = ((125000000000 / 229668883347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (121921763 / 200000000) ≤ -Real.log (62500000000 / 114981974487) ∧
    -Real.log (62500000000 / 114981974487) ≤ (38100551 / 62500000) := by
  have h := checkLog_sound (w := (52481974487 / 177481974487)) (n := 12)
    (lo := (121921763 / 200000000)) (hi := (38100551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114981974487 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114981974487 / 62500000000) = 1/(62500000000 / 114981974487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (121921763 / 200000000) (38100551 / 62500000) (Real.log (114981974487 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (114981974487 / 62500000000) = -Real.log (62500000000 / 114981974487) := by
    rw [show ((114981974487 / 62500000000) : ℝ) = ((62500000000 / 114981974487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (21261173 / 50000000) ≤ -Real.log (500000000000 / 764966130531) ∧
    -Real.log (500000000000 / 764966130531) ≤ (425223461 / 1000000000) := by
  have h := checkLog_sound (w := (264966130531 / 1264966130531)) (n := 12)
    (lo := (21261173 / 50000000)) (hi := (425223461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764966130531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764966130531 / 500000000000) = 1/(500000000000 / 764966130531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21261173 / 50000000) (425223461 / 1000000000) (Real.log (764966130531 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (764966130531 / 500000000000) = -Real.log (500000000000 / 764966130531) := by
    rw [show ((764966130531 / 500000000000) : ℝ) = ((500000000000 / 764966130531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53262761 / 125000000) ≤ -Real.log (31250000000 / 47852409143) ∧
    -Real.log (31250000000 / 47852409143) ≤ (426102089 / 1000000000) := by
  have h := checkLog_sound (w := (16602409143 / 79102409143)) (n := 12)
    (lo := (53262761 / 125000000)) (hi := (426102089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47852409143 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47852409143 / 31250000000) = 1/(31250000000 / 47852409143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53262761 / 125000000) (426102089 / 1000000000) (Real.log (47852409143 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (47852409143 / 31250000000) = -Real.log (31250000000 / 47852409143) := by
    rw [show ((47852409143 / 31250000000) : ℝ) = ((31250000000 / 47852409143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (75537993 / 250000000) ≤ -Real.log (100000000000 / 135276679493) ∧
    -Real.log (100000000000 / 135276679493) ≤ (302151973 / 1000000000) := by
  have h := checkLog_sound (w := (35276679493 / 235276679493)) (n := 12)
    (lo := (75537993 / 250000000)) (hi := (302151973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135276679493 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135276679493 / 100000000000) = 1/(100000000000 / 135276679493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (75537993 / 250000000) (302151973 / 1000000000) (Real.log (135276679493 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (135276679493 / 100000000000) = -Real.log (100000000000 / 135276679493) := by
    rw [show ((135276679493 / 100000000000) : ℝ) = ((100000000000 / 135276679493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (302782169 / 1000000000) ≤ -Real.log (500000000000 / 676809786351) ∧
    -Real.log (500000000000 / 676809786351) ≤ (30278217 / 100000000) := by
  have h := checkLog_sound (w := (176809786351 / 1176809786351)) (n := 12)
    (lo := (302782169 / 1000000000)) (hi := (30278217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676809786351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676809786351 / 500000000000) = 1/(500000000000 / 676809786351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (302782169 / 1000000000) (30278217 / 100000000) (Real.log (676809786351 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (676809786351 / 500000000000) = -Real.log (500000000000 / 676809786351) := by
    rw [show ((676809786351 / 500000000000) : ℝ) = ((500000000000 / 676809786351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22832243 / 1000000000) ≤ -Real.log (39097057599 / 40000000000) ∧
    -Real.log (39097057599 / 40000000000) ≤ (5708061 / 250000000) := by
  have h := checkLog_sound (w := (902942401 / 79097057599)) (n := 12)
    (lo := (22832243 / 1000000000)) (hi := (5708061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39097057599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39097057599) = 1/(39097057599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5708061 / 250000000) (-22832243 / 1000000000) (Real.log (39097057599 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2842207 / 125000000) ≤ -Real.log (977518896031 / 1000000000000) ∧
    -Real.log (977518896031 / 1000000000000) ≤ (22737657 / 1000000000) := by
  have h := checkLog_sound (w := (22481103969 / 1977518896031)) (n := 12)
    (lo := (2842207 / 125000000)) (hi := (22737657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977518896031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977518896031) = 1/(977518896031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22737657 / 1000000000) (-2842207 / 125000000) (Real.log (977518896031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell077
