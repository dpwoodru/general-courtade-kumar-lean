import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0467
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (92014541 / 500000000) ≤ -Real.log (10240 / 12309) ∧
    -Real.log (10240 / 12309) ≤ (184029083 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 22549)) (n := 12)
    (lo := (92014541 / 500000000)) (hi := (184029083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12309 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12309 / 10240) = 1/(10240 / 12309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92014541 / 500000000) (184029083 / 1000000000) (Real.log (12309 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12309 / 10240) = -Real.log (10240 / 12309) := by
    rw [show ((12309 / 10240) : ℝ) = ((10240 / 12309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225710319 / 1000000000) ≤ -Real.log (8171 / 10240) ∧
    -Real.log (8171 / 10240) ≤ (2821379 / 12500000) := by
  have h := checkLog_sound (w := (2069 / 18411)) (n := 12)
    (lo := (225710319 / 1000000000)) (hi := (2821379 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8171) = 1/(8171 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2821379 / 12500000) (-225710319 / 1000000000) (Real.log (8171 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11486583 / 62500000) ≤ -Real.log (5120 / 6153) ∧
    -Real.log (5120 / 6153) ≤ (183785329 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 11273)) (n := 12)
    (lo := (11486583 / 62500000)) (hi := (183785329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6153 / 5120) = 1/(5120 / 6153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11486583 / 62500000) (183785329 / 1000000000) (Real.log (6153 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6153 / 5120) = -Real.log (5120 / 6153) := by
    rw [show ((6153 / 5120) : ℝ) = ((5120 / 6153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112671617 / 500000000) ≤ -Real.log (4087 / 5120) ∧
    -Real.log (4087 / 5120) ≤ (45068647 / 200000000) := by
  have h := checkLog_sound (w := (1033 / 9207)) (n := 12)
    (lo := (112671617 / 500000000)) (hi := (45068647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4087) = 1/(4087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45068647 / 200000000) (-112671617 / 500000000) (Real.log (4087 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8484941 / 25000000) ≤ -Real.log (5120 / 7189) ∧
    -Real.log (5120 / 7189) ≤ (339397641 / 1000000000) := by
  have h := checkLog_sound (w := (2069 / 12309)) (n := 12)
    (lo := (8484941 / 25000000)) (hi := (339397641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7189 / 5120) = 1/(5120 / 7189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8484941 / 25000000) (339397641 / 1000000000) (Real.log (7189 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7189 / 5120) = -Real.log (5120 / 7189) := by
    rw [show ((7189 / 5120) : ℝ) = ((5120 / 7189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (517685033 / 1000000000) ≤ -Real.log (3051 / 5120) ∧
    -Real.log (3051 / 5120) ≤ (258842517 / 500000000) := by
  have h := checkLog_sound (w := (2069 / 8171)) (n := 12)
    (lo := (517685033 / 1000000000)) (hi := (258842517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3051) = 1/(3051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258842517 / 500000000) (-517685033 / 1000000000) (Real.log (3051 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (338980249 / 1000000000) ≤ -Real.log (2560 / 3593) ∧
    -Real.log (2560 / 3593) ≤ (1355921 / 4000000) := by
  have h := checkLog_sound (w := (1033 / 6153)) (n := 12)
    (lo := (338980249 / 1000000000)) (hi := (1355921 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3593 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3593 / 2560) = 1/(2560 / 3593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (338980249 / 1000000000) (1355921 / 4000000) (Real.log (3593 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3593 / 2560) = -Real.log (2560 / 3593) := by
    rw [show ((3593 / 2560) : ℝ) = ((2560 / 3593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (64587779 / 125000000) ≤ -Real.log (1527 / 2560) ∧
    -Real.log (1527 / 2560) ≤ (516702233 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 4087)) (n := 12)
    (lo := (64587779 / 125000000)) (hi := (516702233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1527) = 1/(1527 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-516702233 / 1000000000) (-64587779 / 125000000) (Real.log (1527 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252630117 / 1000000000) ≤ -Real.log (1000000 / 1287407) ∧
    -Real.log (1000000 / 1287407) ≤ (126315059 / 500000000) := by
  have h := checkLog_sound (w := (287407 / 2287407)) (n := 12)
    (lo := (252630117 / 1000000000)) (hi := (126315059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287407 / 1000000) = 1/(1000000 / 1287407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252630117 / 1000000000) (126315059 / 500000000) (Real.log (1287407 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1287407 / 1000000) = -Real.log (1000000 / 1287407) := by
    rw [show ((1287407 / 1000000) : ℝ) = ((1000000 / 1287407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (338844849 / 1000000000) ≤ -Real.log (712593 / 1000000) ∧
    -Real.log (712593 / 1000000) ≤ (6776897 / 20000000) := by
  have h := checkLog_sound (w := (287407 / 1712593)) (n := 12)
    (lo := (338844849 / 1000000000)) (hi := (6776897 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712593) = 1/(712593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6776897 / 20000000) (-338844849 / 1000000000) (Real.log (712593 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31620023 / 125000000) ≤ -Real.log (125000 / 160979) ∧
    -Real.log (125000 / 160979) ≤ (50592037 / 200000000) := by
  have h := checkLog_sound (w := (35979 / 285979)) (n := 12)
    (lo := (31620023 / 125000000)) (hi := (50592037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160979 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160979 / 125000) = 1/(125000 / 160979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31620023 / 125000000) (50592037 / 200000000) (Real.log (160979 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (160979 / 125000) = -Real.log (125000 / 160979) := by
    rw [show ((160979 / 125000) : ℝ) = ((125000 / 160979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2121509 / 6250000) ≤ -Real.log (89021 / 125000) ∧
    -Real.log (89021 / 125000) ≤ (339441441 / 1000000000) := by
  have h := checkLog_sound (w := (35979 / 214021)) (n := 12)
    (lo := (2121509 / 6250000)) (hi := (339441441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89021) = 1/(89021 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-339441441 / 1000000000) (-2121509 / 6250000) (Real.log (89021 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94476841 / 500000000) ≤ -Real.log (200000 / 241597) ∧
    -Real.log (200000 / 241597) ≤ (188953683 / 1000000000) := by
  have h := checkLog_sound (w := (41597 / 441597)) (n := 12)
    (lo := (94476841 / 500000000)) (hi := (188953683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241597 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241597 / 200000) = 1/(200000 / 241597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94476841 / 500000000) (188953683 / 1000000000) (Real.log (241597 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (241597 / 200000) = -Real.log (200000 / 241597) := by
    rw [show ((241597 / 200000) : ℝ) = ((200000 / 241597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (233174947 / 1000000000) ≤ -Real.log (158403 / 200000) ∧
    -Real.log (158403 / 200000) ≤ (58293737 / 250000000) := by
  have h := checkLog_sound (w := (41597 / 358403)) (n := 12)
    (lo := (233174947 / 1000000000)) (hi := (58293737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158403) = 1/(158403 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58293737 / 250000000) (-233174947 / 1000000000) (Real.log (158403 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94610103 / 500000000) ≤ -Real.log (1000000 / 1208307) ∧
    -Real.log (1000000 / 1208307) ≤ (189220207 / 1000000000) := by
  have h := checkLog_sound (w := (208307 / 2208307)) (n := 12)
    (lo := (94610103 / 500000000)) (hi := (189220207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208307 / 1000000) = 1/(1000000 / 1208307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94610103 / 500000000) (189220207 / 1000000000) (Real.log (1208307 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1208307 / 1000000) = -Real.log (1000000 / 1208307) := by
    rw [show ((1208307 / 1000000) : ℝ) = ((1000000 / 1208307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58395397 / 250000000) ≤ -Real.log (791693 / 1000000) ∧
    -Real.log (791693 / 1000000) ≤ (233581589 / 1000000000) := by
  have h := checkLog_sound (w := (208307 / 1791693)) (n := 12)
    (lo := (58395397 / 250000000)) (hi := (233581589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791693) = 1/(791693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-233581589 / 1000000000) (-58395397 / 250000000) (Real.log (791693 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (295737483 / 500000000) ≤ -Real.log (500000000000 / 903325601009) ∧
    -Real.log (500000000000 / 903325601009) ≤ (591474967 / 1000000000) := by
  have h := checkLog_sound (w := (403325601009 / 1403325601009)) (n := 12)
    (lo := (295737483 / 500000000)) (hi := (591474967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903325601009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903325601009 / 500000000000) = 1/(500000000000 / 903325601009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (295737483 / 500000000) (591474967 / 1000000000) (Real.log (903325601009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (903325601009 / 500000000000) = -Real.log (500000000000 / 903325601009) := by
    rw [show ((903325601009 / 500000000000) : ℝ) = ((500000000000 / 903325601009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (74050203 / 125000000) ≤ -Real.log (500000000000 / 904163062649) ∧
    -Real.log (500000000000 / 904163062649) ≤ (4739213 / 8000000) := by
  have h := checkLog_sound (w := (404163062649 / 1404163062649)) (n := 12)
    (lo := (74050203 / 125000000)) (hi := (4739213 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904163062649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904163062649 / 500000000000) = 1/(500000000000 / 904163062649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (74050203 / 125000000) (4739213 / 8000000) (Real.log (904163062649 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (904163062649 / 500000000000) = -Real.log (500000000000 / 904163062649) := by
    rw [show ((904163062649 / 500000000000) : ℝ) = ((500000000000 / 904163062649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42212863 / 100000000) ≤ -Real.log (250000000000 / 381301174851) ∧
    -Real.log (250000000000 / 381301174851) ≤ (422128631 / 1000000000) := by
  have h := checkLog_sound (w := (131301174851 / 631301174851)) (n := 12)
    (lo := (42212863 / 100000000)) (hi := (422128631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381301174851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381301174851 / 250000000000) = 1/(250000000000 / 381301174851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (42212863 / 100000000) (422128631 / 1000000000) (Real.log (381301174851 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (381301174851 / 250000000000) = -Real.log (250000000000 / 381301174851) := by
    rw [show ((381301174851 / 250000000000) : ℝ) = ((250000000000 / 381301174851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (211400897 / 500000000) ≤ -Real.log (250000000000 / 381557939757) ∧
    -Real.log (250000000000 / 381557939757) ≤ (84560359 / 200000000) := by
  have h := checkLog_sound (w := (131557939757 / 631557939757)) (n := 12)
    (lo := (211400897 / 500000000)) (hi := (84560359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381557939757 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381557939757 / 250000000000) = 1/(250000000000 / 381557939757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (211400897 / 500000000) (84560359 / 200000000) (Real.log (381557939757 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381557939757 / 250000000000) = -Real.log (250000000000 / 381557939757) := by
    rw [show ((381557939757 / 250000000000) : ℝ) = ((250000000000 / 381557939757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0467
