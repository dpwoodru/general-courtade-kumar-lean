import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0446
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

theorem reflection_log_1_neg : (37826847 / 200000000) ≤ -Real.log (2560 / 3093) ∧
    -Real.log (2560 / 3093) ≤ (47283559 / 250000000) := by
  have h := checkLog_sound (w := (533 / 5653)) (n := 12)
    (lo := (37826847 / 200000000)) (hi := (47283559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3093 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3093 / 2560) = 1/(2560 / 3093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37826847 / 200000000) (47283559 / 250000000) (Real.log (3093 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3093 / 2560) = -Real.log (2560 / 3093) := by
    rw [show ((3093 / 2560) : ℝ) = ((2560 / 3093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (233450391 / 1000000000) ≤ -Real.log (2027 / 2560) ∧
    -Real.log (2027 / 2560) ≤ (29181299 / 125000000) := by
  have h := checkLog_sound (w := (533 / 4587)) (n := 12)
    (lo := (233450391 / 1000000000)) (hi := (29181299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2027) = 1/(2027 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-29181299 / 125000000) (-233450391 / 1000000000) (Real.log (2027 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (94445861 / 500000000) ≤ -Real.log (10240 / 12369) ∧
    -Real.log (10240 / 12369) ≤ (188891723 / 1000000000) := by
  have h := checkLog_sound (w := (2129 / 22609)) (n := 12)
    (lo := (94445861 / 500000000)) (hi := (188891723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12369 / 10240) = 1/(10240 / 12369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (94445861 / 500000000) (188891723 / 1000000000) (Real.log (12369 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12369 / 10240) = -Real.log (10240 / 12369) := by
    rw [show ((12369 / 10240) : ℝ) = ((10240 / 12369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (116540227 / 500000000) ≤ -Real.log (8111 / 10240) ∧
    -Real.log (8111 / 10240) ≤ (46616091 / 200000000) := by
  have h := checkLog_sound (w := (2129 / 18351)) (n := 12)
    (lo := (116540227 / 500000000)) (hi := (46616091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8111) = 1/(8111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46616091 / 200000000) (-116540227 / 500000000) (Real.log (8111 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348122853 / 1000000000) ≤ -Real.log (1280 / 1813) ∧
    -Real.log (1280 / 1813) ≤ (174061427 / 500000000) := by
  have h := checkLog_sound (w := (533 / 3093)) (n := 12)
    (lo := (348122853 / 1000000000)) (hi := (174061427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1280) = 1/(1280 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348122853 / 1000000000) (174061427 / 500000000) (Real.log (1813 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1813 / 1280) = -Real.log (1280 / 1813) := by
    rw [show ((1813 / 1280) : ℝ) = ((1280 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (538550171 / 1000000000) ≤ -Real.log (747 / 1280) ∧
    -Real.log (747 / 1280) ≤ (134637543 / 250000000) := by
  have h := checkLog_sound (w := (533 / 2027)) (n := 12)
    (lo := (538550171 / 1000000000)) (hi := (134637543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 747) = 1/(747 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134637543 / 250000000) (-538550171 / 1000000000) (Real.log (747 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (347709089 / 1000000000) ≤ -Real.log (5120 / 7249) ∧
    -Real.log (5120 / 7249) ≤ (34770909 / 100000000) := by
  have h := checkLog_sound (w := (2129 / 12369)) (n := 12)
    (lo := (347709089 / 1000000000)) (hi := (34770909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7249 / 5120) = 1/(5120 / 7249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (347709089 / 1000000000) (34770909 / 100000000) (Real.log (7249 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7249 / 5120) = -Real.log (5120 / 7249) := by
    rw [show ((7249 / 5120) : ℝ) = ((5120 / 7249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (537546659 / 1000000000) ≤ -Real.log (2991 / 5120) ∧
    -Real.log (2991 / 5120) ≤ (26877333 / 50000000) := by
  have h := checkLog_sound (w := (2129 / 8111)) (n := 12)
    (lo := (537546659 / 1000000000)) (hi := (26877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2991) = 1/(2991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26877333 / 50000000) (-537546659 / 1000000000) (Real.log (2991 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259525623 / 1000000000) ≤ -Real.log (200000 / 259263) ∧
    -Real.log (200000 / 259263) ≤ (32440703 / 125000000) := by
  have h := checkLog_sound (w := (59263 / 459263)) (n := 12)
    (lo := (259525623 / 1000000000)) (hi := (32440703 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259263 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259263 / 200000) = 1/(200000 / 259263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259525623 / 1000000000) (32440703 / 125000000) (Real.log (259263 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (259263 / 200000) = -Real.log (200000 / 259263) := by
    rw [show ((259263 / 200000) : ℝ) = ((200000 / 259263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (175712233 / 500000000) ≤ -Real.log (140737 / 200000) ∧
    -Real.log (140737 / 200000) ≤ (351424467 / 1000000000) := by
  have h := checkLog_sound (w := (59263 / 340737)) (n := 12)
    (lo := (175712233 / 500000000)) (hi := (351424467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140737) = 1/(140737 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-351424467 / 1000000000) (-175712233 / 500000000) (Real.log (140737 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (129926711 / 500000000) ≤ -Real.log (50000 / 64837) ∧
    -Real.log (50000 / 64837) ≤ (259853423 / 1000000000) := by
  have h := checkLog_sound (w := (14837 / 114837)) (n := 12)
    (lo := (129926711 / 500000000)) (hi := (259853423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64837 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64837 / 50000) = 1/(50000 / 64837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (129926711 / 500000000) (259853423 / 1000000000) (Real.log (64837 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (64837 / 50000) = -Real.log (50000 / 64837) := by
    rw [show ((64837 / 50000) : ℝ) = ((50000 / 64837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88007153 / 250000000) ≤ -Real.log (35163 / 50000) ∧
    -Real.log (35163 / 50000) ≤ (352028613 / 1000000000) := by
  have h := checkLog_sound (w := (14837 / 85163)) (n := 12)
    (lo := (88007153 / 250000000)) (hi := (352028613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35163) = 1/(35163 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-352028613 / 1000000000) (-88007153 / 250000000) (Real.log (35163 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12158489 / 62500000) ≤ -Real.log (1000000 / 1214747) ∧
    -Real.log (1000000 / 1214747) ≤ (7781433 / 40000000) := by
  have h := checkLog_sound (w := (214747 / 2214747)) (n := 12)
    (lo := (12158489 / 62500000)) (hi := (7781433 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214747 / 1000000) = 1/(1000000 / 1214747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12158489 / 62500000) (7781433 / 40000000) (Real.log (1214747 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1214747 / 1000000) = -Real.log (1000000 / 1214747) := by
    rw [show ((1214747 / 1000000) : ℝ) = ((1000000 / 1214747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6043733 / 25000000) ≤ -Real.log (785253 / 1000000) ∧
    -Real.log (785253 / 1000000) ≤ (241749321 / 1000000000) := by
  have h := checkLog_sound (w := (214747 / 1785253)) (n := 12)
    (lo := (6043733 / 25000000)) (hi := (241749321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785253) = 1/(785253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-241749321 / 1000000000) (-6043733 / 25000000) (Real.log (785253 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194802511 / 1000000000) ≤ -Real.log (1000000 / 1215071) ∧
    -Real.log (1000000 / 1215071) ≤ (12175157 / 62500000) := by
  have h := checkLog_sound (w := (215071 / 2215071)) (n := 12)
    (lo := (194802511 / 1000000000)) (hi := (12175157 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215071 / 1000000) = 1/(1000000 / 1215071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194802511 / 1000000000) (12175157 / 62500000) (Real.log (1215071 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1215071 / 1000000) = -Real.log (1000000 / 1215071) := by
    rw [show ((1215071 / 1000000) : ℝ) = ((1000000 / 1215071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (242162011 / 1000000000) ≤ -Real.log (784929 / 1000000) ∧
    -Real.log (784929 / 1000000) ≤ (60540503 / 250000000) := by
  have h := checkLog_sound (w := (215071 / 1784929)) (n := 12)
    (lo := (242162011 / 1000000000)) (hi := (60540503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784929) = 1/(784929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60540503 / 250000000) (-242162011 / 1000000000) (Real.log (784929 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (61095009 / 100000000) ≤ -Real.log (100000000000 / 184218080533) ∧
    -Real.log (100000000000 / 184218080533) ≤ (610950091 / 1000000000) := by
  have h := checkLog_sound (w := (84218080533 / 284218080533)) (n := 12)
    (lo := (61095009 / 100000000)) (hi := (610950091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184218080533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184218080533 / 100000000000) = 1/(100000000000 / 184218080533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61095009 / 100000000) (610950091 / 1000000000) (Real.log (184218080533 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184218080533 / 100000000000) = -Real.log (100000000000 / 184218080533) := by
    rw [show ((184218080533 / 100000000000) : ℝ) = ((100000000000 / 184218080533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305941017 / 500000000) ≤ -Real.log (20000000000 / 36877968319) ∧
    -Real.log (20000000000 / 36877968319) ≤ (122376407 / 200000000) := by
  have h := checkLog_sound (w := (16877968319 / 56877968319)) (n := 12)
    (lo := (305941017 / 500000000)) (hi := (122376407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36877968319 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36877968319 / 20000000000) = 1/(20000000000 / 36877968319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305941017 / 500000000) (122376407 / 200000000) (Real.log (36877968319 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (36877968319 / 20000000000) = -Real.log (20000000000 / 36877968319) := by
    rw [show ((36877968319 / 20000000000) : ℝ) = ((20000000000 / 36877968319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54535643 / 125000000) ≤ -Real.log (250000000000 / 386737459137) ∧
    -Real.log (250000000000 / 386737459137) ≤ (87257029 / 200000000) := by
  have h := checkLog_sound (w := (136737459137 / 636737459137)) (n := 12)
    (lo := (54535643 / 125000000)) (hi := (87257029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386737459137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386737459137 / 250000000000) = 1/(250000000000 / 386737459137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54535643 / 125000000) (87257029 / 200000000) (Real.log (386737459137 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (386737459137 / 250000000000) = -Real.log (250000000000 / 386737459137) := by
    rw [show ((386737459137 / 250000000000) : ℝ) = ((250000000000 / 386737459137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (218482261 / 500000000) ≤ -Real.log (500000000000 / 774000578397) ∧
    -Real.log (500000000000 / 774000578397) ≤ (436964523 / 1000000000) := by
  have h := checkLog_sound (w := (274000578397 / 1274000578397)) (n := 12)
    (lo := (218482261 / 500000000)) (hi := (436964523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774000578397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774000578397 / 500000000000) = 1/(500000000000 / 774000578397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (218482261 / 500000000) (436964523 / 1000000000) (Real.log (774000578397 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (774000578397 / 500000000000) = -Real.log (500000000000 / 774000578397) := by
    rw [show ((774000578397 / 500000000000) : ℝ) = ((500000000000 / 774000578397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0446
