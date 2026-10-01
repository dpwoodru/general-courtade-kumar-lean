import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell200
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

theorem reflection_log_1_neg : (313184189 / 1000000000) ≤ -Real.log (5120 / 7003) ∧
    -Real.log (5120 / 7003) ≤ (31318419 / 100000000) := by
  have h := checkLog_sound (w := (1883 / 12123)) (n := 12)
    (lo := (313184189 / 1000000000)) (hi := (31318419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7003 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7003 / 5120) = 1/(5120 / 7003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (313184189 / 1000000000) (31318419 / 100000000) (Real.log (7003 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7003 / 5120) = -Real.log (5120 / 7003) := by
    rw [show ((7003 / 5120) : ℝ) = ((5120 / 7003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57313433 / 125000000) ≤ -Real.log (3237 / 5120) ∧
    -Real.log (3237 / 5120) ≤ (91701493 / 200000000) := by
  have h := checkLog_sound (w := (1883 / 8357)) (n := 12)
    (lo := (57313433 / 125000000)) (hi := (91701493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3237) = 1/(3237 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91701493 / 200000000) (-57313433 / 125000000) (Real.log (3237 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31275571 / 100000000) ≤ -Real.log (128 / 175) ∧
    -Real.log (128 / 175) ≤ (312755711 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 303)) (n := 12)
    (lo := (31275571 / 100000000)) (hi := (312755711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175 / 128) = 1/(128 / 175) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (31275571 / 100000000) (312755711 / 1000000000) (Real.log (175 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (175 / 128) = -Real.log (128 / 175) := by
    rw [show ((175 / 128) : ℝ) = ((128 / 175) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (457581109 / 1000000000) ≤ -Real.log (81 / 128) ∧
    -Real.log (81 / 128) ≤ (45758111 / 100000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 81) = 1/(81 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45758111 / 100000000) (-457581109 / 1000000000) (Real.log (81 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11602667 / 50000000) ≤ -Real.log (1000000 / 1261187) ∧
    -Real.log (1000000 / 1261187) ≤ (232053341 / 1000000000) := by
  have h := checkLog_sound (w := (261187 / 2261187)) (n := 12)
    (lo := (11602667 / 50000000)) (hi := (232053341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261187 / 1000000) = 1/(1000000 / 1261187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11602667 / 50000000) (232053341 / 1000000000) (Real.log (1261187 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1261187 / 1000000) = -Real.log (1000000 / 1261187) := by
    rw [show ((1261187 / 1000000) : ℝ) = ((1000000 / 1261187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (151355217 / 500000000) ≤ -Real.log (738813 / 1000000) ∧
    -Real.log (738813 / 1000000) ≤ (60542087 / 200000000) := by
  have h := checkLog_sound (w := (261187 / 1738813)) (n := 12)
    (lo := (151355217 / 500000000)) (hi := (60542087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738813) = 1/(738813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60542087 / 200000000) (-151355217 / 500000000) (Real.log (738813 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (232388683 / 1000000000) ≤ -Real.log (100000 / 126161) ∧
    -Real.log (100000 / 126161) ≤ (58097171 / 250000000) := by
  have h := checkLog_sound (w := (26161 / 226161)) (n := 12)
    (lo := (232388683 / 1000000000)) (hi := (58097171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126161 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126161 / 100000) = 1/(100000 / 126161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (232388683 / 1000000000) (58097171 / 250000000) (Real.log (126161 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (126161 / 100000) = -Real.log (100000 / 126161) := by
    rw [show ((126161 / 100000) : ℝ) = ((100000 / 126161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (151641569 / 500000000) ≤ -Real.log (73839 / 100000) ∧
    -Real.log (73839 / 100000) ≤ (303283139 / 1000000000) := by
  have h := checkLog_sound (w := (26161 / 173839)) (n := 12)
    (lo := (151641569 / 500000000)) (hi := (303283139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73839) = 1/(73839 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-303283139 / 1000000000) (-151641569 / 500000000) (Real.log (73839 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (172476587 / 1000000000) ≤ -Real.log (250000 / 297061) ∧
    -Real.log (250000 / 297061) ≤ (43119147 / 250000000) := by
  have h := checkLog_sound (w := (47061 / 547061)) (n := 12)
    (lo := (172476587 / 1000000000)) (hi := (43119147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297061 / 250000) = 1/(250000 / 297061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (172476587 / 1000000000) (43119147 / 250000000) (Real.log (297061 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297061 / 250000) = -Real.log (250000 / 297061) := by
    rw [show ((297061 / 250000) : ℝ) = ((250000 / 297061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52138869 / 250000000) ≤ -Real.log (202939 / 250000) ∧
    -Real.log (202939 / 250000) ≤ (208555477 / 1000000000) := by
  have h := checkLog_sound (w := (47061 / 452939)) (n := 12)
    (lo := (52138869 / 250000000)) (hi := (208555477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202939) = 1/(202939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-208555477 / 1000000000) (-52138869 / 250000000) (Real.log (202939 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (172743331 / 1000000000) ≤ -Real.log (1000000 / 1188561) ∧
    -Real.log (1000000 / 1188561) ≤ (43185833 / 250000000) := by
  have h := checkLog_sound (w := (188561 / 2188561)) (n := 12)
    (lo := (172743331 / 1000000000)) (hi := (43185833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188561 / 1000000) = 1/(1000000 / 1188561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (172743331 / 1000000000) (43185833 / 250000000) (Real.log (1188561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1188561 / 1000000) = -Real.log (1000000 / 1188561) := by
    rw [show ((1188561 / 1000000) : ℝ) = ((1000000 / 1188561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13059129 / 62500000) ≤ -Real.log (811439 / 1000000) ∧
    -Real.log (811439 / 1000000) ≤ (41789213 / 200000000) := by
  have h := checkLog_sound (w := (188561 / 1811439)) (n := 12)
    (lo := (13059129 / 62500000)) (hi := (41789213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811439) = 1/(811439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41789213 / 200000000) (-13059129 / 62500000) (Real.log (811439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (385168409 / 500000000) ≤ -Real.log (25000000000 / 54012345679) ∧
    -Real.log (25000000000 / 54012345679) ≤ (38516841 / 50000000) := by
  have h := checkLog_sound (w := (4012345679 / 104012345679)) (n := 12)
    (lo := (38594819 / 500000000)) (hi := (77189639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54012345679 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(54012345679 / 50000000000) = 1/(25000000000 / 54012345679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (385168409 / 500000000) (38516841 / 50000000) (Real.log (54012345679 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (54012345679 / 25000000000) = -Real.log (25000000000 / 54012345679) := by
    rw [show ((54012345679 / 25000000000) : ℝ) = ((25000000000 / 54012345679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (771691653 / 1000000000) ≤ -Real.log (50000000000 / 108171146123) ∧
    -Real.log (50000000000 / 108171146123) ≤ (154338331 / 200000000) := by
  have h := checkLog_sound (w := (8171146123 / 208171146123)) (n := 12)
    (lo := (78544473 / 1000000000)) (hi := (39272237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108171146123 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(108171146123 / 100000000000) = 1/(50000000000 / 108171146123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (771691653 / 1000000000) (154338331 / 200000000) (Real.log (108171146123 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (108171146123 / 50000000000) = -Real.log (50000000000 / 108171146123) := by
    rw [show ((108171146123 / 50000000000) : ℝ) = ((50000000000 / 108171146123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (21390551 / 40000000) ≤ -Real.log (500000000000 / 853522474563) ∧
    -Real.log (500000000000 / 853522474563) ≤ (2088921 / 3906250) := by
  have h := checkLog_sound (w := (353522474563 / 1353522474563)) (n := 12)
    (lo := (21390551 / 40000000)) (hi := (2088921 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853522474563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853522474563 / 500000000000) = 1/(500000000000 / 853522474563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21390551 / 40000000) (2088921 / 3906250) (Real.log (853522474563 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (853522474563 / 500000000000) = -Real.log (500000000000 / 853522474563) := by
    rw [show ((853522474563 / 500000000000) : ℝ) = ((500000000000 / 853522474563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (535671821 / 1000000000) ≤ -Real.log (500000000000 / 854297864273) ∧
    -Real.log (500000000000 / 854297864273) ≤ (267835911 / 500000000) := by
  have h := checkLog_sound (w := (354297864273 / 1354297864273)) (n := 12)
    (lo := (535671821 / 1000000000)) (hi := (267835911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854297864273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854297864273 / 500000000000) = 1/(500000000000 / 854297864273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (535671821 / 1000000000) (267835911 / 500000000) (Real.log (854297864273 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (854297864273 / 500000000000) = -Real.log (500000000000 / 854297864273) := by
    rw [show ((854297864273 / 500000000000) : ℝ) = ((500000000000 / 854297864273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (381032063 / 1000000000) ≤ -Real.log (250000000000 / 365948634811) ∧
    -Real.log (250000000000 / 365948634811) ≤ (2976813 / 7812500) := by
  have h := checkLog_sound (w := (115948634811 / 615948634811)) (n := 12)
    (lo := (381032063 / 1000000000)) (hi := (2976813 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365948634811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365948634811 / 250000000000) = 1/(250000000000 / 365948634811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (381032063 / 1000000000) (2976813 / 7812500) (Real.log (365948634811 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (365948634811 / 250000000000) = -Real.log (250000000000 / 365948634811) := by
    rw [show ((365948634811 / 250000000000) : ℝ) = ((250000000000 / 365948634811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76337879 / 200000000) ≤ -Real.log (50000000000 / 73237852753) ∧
    -Real.log (50000000000 / 73237852753) ≤ (95422349 / 250000000) := by
  have h := checkLog_sound (w := (23237852753 / 123237852753)) (n := 12)
    (lo := (76337879 / 200000000)) (hi := (95422349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73237852753 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73237852753 / 50000000000) = 1/(50000000000 / 73237852753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76337879 / 200000000) (95422349 / 250000000) (Real.log (73237852753 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (73237852753 / 50000000000) = -Real.log (50000000000 / 73237852753) := by
    rw [show ((73237852753 / 50000000000) : ℝ) = ((50000000000 / 73237852753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9050683 / 250000000) ≤ -Real.log (964444749279 / 1000000000000) ∧
    -Real.log (964444749279 / 1000000000000) ≤ (36202733 / 1000000000) := by
  have h := checkLog_sound (w := (35555250721 / 1964444749279)) (n := 12)
    (lo := (9050683 / 250000000)) (hi := (36202733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964444749279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964444749279) = 1/(964444749279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-36202733 / 1000000000) (-9050683 / 250000000) (Real.log (964444749279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (36078889 / 1000000000) ≤ -Real.log (60285262279 / 62500000000) ∧
    -Real.log (60285262279 / 62500000000) ≤ (3607889 / 100000000) := by
  have h := checkLog_sound (w := (2214737721 / 122785262279)) (n := 12)
    (lo := (36078889 / 1000000000)) (hi := (3607889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60285262279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60285262279) = 1/(60285262279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3607889 / 100000000) (-36078889 / 1000000000) (Real.log (60285262279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell200
