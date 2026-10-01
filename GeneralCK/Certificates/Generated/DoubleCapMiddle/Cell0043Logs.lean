import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0043
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

theorem reflection_log_1_neg : (3801473 / 10000000) ≤ -Real.log (80 / 117) ∧
    -Real.log (80 / 117) ≤ (380147301 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 197)) (n := 12)
    (lo := (3801473 / 10000000)) (hi := (380147301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 80) = 1/(80 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3801473 / 10000000) (380147301 / 1000000000) (Real.log (117 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (117 / 80) = -Real.log (80 / 117) := by
    rw [show ((117 / 80) : ℝ) = ((80 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (310413259 / 500000000) ≤ -Real.log (43 / 80) ∧
    -Real.log (43 / 80) ≤ (620826519 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 123)) (n := 12)
    (lo := (310413259 / 500000000)) (hi := (620826519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 43) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 43) = 1/(43 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-620826519 / 1000000000) (-310413259 / 500000000) (Real.log (43 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11854553 / 31250000) ≤ -Real.log (2560 / 3741) ∧
    -Real.log (2560 / 3741) ≤ (379345697 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 6301)) (n := 12)
    (lo := (11854553 / 31250000)) (hi := (379345697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 2560) = 1/(2560 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11854553 / 31250000) (379345697 / 1000000000) (Real.log (3741 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3741 / 2560) = -Real.log (2560 / 3741) := by
    rw [show ((3741 / 2560) : ℝ) = ((2560 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (618648659 / 1000000000) ≤ -Real.log (1379 / 2560) ∧
    -Real.log (1379 / 2560) ≤ (30932433 / 50000000) := by
  have h := checkLog_sound (w := (1181 / 3939)) (n := 12)
    (lo := (618648659 / 1000000000)) (hi := (30932433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1379) = 1/(1379 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30932433 / 50000000) (-618648659 / 1000000000) (Real.log (1379 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (654925967 / 1000000000) ≤ -Real.log (40 / 77) ∧
    -Real.log (40 / 77) ≤ (40932873 / 62500000) := by
  have h := checkLog_sound (w := (37 / 117)) (n := 12)
    (lo := (654925967 / 1000000000)) (hi := (40932873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77 / 40) = 1/(40 / 77) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (654925967 / 1000000000) (40932873 / 62500000) (Real.log (77 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (77 / 40) = -Real.log (40 / 77) := by
    rw [show ((77 / 40) : ℝ) = ((40 / 77) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2590267163 / 1000000000) ≤ -Real.log (3 / 40) ∧
    -Real.log (3 / 40) ≤ (2590267167 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5 / 3) = 1/(3 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2590267167 / 1000000000) (-2590267163 / 1000000000) (Real.log (3 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653707693 / 1000000000) ≤ -Real.log (1280 / 2461) ∧
    -Real.log (1280 / 2461) ≤ (326853847 / 500000000) := by
  have h := checkLog_sound (w := (1181 / 3741)) (n := 12)
    (lo := (653707693 / 1000000000)) (hi := (326853847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1280) = 1/(1280 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653707693 / 1000000000) (326853847 / 500000000) (Real.log (2461 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2461 / 1280) = -Real.log (1280 / 2461) := by
    rw [show ((2461 / 1280) : ℝ) = ((1280 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (511899101 / 200000000) ≤ -Real.log (99 / 1280) ∧
    -Real.log (99 / 1280) ≤ (2559495509 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 99) = 1/(99 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2559495509 / 1000000000) (-511899101 / 200000000) (Real.log (99 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (526715311 / 1000000000) ≤ -Real.log (1000000 / 1693361) ∧
    -Real.log (1000000 / 1693361) ≤ (32919707 / 62500000) := by
  have h := checkLog_sound (w := (693361 / 2693361)) (n := 12)
    (lo := (526715311 / 1000000000)) (hi := (32919707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693361 / 1000000) = 1/(1000000 / 1693361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (526715311 / 1000000000) (32919707 / 62500000) (Real.log (1693361 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1693361 / 1000000) = -Real.log (1000000 / 1693361) := by
    rw [show ((1693361 / 1000000) : ℝ) = ((1000000 / 1693361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (591042059 / 500000000) ≤ -Real.log (306639 / 1000000) ∧
    -Real.log (306639 / 1000000) ≤ (29552103 / 25000000) := by
  have h := checkLog_sound (w := (193361 / 806639)) (n := 12)
    (lo := (244468469 / 500000000)) (hi := (488936939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 306639) = 1/(306639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-29552103 / 25000000) (-591042059 / 500000000) (Real.log (306639 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (528019557 / 1000000000) ≤ -Real.log (1000000 / 1695571) ∧
    -Real.log (1000000 / 1695571) ≤ (264009779 / 500000000) := by
  have h := checkLog_sound (w := (695571 / 2695571)) (n := 12)
    (lo := (528019557 / 1000000000)) (hi := (264009779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1695571 / 1000000) = 1/(1000000 / 1695571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (528019557 / 1000000000) (264009779 / 500000000) (Real.log (1695571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1695571 / 1000000) = -Real.log (1000000 / 1695571) := by
    rw [show ((1695571 / 1000000) : ℝ) = ((1000000 / 1695571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1189317387 / 1000000000) ≤ -Real.log (304429 / 1000000) ∧
    -Real.log (304429 / 1000000) ≤ (1189317389 / 1000000000) := by
  have h := checkLog_sound (w := (195571 / 804429)) (n := 12)
    (lo := (496170207 / 1000000000)) (hi := (15505319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 304429) = 1/(304429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1189317389 / 1000000000) (-1189317387 / 1000000000) (Real.log (304429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4474883 / 10000000) ≤ -Real.log (500000 / 782189) ∧
    -Real.log (500000 / 782189) ≤ (447488301 / 1000000000) := by
  have h := checkLog_sound (w := (282189 / 1282189)) (n := 12)
    (lo := (4474883 / 10000000)) (hi := (447488301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782189 / 500000) = 1/(500000 / 782189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4474883 / 10000000) (447488301 / 1000000000) (Real.log (782189 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (782189 / 500000) = -Real.log (500000 / 782189) := by
    rw [show ((782189 / 500000) : ℝ) = ((500000 / 782189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (830980383 / 1000000000) ≤ -Real.log (217811 / 500000) ∧
    -Real.log (217811 / 500000) ≤ (166196077 / 200000000) := by
  have h := checkLog_sound (w := (32189 / 467811)) (n := 12)
    (lo := (137833203 / 1000000000)) (hi := (34458301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217811) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 217811) = 1/(217811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-166196077 / 200000000) (-830980383 / 1000000000) (Real.log (217811 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (448974687 / 1000000000) ≤ -Real.log (200000 / 313341) ∧
    -Real.log (200000 / 313341) ≤ (14030459 / 31250000) := by
  have h := checkLog_sound (w := (113341 / 513341)) (n := 12)
    (lo := (448974687 / 1000000000)) (hi := (14030459 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313341 / 200000) = 1/(200000 / 313341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (448974687 / 1000000000) (14030459 / 31250000) (Real.log (313341 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (313341 / 200000) = -Real.log (200000 / 313341) := by
    rw [show ((313341 / 200000) : ℝ) = ((200000 / 313341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (836336489 / 1000000000) ≤ -Real.log (86659 / 200000) ∧
    -Real.log (86659 / 200000) ≤ (836336491 / 1000000000) := by
  have h := checkLog_sound (w := (13341 / 186659)) (n := 12)
    (lo := (143189309 / 1000000000)) (hi := (14318931 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 86659) = 1/(86659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-836336491 / 1000000000) (-836336489 / 1000000000) (Real.log (86659 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1708799429 / 1000000000) ≤ -Real.log (250000000000 / 1380581889453) ∧
    -Real.log (250000000000 / 1380581889453) ≤ (213599929 / 125000000) := by
  have h := checkLog_sound (w := (380581889453 / 2380581889453)) (n := 12)
    (lo := (322505069 / 1000000000)) (hi := (32250507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1380581889453 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1380581889453 / 1000000000000) = 1/(250000000000 / 1380581889453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1708799429 / 1000000000) (213599929 / 125000000) (Real.log (1380581889453 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1380581889453 / 250000000000) = -Real.log (250000000000 / 1380581889453) := by
    rw [show ((1380581889453 / 250000000000) : ℝ) = ((250000000000 / 1380581889453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (107333559 / 62500000) ≤ -Real.log (15625000000 / 87026192889) ∧
    -Real.log (15625000000 / 87026192889) ≤ (1717336947 / 1000000000) := by
  have h := checkLog_sound (w := (24526192889 / 149526192889)) (n := 12)
    (lo := (41380323 / 125000000)) (hi := (66208517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87026192889 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(87026192889 / 62500000000) = 1/(15625000000 / 87026192889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (107333559 / 62500000) (1717336947 / 1000000000) (Real.log (87026192889 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87026192889 / 15625000000) = -Real.log (15625000000 / 87026192889) := by
    rw [show ((87026192889 / 15625000000) : ℝ) = ((15625000000 / 87026192889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (319617171 / 250000000) ≤ -Real.log (500000000000 / 1795568176079) ∧
    -Real.log (500000000000 / 1795568176079) ≤ (639234343 / 500000000) := by
  have h := checkLog_sound (w := (795568176079 / 2795568176079)) (n := 12)
    (lo := (18291297 / 31250000)) (hi := (117064301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1795568176079 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1795568176079 / 1000000000000) = 1/(500000000000 / 1795568176079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (319617171 / 250000000) (639234343 / 500000000) (Real.log (1795568176079 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1795568176079 / 500000000000) = -Real.log (500000000000 / 1795568176079) := by
    rw [show ((1795568176079 / 500000000000) : ℝ) = ((500000000000 / 1795568176079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (160663897 / 125000000) ≤ -Real.log (100000000000 / 361579293553) ∧
    -Real.log (100000000000 / 361579293553) ≤ (642655589 / 500000000) := by
  have h := checkLog_sound (w := (161579293553 / 561579293553)) (n := 12)
    (lo := (148040999 / 250000000)) (hi := (592163997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361579293553 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361579293553 / 200000000000) = 1/(100000000000 / 361579293553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (160663897 / 125000000) (642655589 / 500000000) (Real.log (361579293553 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (361579293553 / 100000000000) = -Real.log (100000000000 / 361579293553) := by
    rw [show ((361579293553 / 100000000000) : ℝ) = ((100000000000 / 361579293553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0043
