import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0114
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

theorem reflection_log_1_neg : (668370091 / 1000000000) ≤ -Real.log (25600 / 49947) ∧
    -Real.log (25600 / 49947) ≤ (167092523 / 250000000) := by
  have h := checkLog_sound (w := (24347 / 75547)) (n := 12)
    (lo := (668370091 / 1000000000)) (hi := (167092523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49947 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49947 / 25600) = 1/(25600 / 49947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (668370091 / 1000000000) (167092523 / 250000000) (Real.log (49947 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49947 / 25600) = -Real.log (25600 / 49947) := by
    rw [show ((49947 / 25600) : ℝ) = ((25600 / 49947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3017051673 / 1000000000) ≤ -Real.log (1253 / 25600) ∧
    -Real.log (1253 / 25600) ≤ (1508525839 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1253) = 1/(1253 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1508525839 / 500000000) (-3017051673 / 1000000000) (Real.log (1253 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41749351 / 62500000) ≤ -Real.log (3200 / 6241) ∧
    -Real.log (3200 / 6241) ≤ (667989617 / 1000000000) := by
  have h := checkLog_sound (w := (3041 / 9441)) (n := 12)
    (lo := (41749351 / 62500000)) (hi := (667989617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6241 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6241 / 3200) = 1/(3200 / 6241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41749351 / 62500000) (667989617 / 1000000000) (Real.log (6241 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6241 / 3200) = -Real.log (3200 / 6241) := by
    rw [show ((6241 / 3200) : ℝ) = ((3200 / 6241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (750500471 / 250000000) ≤ -Real.log (159 / 3200) ∧
    -Real.log (159 / 3200) ≤ (3002001889 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 159) = 1/(159 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3002001889 / 1000000000) (-750500471 / 250000000) (Real.log (159 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (642963467 / 1000000000) ≤ -Real.log (12800 / 24347) ∧
    -Real.log (12800 / 24347) ≤ (160740867 / 250000000) := by
  have h := checkLog_sound (w := (11547 / 37147)) (n := 12)
    (lo := (642963467 / 1000000000)) (hi := (160740867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24347 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24347 / 12800) = 1/(12800 / 24347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (642963467 / 1000000000) (160740867 / 250000000) (Real.log (24347 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24347 / 12800) = -Real.log (12800 / 24347) := by
    rw [show ((24347 / 12800) : ℝ) = ((12800 / 24347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2323904493 / 1000000000) ≤ -Real.log (1253 / 12800) ∧
    -Real.log (1253 / 12800) ≤ (2323904497 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2853)) (n := 12)
    (lo := (244462953 / 1000000000)) (hi := (122231477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1253) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1253) = 1/(1253 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2323904497 / 1000000000) (-2323904493 / 1000000000) (Real.log (1253 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (642182779 / 1000000000) ≤ -Real.log (1600 / 3041) ∧
    -Real.log (1600 / 3041) ≤ (32109139 / 50000000) := by
  have h := checkLog_sound (w := (1441 / 4641)) (n := 12)
    (lo := (642182779 / 1000000000)) (hi := (32109139 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3041 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3041 / 1600) = 1/(1600 / 3041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (642182779 / 1000000000) (32109139 / 50000000) (Real.log (3041 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3041 / 1600) = -Real.log (1600 / 3041) := by
    rw [show ((3041 / 1600) : ℝ) = ((1600 / 3041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (144303419 / 62500000) ≤ -Real.log (159 / 1600) ∧
    -Real.log (159 / 1600) ≤ (577213677 / 250000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 159) = 1/(159 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-577213677 / 250000000) (-144303419 / 62500000) (Real.log (159 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (672745473 / 1000000000) ≤ -Real.log (100000 / 195961) ∧
    -Real.log (100000 / 195961) ≤ (336372737 / 500000000) := by
  have h := checkLog_sound (w := (95961 / 295961)) (n := 12)
    (lo := (672745473 / 1000000000)) (hi := (336372737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195961 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195961 / 100000) = 1/(100000 / 195961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (672745473 / 1000000000) (336372737 / 500000000) (Real.log (195961 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (195961 / 100000) = -Real.log (100000 / 195961) := by
    rw [show ((195961 / 100000) : ℝ) = ((100000 / 195961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3209173047 / 1000000000) ≤ -Real.log (4039 / 100000) ∧
    -Real.log (4039 / 100000) ≤ (802293263 / 250000000) := by
  have h := checkLog_sound (w := (2211 / 10289)) (n := 12)
    (lo := (436584327 / 1000000000)) (hi := (54573041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4039) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4039) = 1/(4039 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-802293263 / 250000000) (-3209173047 / 1000000000) (Real.log (4039 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336516877 / 500000000) ≤ -Real.log (40000 / 78407) ∧
    -Real.log (40000 / 78407) ≤ (134606751 / 200000000) := by
  have h := checkLog_sound (w := (38407 / 118407)) (n := 12)
    (lo := (336516877 / 500000000)) (hi := (134606751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78407 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78407 / 40000) = 1/(40000 / 78407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336516877 / 500000000) (134606751 / 200000000) (Real.log (78407 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (78407 / 40000) = -Real.log (40000 / 78407) := by
    rw [show ((78407 / 40000) : ℝ) = ((40000 / 78407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (161163021 / 50000000) ≤ -Real.log (1593 / 40000) ∧
    -Real.log (1593 / 40000) ≤ (128930417 / 40000000) := by
  have h := checkLog_sound (w := (907 / 4093)) (n := 12)
    (lo := (4506717 / 10000000)) (hi := (450671701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1593) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1593) = 1/(1593 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-128930417 / 40000000) (-161163021 / 50000000) (Real.log (1593 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (672503559 / 1000000000) ≤ -Real.log (31250 / 61223) ∧
    -Real.log (31250 / 61223) ≤ (16812589 / 25000000) := by
  have h := checkLog_sound (w := (29973 / 92473)) (n := 12)
    (lo := (672503559 / 1000000000)) (hi := (16812589 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61223 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61223 / 31250) = 1/(31250 / 61223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (672503559 / 1000000000) (16812589 / 25000000) (Real.log (61223 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61223 / 31250) = -Real.log (31250 / 61223) := by
    rw [show ((61223 / 31250) : ℝ) = ((31250 / 61223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (799376449 / 250000000) ≤ -Real.log (1277 / 31250) ∧
    -Real.log (1277 / 31250) ≤ (3197505801 / 1000000000) := by
  have h := checkLog_sound (w := (5409 / 25841)) (n := 12)
    (lo := (106229269 / 250000000)) (hi := (424917077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10216) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10216) = 1/(1277 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3197505801 / 1000000000) (-799376449 / 250000000) (Real.log (1277 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134560117 / 200000000) ≤ -Real.log (500000 / 979859) ∧
    -Real.log (500000 / 979859) ≤ (336400293 / 500000000) := by
  have h := checkLog_sound (w := (479859 / 1479859)) (n := 12)
    (lo := (134560117 / 200000000)) (hi := (336400293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979859 / 500000) = 1/(500000 / 979859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134560117 / 200000000) (336400293 / 500000000) (Real.log (979859 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (979859 / 500000) = -Real.log (500000 / 979859) := by
    rw [show ((979859 / 500000) : ℝ) = ((500000 / 979859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3211850557 / 1000000000) ≤ -Real.log (20141 / 500000) ∧
    -Real.log (20141 / 500000) ≤ (1605925281 / 500000000) := by
  have h := checkLog_sound (w := (11109 / 51391)) (n := 12)
    (lo := (439261837 / 1000000000)) (hi := (219630919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20141) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 20141) = 1/(20141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1605925281 / 500000000) (-3211850557 / 1000000000) (Real.log (20141 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (97047963 / 25000000) ≤ -Real.log (125000000000 / 6064650903689) ∧
    -Real.log (125000000000 / 6064650903689) ≤ (1940959263 / 500000000) := by
  have h := checkLog_sound (w := (2064650903689 / 10064650903689)) (n := 12)
    (lo := (20809131 / 50000000)) (hi := (416182621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6064650903689 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6064650903689 / 4000000000000) = 1/(125000000000 / 6064650903689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (97047963 / 25000000) (1940959263 / 500000000) (Real.log (6064650903689 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6064650903689 / 125000000000) = -Real.log (125000000000 / 6064650903689) := by
    rw [show ((6064650903689 / 125000000000) : ℝ) = ((125000000000 / 6064650903689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (155851767 / 40000000) ≤ -Real.log (500000000000 / 24609855618331) ∧
    -Real.log (500000000000 / 24609855618331) ≤ (3896294181 / 1000000000) := by
  have h := checkLog_sound (w := (8609855618331 / 40609855618331)) (n := 12)
    (lo := (17222331 / 40000000)) (hi := (107639569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609855618331 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24609855618331 / 16000000000000) = 1/(500000000000 / 24609855618331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (155851767 / 40000000) (3896294181 / 1000000000) (Real.log (24609855618331 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24609855618331 / 500000000000) = -Real.log (500000000000 / 24609855618331) := by
    rw [show ((24609855618331 / 500000000000) : ℝ) = ((500000000000 / 24609855618331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (967502339 / 250000000) ≤ -Real.log (250000000000 / 11985708692247) ∧
    -Real.log (250000000000 / 11985708692247) ≤ (1935004681 / 500000000) := by
  have h := checkLog_sound (w := (3985708692247 / 19985708692247)) (n := 12)
    (lo := (25267091 / 62500000)) (hi := (404273457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11985708692247 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11985708692247 / 8000000000000) = 1/(250000000000 / 11985708692247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (967502339 / 250000000) (1935004681 / 500000000) (Real.log (11985708692247 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11985708692247 / 250000000000) = -Real.log (250000000000 / 11985708692247) := by
    rw [show ((11985708692247 / 250000000000) : ℝ) = ((250000000000 / 11985708692247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1942325571 / 500000000) ≤ -Real.log (500000000000 / 24324983863761) ∧
    -Real.log (500000000000 / 24324983863761) ≤ (971162787 / 250000000) := by
  have h := checkLog_sound (w := (8324983863761 / 40324983863761)) (n := 12)
    (lo := (209457621 / 500000000)) (hi := (418915243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24324983863761 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24324983863761 / 16000000000000) = 1/(500000000000 / 24324983863761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1942325571 / 500000000) (971162787 / 250000000) (Real.log (24324983863761 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24324983863761 / 500000000000) = -Real.log (500000000000 / 24324983863761) := by
    rw [show ((24324983863761 / 500000000000) : ℝ) = ((500000000000 / 24324983863761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0114
