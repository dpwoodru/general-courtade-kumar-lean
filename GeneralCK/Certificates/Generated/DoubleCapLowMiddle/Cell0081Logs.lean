import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0081
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

theorem reflection_log_1_neg : (675005087 / 1000000000) ≤ -Real.log (51200 / 100559) ∧
    -Real.log (51200 / 100559) ≤ (21093909 / 31250000) := by
  have h := checkLog_sound (w := (49359 / 151759)) (n := 12)
    (lo := (675005087 / 1000000000)) (hi := (21093909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100559 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100559 / 51200) = 1/(51200 / 100559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675005087 / 1000000000) (21093909 / 31250000) (Real.log (100559 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100559 / 51200) = -Real.log (51200 / 100559) := by
    rw [show ((100559 / 51200) : ℝ) = ((51200 / 100559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3325430627 / 1000000000) ≤ -Real.log (1841 / 51200) ∧
    -Real.log (1841 / 51200) ≤ (415678829 / 125000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1841) = 1/(1841 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-415678829 / 125000000) (-3325430627 / 1000000000) (Real.log (1841 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337408063 / 500000000) ≤ -Real.log (2560 / 5027) ∧
    -Real.log (2560 / 5027) ≤ (674816127 / 1000000000) := by
  have h := checkLog_sound (w := (2467 / 7587)) (n := 12)
    (lo := (337408063 / 500000000)) (hi := (674816127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5027 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5027 / 2560) = 1/(2560 / 5027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337408063 / 500000000) (674816127 / 1000000000) (Real.log (5027 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5027 / 2560) = -Real.log (2560 / 5027) := by
    rw [show ((5027 / 2560) : ℝ) = ((2560 / 5027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1657581521 / 500000000) ≤ -Real.log (93 / 2560) ∧
    -Real.log (93 / 2560) ≤ (3315163047 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 93) = 1/(93 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3315163047 / 1000000000) (-1657581521 / 500000000) (Real.log (93 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82065971 / 125000000) ≤ -Real.log (25600 / 49359) ∧
    -Real.log (25600 / 49359) ≤ (656527769 / 1000000000) := by
  have h := checkLog_sound (w := (23759 / 74959)) (n := 12)
    (lo := (82065971 / 125000000)) (hi := (656527769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49359 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49359 / 25600) = 1/(25600 / 49359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82065971 / 125000000) (656527769 / 1000000000) (Real.log (49359 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49359 / 25600) = -Real.log (25600 / 49359) := by
    rw [show ((49359 / 25600) : ℝ) = ((25600 / 49359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2632283447 / 1000000000) ≤ -Real.log (1841 / 25600) ∧
    -Real.log (1841 / 25600) ≤ (2632283451 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1841) = 1/(1841 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2632283451 / 1000000000) (-2632283447 / 1000000000) (Real.log (1841 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4237459 / 6250000) ≤ -Real.log (1000000 / 1969921) ∧
    -Real.log (1000000 / 1969921) ≤ (677993441 / 1000000000) := by
  have h := checkLog_sound (w := (969921 / 2969921)) (n := 12)
    (lo := (4237459 / 6250000)) (hi := (677993441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969921 / 1000000) = 1/(1000000 / 1969921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4237459 / 6250000) (677993441 / 1000000000) (Real.log (1969921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1969921 / 1000000) = -Real.log (1000000 / 1969921) := by
    rw [show ((1969921 / 1000000) : ℝ) = ((1000000 / 1969921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1751964011 / 500000000) ≤ -Real.log (30079 / 1000000) ∧
    -Real.log (30079 / 1000000) ≤ (875982007 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 61329)) (n := 12)
    (lo := (19096061 / 500000000)) (hi := (38192123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30079) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30079) = 1/(30079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-875982007 / 250000000) (-1751964011 / 500000000) (Real.log (30079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339070829 / 500000000) ≤ -Real.log (1000000 / 1970213) ∧
    -Real.log (1000000 / 1970213) ≤ (678141659 / 1000000000) := by
  have h := checkLog_sound (w := (970213 / 2970213)) (n := 12)
    (lo := (339070829 / 500000000)) (hi := (678141659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970213 / 1000000) = 1/(1000000 / 1970213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339070829 / 500000000) (678141659 / 1000000000) (Real.log (1970213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1970213 / 1000000) = -Real.log (1000000 / 1970213) := by
    rw [show ((1970213 / 1000000) : ℝ) = ((1000000 / 1970213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3513683219 / 1000000000) ≤ -Real.log (29787 / 1000000) ∧
    -Real.log (29787 / 1000000) ≤ (140547329 / 40000000) := by
  have h := checkLog_sound (w := (1463 / 61037)) (n := 12)
    (lo := (47947319 / 1000000000)) (hi := (1198683 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29787) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29787) = 1/(29787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140547329 / 40000000) (-3513683219 / 1000000000) (Real.log (29787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338937577 / 500000000) ≤ -Real.log (125000 / 246211) ∧
    -Real.log (125000 / 246211) ≤ (135575031 / 200000000) := by
  have h := checkLog_sound (w := (121211 / 371211)) (n := 12)
    (lo := (338937577 / 500000000)) (hi := (135575031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246211 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246211 / 125000) = 1/(125000 / 246211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338937577 / 500000000) (135575031 / 200000000) (Real.log (246211 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246211 / 125000) = -Real.log (125000 / 246211) := by
    rw [show ((246211 / 125000) : ℝ) = ((125000 / 246211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1748105801 / 500000000) ≤ -Real.log (3789 / 125000) ∧
    -Real.log (3789 / 125000) ≤ (437026451 / 125000000) := by
  have h := checkLog_sound (w := (469 / 30781)) (n := 12)
    (lo := (15237851 / 500000000)) (hi := (30475703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15156) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15156) = 1/(3789 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-437026451 / 125000000) (-1748105801 / 500000000) (Real.log (3789 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84753241 / 125000000) ≤ -Real.log (200000 / 393997) ∧
    -Real.log (200000 / 393997) ≤ (678025929 / 1000000000) := by
  have h := checkLog_sound (w := (193997 / 593997)) (n := 12)
    (lo := (84753241 / 125000000)) (hi := (678025929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393997 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393997 / 200000) = 1/(200000 / 393997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84753241 / 125000000) (678025929 / 1000000000) (Real.log (393997 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393997 / 200000) = -Real.log (200000 / 393997) := by
    rw [show ((393997 / 200000) : ℝ) = ((200000 / 393997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3506058019 / 1000000000) ≤ -Real.log (6003 / 200000) ∧
    -Real.log (6003 / 200000) ≤ (140242321 / 40000000) := by
  have h := checkLog_sound (w := (247 / 12253)) (n := 12)
    (lo := (40322119 / 1000000000)) (hi := (1008053 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 6003) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 6003) = 1/(6003 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-140242321 / 40000000) (-3506058019 / 1000000000) (Real.log (6003 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2090960731 / 500000000) ≤ -Real.log (125000000000 / 8186446524153) ∧
    -Real.log (125000000000 / 8186446524153) ≤ (4181921469 / 1000000000) := by
  have h := checkLog_sound (w := (186446524153 / 16186446524153)) (n := 12)
    (lo := (11519191 / 500000000)) (hi := (23038383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8186446524153 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8186446524153 / 8000000000000) = 1/(125000000000 / 8186446524153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2090960731 / 500000000) (4181921469 / 1000000000) (Real.log (8186446524153 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8186446524153 / 125000000000) = -Real.log (125000000000 / 8186446524153) := by
    rw [show ((8186446524153 / 125000000000) : ℝ) = ((125000000000 / 8186446524153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4191824877 / 1000000000) ≤ -Real.log (125000000000 / 8267923087253) ∧
    -Real.log (125000000000 / 8267923087253) ≤ (1047956221 / 250000000) := by
  have h := checkLog_sound (w := (267923087253 / 16267923087253)) (n := 12)
    (lo := (32941797 / 1000000000)) (hi := (16470899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8267923087253 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8267923087253 / 8000000000000) = 1/(125000000000 / 8267923087253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4191824877 / 1000000000) (1047956221 / 250000000) (Real.log (8267923087253 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8267923087253 / 125000000000) = -Real.log (125000000000 / 8267923087253) := by
    rw [show ((8267923087253 / 125000000000) : ℝ) = ((125000000000 / 8267923087253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1043521689 / 250000000) ≤ -Real.log (62500000000 / 4061279361309) ∧
    -Real.log (62500000000 / 4061279361309) ≤ (4174086763 / 1000000000) := by
  have h := checkLog_sound (w := (61279361309 / 8061279361309)) (n := 12)
    (lo := (3800919 / 250000000)) (hi := (15203677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061279361309 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4061279361309 / 4000000000000) = 1/(62500000000 / 4061279361309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1043521689 / 250000000) (4174086763 / 1000000000) (Real.log (4061279361309 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4061279361309 / 62500000000) = -Real.log (62500000000 / 4061279361309) := by
    rw [show ((4061279361309 / 62500000000) : ℝ) = ((62500000000 / 4061279361309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4184083947 / 1000000000) ≤ -Real.log (125000000000 / 8204168748959) ∧
    -Real.log (125000000000 / 8204168748959) ≤ (2092041977 / 500000000) := by
  have h := checkLog_sound (w := (204168748959 / 16204168748959)) (n := 12)
    (lo := (25200867 / 1000000000)) (hi := (6300217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8204168748959 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8204168748959 / 8000000000000) = 1/(125000000000 / 8204168748959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4184083947 / 1000000000) (2092041977 / 500000000) (Real.log (8204168748959 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8204168748959 / 125000000000) = -Real.log (125000000000 / 8204168748959) := by
    rw [show ((8204168748959 / 125000000000) : ℝ) = ((125000000000 / 8204168748959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0081
