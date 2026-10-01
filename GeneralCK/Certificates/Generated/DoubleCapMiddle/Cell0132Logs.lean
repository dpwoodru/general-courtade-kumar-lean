import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0132
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

theorem reflection_log_1_neg : (153081297 / 500000000) ≤ -Real.log (2560 / 3477) ∧
    -Real.log (2560 / 3477) ≤ (61232519 / 200000000) := by
  have h := checkLog_sound (w := (917 / 6037)) (n := 12)
    (lo := (153081297 / 500000000)) (hi := (61232519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3477 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3477 / 2560) = 1/(2560 / 3477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153081297 / 500000000) (61232519 / 200000000) (Real.log (3477 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3477 / 2560) = -Real.log (2560 / 3477) := by
    rw [show ((3477 / 2560) : ℝ) = ((2560 / 3477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (443483419 / 1000000000) ≤ -Real.log (1643 / 2560) ∧
    -Real.log (1643 / 2560) ≤ (22174171 / 50000000) := by
  have h := checkLog_sound (w := (917 / 4203)) (n := 12)
    (lo := (443483419 / 1000000000)) (hi := (22174171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1643) = 1/(1643 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22174171 / 50000000) (-443483419 / 1000000000) (Real.log (1643 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (305299409 / 1000000000) ≤ -Real.log (1280 / 1737) ∧
    -Real.log (1280 / 1737) ≤ (30529941 / 100000000) := by
  have h := checkLog_sound (w := (457 / 3017)) (n := 12)
    (lo := (305299409 / 1000000000)) (hi := (30529941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1280) = 1/(1280 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (305299409 / 1000000000) (30529941 / 100000000) (Real.log (1737 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1737 / 1280) = -Real.log (1280 / 1737) := by
    rw [show ((1737 / 1280) : ℝ) = ((1280 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (110414789 / 250000000) ≤ -Real.log (823 / 1280) ∧
    -Real.log (823 / 1280) ≤ (441659157 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 823) = 1/(823 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-441659157 / 1000000000) (-110414789 / 250000000) (Real.log (823 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (108046543 / 200000000) ≤ -Real.log (1280 / 2197) ∧
    -Real.log (1280 / 2197) ≤ (135058179 / 250000000) := by
  have h := checkLog_sound (w := (917 / 3477)) (n := 12)
    (lo := (108046543 / 200000000)) (hi := (135058179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2197 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2197 / 1280) = 1/(1280 / 2197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (108046543 / 200000000) (135058179 / 250000000) (Real.log (2197 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2197 / 1280) = -Real.log (1280 / 2197) := by
    rw [show ((2197 / 1280) : ℝ) = ((1280 / 2197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (630106261 / 500000000) ≤ -Real.log (363 / 1280) ∧
    -Real.log (363 / 1280) ≤ (315053131 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 363) = 1/(363 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-315053131 / 250000000) (-630106261 / 500000000) (Real.log (363 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (538866283 / 1000000000) ≤ -Real.log (640 / 1097) ∧
    -Real.log (640 / 1097) ≤ (134716571 / 250000000) := by
  have h := checkLog_sound (w := (457 / 1737)) (n := 12)
    (lo := (538866283 / 1000000000)) (hi := (134716571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097 / 640) = 1/(640 / 1097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (538866283 / 1000000000) (134716571 / 250000000) (Real.log (1097 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1097 / 640) = -Real.log (640 / 1097) := by
    rw [show ((1097 / 640) : ℝ) = ((640 / 1097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (625991011 / 500000000) ≤ -Real.log (183 / 640) ∧
    -Real.log (183 / 640) ≤ (156497753 / 125000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 183) = 1/(183 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-156497753 / 125000000) (-625991011 / 500000000) (Real.log (183 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (208982331 / 500000000) ≤ -Real.log (1000000 / 1518867) ∧
    -Real.log (1000000 / 1518867) ≤ (417964663 / 1000000000) := by
  have h := checkLog_sound (w := (518867 / 2518867)) (n := 12)
    (lo := (208982331 / 500000000)) (hi := (417964663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1518867 / 1000000) = 1/(1000000 / 1518867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (208982331 / 500000000) (417964663 / 1000000000) (Real.log (1518867 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1518867 / 1000000) = -Real.log (1000000 / 1518867) := by
    rw [show ((1518867 / 1000000) : ℝ) = ((1000000 / 1518867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (731611539 / 1000000000) ≤ -Real.log (481133 / 1000000) ∧
    -Real.log (481133 / 1000000) ≤ (731611541 / 1000000000) := by
  have h := checkLog_sound (w := (18867 / 981133)) (n := 12)
    (lo := (38464359 / 1000000000)) (hi := (961609 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 481133) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 481133) = 1/(481133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-731611541 / 1000000000) (-731611539 / 1000000000) (Real.log (481133 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (419167467 / 1000000000) ≤ -Real.log (200000 / 304139) ∧
    -Real.log (200000 / 304139) ≤ (104791867 / 250000000) := by
  have h := checkLog_sound (w := (104139 / 504139)) (n := 12)
    (lo := (419167467 / 1000000000)) (hi := (104791867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304139 / 200000) = 1/(200000 / 304139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (419167467 / 1000000000) (104791867 / 250000000) (Real.log (304139 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (304139 / 200000) = -Real.log (200000 / 304139) := by
    rw [show ((304139 / 200000) : ℝ) = ((200000 / 304139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36770907 / 50000000) ≤ -Real.log (95861 / 200000) ∧
    -Real.log (95861 / 200000) ≤ (367709071 / 500000000) := by
  have h := checkLog_sound (w := (4139 / 195861)) (n := 12)
    (lo := (528387 / 12500000)) (hi := (42270961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 95861) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 95861) = 1/(95861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367709071 / 500000000) (-36770907 / 50000000) (Real.log (95861 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (66765749 / 200000000) ≤ -Real.log (62500 / 87269) ∧
    -Real.log (62500 / 87269) ≤ (166914373 / 500000000) := by
  have h := checkLog_sound (w := (24769 / 149769)) (n := 12)
    (lo := (66765749 / 200000000)) (hi := (166914373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87269 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87269 / 62500) = 1/(62500 / 87269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (66765749 / 200000000) (166914373 / 500000000) (Real.log (87269 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (87269 / 62500) = -Real.log (62500 / 87269) := by
    rw [show ((87269 / 62500) : ℝ) = ((62500 / 87269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (504684519 / 1000000000) ≤ -Real.log (37731 / 62500) ∧
    -Real.log (37731 / 62500) ≤ (12617113 / 25000000) := by
  have h := checkLog_sound (w := (24769 / 100231)) (n := 12)
    (lo := (504684519 / 1000000000)) (hi := (12617113 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 37731) = 1/(37731 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12617113 / 25000000) (-504684519 / 1000000000) (Real.log (37731 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334987563 / 1000000000) ≤ -Real.log (1000000 / 1397923) ∧
    -Real.log (1000000 / 1397923) ≤ (83746891 / 250000000) := by
  have h := checkLog_sound (w := (397923 / 2397923)) (n := 12)
    (lo := (334987563 / 1000000000)) (hi := (83746891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397923 / 1000000) = 1/(1000000 / 1397923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334987563 / 1000000000) (83746891 / 250000000) (Real.log (1397923 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1397923 / 1000000) = -Real.log (1000000 / 1397923) := by
    rw [show ((1397923 / 1000000) : ℝ) = ((1000000 / 1397923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253684967 / 500000000) ≤ -Real.log (602077 / 1000000) ∧
    -Real.log (602077 / 1000000) ≤ (101473987 / 200000000) := by
  have h := checkLog_sound (w := (397923 / 1602077)) (n := 12)
    (lo := (253684967 / 500000000)) (hi := (101473987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 602077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 602077) = 1/(602077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-101473987 / 200000000) (-253684967 / 500000000) (Real.log (602077 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1149576201 / 1000000000) ≤ -Real.log (125000000000 / 394606844677) ∧
    -Real.log (125000000000 / 394606844677) ≤ (1149576203 / 1000000000) := by
  have h := checkLog_sound (w := (144606844677 / 644606844677)) (n := 12)
    (lo := (456429021 / 1000000000)) (hi := (228214511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394606844677 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(394606844677 / 250000000000) = 1/(125000000000 / 394606844677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1149576201 / 1000000000) (1149576203 / 1000000000) (Real.log (394606844677 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (394606844677 / 125000000000) = -Real.log (125000000000 / 394606844677) := by
    rw [show ((394606844677 / 125000000000) : ℝ) = ((125000000000 / 394606844677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1154585607 / 1000000000) ≤ -Real.log (500000000000 / 1586354200353) ∧
    -Real.log (500000000000 / 1586354200353) ≤ (1154585609 / 1000000000) := by
  have h := checkLog_sound (w := (586354200353 / 2586354200353)) (n := 12)
    (lo := (461438427 / 1000000000)) (hi := (115359607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1586354200353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1586354200353 / 1000000000000) = 1/(500000000000 / 1586354200353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1154585607 / 1000000000) (1154585609 / 1000000000) (Real.log (1586354200353 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1586354200353 / 500000000000) = -Real.log (500000000000 / 1586354200353) := by
    rw [show ((1586354200353 / 500000000000) : ℝ) = ((500000000000 / 1586354200353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (52407079 / 62500000) ≤ -Real.log (125000000000 / 289115713869) ∧
    -Real.log (125000000000 / 289115713869) ≤ (419256633 / 500000000) := by
  have h := checkLog_sound (w := (39115713869 / 539115713869)) (n := 12)
    (lo := (36341521 / 250000000)) (hi := (29073217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289115713869 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(289115713869 / 250000000000) = 1/(125000000000 / 289115713869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (52407079 / 62500000) (419256633 / 500000000) (Real.log (289115713869 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (289115713869 / 125000000000) = -Real.log (125000000000 / 289115713869) := by
    rw [show ((289115713869 / 125000000000) : ℝ) = ((125000000000 / 289115713869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (842357497 / 1000000000) ≤ -Real.log (500000000000 / 1160917125219) ∧
    -Real.log (500000000000 / 1160917125219) ≤ (842357499 / 1000000000) := by
  have h := checkLog_sound (w := (160917125219 / 2160917125219)) (n := 12)
    (lo := (149210317 / 1000000000)) (hi := (74605159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160917125219 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160917125219 / 1000000000000) = 1/(500000000000 / 1160917125219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (842357497 / 1000000000) (842357499 / 1000000000) (Real.log (1160917125219 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1160917125219 / 500000000000) = -Real.log (500000000000 / 1160917125219) := by
    rw [show ((1160917125219 / 500000000000) : ℝ) = ((500000000000 / 1160917125219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0132
