import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0252
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

theorem reflection_log_1_neg : (121013319 / 500000000) ≤ -Real.log (2560 / 3261) ∧
    -Real.log (2560 / 3261) ≤ (242026639 / 1000000000) := by
  have h := checkLog_sound (w := (701 / 5821)) (n := 12)
    (lo := (121013319 / 500000000)) (hi := (242026639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3261 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3261 / 2560) = 1/(2560 / 3261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121013319 / 500000000) (242026639 / 1000000000) (Real.log (3261 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3261 / 2560) = -Real.log (2560 / 3261) := by
    rw [show ((3261 / 2560) : ℝ) = ((2560 / 3261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (319968549 / 1000000000) ≤ -Real.log (1859 / 2560) ∧
    -Real.log (1859 / 2560) ≤ (6399371 / 20000000) := by
  have h := checkLog_sound (w := (701 / 4419)) (n := 12)
    (lo := (319968549 / 1000000000)) (hi := (6399371 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1859) = 1/(1859 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6399371 / 20000000) (-319968549 / 1000000000) (Real.log (1859 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4831331 / 20000000) ≤ -Real.log (5120 / 6519) ∧
    -Real.log (5120 / 6519) ≤ (241566551 / 1000000000) := by
  have h := checkLog_sound (w := (1399 / 11639)) (n := 12)
    (lo := (4831331 / 20000000)) (hi := (241566551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6519 / 5120) = 1/(5120 / 6519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4831331 / 20000000) (241566551 / 1000000000) (Real.log (6519 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6519 / 5120) = -Real.log (5120 / 6519) := by
    rw [show ((6519 / 5120) : ℝ) = ((5120 / 6519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (319161989 / 1000000000) ≤ -Real.log (3721 / 5120) ∧
    -Real.log (3721 / 5120) ≤ (31916199 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 8841)) (n := 12)
    (lo := (319161989 / 1000000000)) (hi := (31916199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3721) = 1/(3721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-31916199 / 100000000) (-319161989 / 1000000000) (Real.log (3721 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (436741689 / 1000000000) ≤ -Real.log (1280 / 1981) ∧
    -Real.log (1280 / 1981) ≤ (43674169 / 100000000) := by
  have h := checkLog_sound (w := (701 / 3261)) (n := 12)
    (lo := (436741689 / 1000000000)) (hi := (43674169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1280) = 1/(1280 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (436741689 / 1000000000) (43674169 / 100000000) (Real.log (1981 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1981 / 1280) = -Real.log (1280 / 1981) := by
    rw [show ((1981 / 1280) : ℝ) = ((1280 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (396656439 / 500000000) ≤ -Real.log (579 / 1280) ∧
    -Real.log (579 / 1280) ≤ (9916411 / 12500000) := by
  have h := checkLog_sound (w := (61 / 1219)) (n := 12)
    (lo := (50082849 / 500000000)) (hi := (100165699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 579) = 1/(579 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9916411 / 12500000) (-396656439 / 500000000) (Real.log (579 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (435984209 / 1000000000) ≤ -Real.log (2560 / 3959) ∧
    -Real.log (2560 / 3959) ≤ (43598421 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 6519)) (n := 12)
    (lo := (435984209 / 1000000000)) (hi := (43598421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3959 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3959 / 2560) = 1/(2560 / 3959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (435984209 / 1000000000) (43598421 / 100000000) (Real.log (3959 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3959 / 2560) = -Real.log (2560 / 3959) := by
    rw [show ((3959 / 2560) : ℝ) = ((2560 / 3959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158145111 / 200000000) ≤ -Real.log (1161 / 2560) ∧
    -Real.log (1161 / 2560) ≤ (790725557 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 2441)) (n := 12)
    (lo := (780627 / 8000000)) (hi := (12197297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1161) = 1/(1161 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-790725557 / 1000000000) (-158145111 / 200000000) (Real.log (1161 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330702049 / 1000000000) ≤ -Real.log (200000 / 278389) ∧
    -Real.log (200000 / 278389) ≤ (6614041 / 20000000) := by
  have h := checkLog_sound (w := (78389 / 478389)) (n := 12)
    (lo := (330702049 / 1000000000)) (hi := (6614041 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278389 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278389 / 200000) = 1/(200000 / 278389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330702049 / 1000000000) (6614041 / 20000000) (Real.log (278389 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (278389 / 200000) = -Real.log (200000 / 278389) := by
    rw [show ((278389 / 200000) : ℝ) = ((200000 / 278389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24874497 / 50000000) ≤ -Real.log (121611 / 200000) ∧
    -Real.log (121611 / 200000) ≤ (497489941 / 1000000000) := by
  have h := checkLog_sound (w := (78389 / 321611)) (n := 12)
    (lo := (24874497 / 50000000)) (hi := (497489941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 121611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 121611) = 1/(121611 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-497489941 / 1000000000) (-24874497 / 50000000) (Real.log (121611 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (331326161 / 1000000000) ≤ -Real.log (500000 / 696407) ∧
    -Real.log (500000 / 696407) ≤ (165663081 / 500000000) := by
  have h := checkLog_sound (w := (196407 / 1196407)) (n := 12)
    (lo := (331326161 / 1000000000)) (hi := (165663081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696407 / 500000) = 1/(500000 / 696407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (331326161 / 1000000000) (165663081 / 500000000) (Real.log (696407 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (696407 / 500000) = -Real.log (500000 / 696407) := by
    rw [show ((696407 / 500000) : ℝ) = ((500000 / 696407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (498920109 / 1000000000) ≤ -Real.log (303593 / 500000) ∧
    -Real.log (303593 / 500000) ≤ (49892011 / 100000000) := by
  have h := checkLog_sound (w := (196407 / 803593)) (n := 12)
    (lo := (498920109 / 1000000000)) (hi := (49892011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303593) = 1/(303593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49892011 / 100000000) (-498920109 / 1000000000) (Real.log (303593 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (254208791 / 1000000000) ≤ -Real.log (1000000 / 1289441) ∧
    -Real.log (1000000 / 1289441) ≤ (31776099 / 125000000) := by
  have h := checkLog_sound (w := (289441 / 2289441)) (n := 12)
    (lo := (254208791 / 1000000000)) (hi := (31776099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289441 / 1000000) = 1/(1000000 / 1289441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (254208791 / 1000000000) (31776099 / 125000000) (Real.log (1289441 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1289441 / 1000000) = -Real.log (1000000 / 1289441) := by
    rw [show ((1289441 / 1000000) : ℝ) = ((1000000 / 1289441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (170851647 / 500000000) ≤ -Real.log (710559 / 1000000) ∧
    -Real.log (710559 / 1000000) ≤ (68340659 / 200000000) := by
  have h := checkLog_sound (w := (289441 / 1710559)) (n := 12)
    (lo := (170851647 / 500000000)) (hi := (68340659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710559) = 1/(710559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68340659 / 200000000) (-170851647 / 500000000) (Real.log (710559 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (254750739 / 1000000000) ≤ -Real.log (50000 / 64507) ∧
    -Real.log (50000 / 64507) ≤ (12737537 / 50000000) := by
  have h := checkLog_sound (w := (14507 / 114507)) (n := 12)
    (lo := (254750739 / 1000000000)) (hi := (12737537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64507 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64507 / 50000) = 1/(50000 / 64507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (254750739 / 1000000000) (12737537 / 50000000) (Real.log (64507 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (64507 / 50000) = -Real.log (50000 / 64507) := by
    rw [show ((64507 / 50000) : ℝ) = ((50000 / 64507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (342687511 / 1000000000) ≤ -Real.log (35493 / 50000) ∧
    -Real.log (35493 / 50000) ≤ (42835939 / 125000000) := by
  have h := checkLog_sound (w := (14507 / 85493)) (n := 12)
    (lo := (342687511 / 1000000000)) (hi := (42835939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35493) = 1/(35493 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42835939 / 125000000) (-342687511 / 1000000000) (Real.log (35493 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (828191989 / 1000000000) ≤ -Real.log (250000000000 / 572294035901) ∧
    -Real.log (250000000000 / 572294035901) ≤ (828191991 / 1000000000) := by
  have h := checkLog_sound (w := (72294035901 / 1072294035901)) (n := 12)
    (lo := (135044809 / 1000000000)) (hi := (13504481 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572294035901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572294035901 / 500000000000) = 1/(250000000000 / 572294035901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (828191989 / 1000000000) (828191991 / 1000000000) (Real.log (572294035901 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (572294035901 / 250000000000) = -Real.log (250000000000 / 572294035901) := by
    rw [show ((572294035901 / 250000000000) : ℝ) = ((250000000000 / 572294035901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (83024627 / 100000000) ≤ -Real.log (62500000000 / 143367724223) ∧
    -Real.log (62500000000 / 143367724223) ≤ (6486299 / 7812500) := by
  have h := checkLog_sound (w := (18367724223 / 268367724223)) (n := 12)
    (lo := (13709909 / 100000000)) (hi := (137099091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143367724223 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143367724223 / 125000000000) = 1/(62500000000 / 143367724223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (83024627 / 100000000) (6486299 / 7812500) (Real.log (143367724223 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (143367724223 / 62500000000) = -Real.log (62500000000 / 143367724223) := by
    rw [show ((143367724223 / 62500000000) : ℝ) = ((62500000000 / 143367724223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (119182417 / 200000000) ≤ -Real.log (125000000000 / 226835667411) ∧
    -Real.log (125000000000 / 226835667411) ≤ (297956043 / 500000000) := by
  have h := checkLog_sound (w := (101835667411 / 351835667411)) (n := 12)
    (lo := (119182417 / 200000000)) (hi := (297956043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226835667411 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226835667411 / 125000000000) = 1/(125000000000 / 226835667411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (119182417 / 200000000) (297956043 / 500000000) (Real.log (226835667411 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (226835667411 / 125000000000) = -Real.log (125000000000 / 226835667411) := by
    rw [show ((226835667411 / 125000000000) : ℝ) = ((125000000000 / 226835667411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (597438251 / 1000000000) ≤ -Real.log (500000000000 / 908728481673) ∧
    -Real.log (500000000000 / 908728481673) ≤ (149359563 / 250000000) := by
  have h := checkLog_sound (w := (408728481673 / 1408728481673)) (n := 12)
    (lo := (597438251 / 1000000000)) (hi := (149359563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908728481673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908728481673 / 500000000000) = 1/(500000000000 / 908728481673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (597438251 / 1000000000) (149359563 / 250000000) (Real.log (908728481673 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (908728481673 / 500000000000) = -Real.log (500000000000 / 908728481673) := by
    rw [show ((908728481673 / 500000000000) : ℝ) = ((500000000000 / 908728481673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0252
