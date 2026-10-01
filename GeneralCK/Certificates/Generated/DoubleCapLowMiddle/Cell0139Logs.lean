import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139
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

theorem reflection_log_1_neg : (658814501 / 1000000000) ≤ -Real.log (400 / 773) ∧
    -Real.log (400 / 773) ≤ (329407251 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1173)) (n := 12)
    (lo := (658814501 / 1000000000)) (hi := (329407251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773 / 400) = 1/(400 / 773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (658814501 / 1000000000) (329407251 / 500000000) (Real.log (773 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (773 / 400) = -Real.log (400 / 773) := by
    rw [show ((773 / 400) : ℝ) = ((400 / 773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2695627679 / 1000000000) ≤ -Real.log (27 / 400) ∧
    -Real.log (27 / 400) ≤ (2695627683 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(50 / 27) = 1/(27 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) (Real.log (27 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164607593 / 250000000) ≤ -Real.log (25600 / 49453) ∧
    -Real.log (25600 / 49453) ≤ (658430373 / 1000000000) := by
  have h := checkLog_sound (w := (23853 / 75053)) (n := 12)
    (lo := (164607593 / 250000000)) (hi := (658430373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49453 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49453 / 25600) = 1/(25600 / 49453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164607593 / 250000000) (658430373 / 1000000000) (Real.log (49453 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49453 / 25600) = -Real.log (25600 / 49453) := by
    rw [show ((49453 / 25600) : ℝ) = ((25600 / 49453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1342346159 / 500000000) ≤ -Real.log (1747 / 25600) ∧
    -Real.log (1747 / 25600) ≤ (1342346161 / 500000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1747) = 1/(1747 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) (Real.log (1747 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (623261053 / 1000000000) ≤ -Real.log (200 / 373) ∧
    -Real.log (200 / 373) ≤ (311630527 / 500000000) := by
  have h := checkLog_sound (w := (173 / 573)) (n := 12)
    (lo := (623261053 / 1000000000)) (hi := (311630527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373 / 200) = 1/(200 / 373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (623261053 / 1000000000) (311630527 / 500000000) (Real.log (373 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (373 / 200) = -Real.log (200 / 373) := by
    rw [show ((373 / 200) : ℝ) = ((200 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2002480499 / 1000000000) ≤ -Real.log (27 / 200) ∧
    -Real.log (27 / 200) ≤ (1001240251 / 500000000) := by
  have h := checkLog_sound (w := (23 / 77)) (n := 12)
    (lo := (616186139 / 1000000000)) (hi := (30809307 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 27) = 1/(27 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) (Real.log (27 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77808103 / 125000000) ≤ -Real.log (12800 / 23853) ∧
    -Real.log (12800 / 23853) ≤ (24898593 / 40000000) := by
  have h := checkLog_sound (w := (11053 / 36653)) (n := 12)
    (lo := (77808103 / 125000000)) (hi := (24898593 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23853 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23853 / 12800) = 1/(12800 / 23853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77808103 / 125000000) (24898593 / 40000000) (Real.log (23853 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23853 / 12800) = -Real.log (12800 / 23853) := by
    rw [show ((23853 / 12800) : ℝ) = ((12800 / 23853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (995772569 / 500000000) ≤ -Real.log (1747 / 12800) ∧
    -Real.log (1747 / 12800) ≤ (1991545141 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1747) = 1/(1747 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) (Real.log (1747 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332833261 / 500000000) ≤ -Real.log (1000000 / 1945787) ∧
    -Real.log (1000000 / 1945787) ≤ (665666523 / 1000000000) := by
  have h := checkLog_sound (w := (945787 / 2945787)) (n := 12)
    (lo := (332833261 / 500000000)) (hi := (665666523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945787 / 1000000) = 1/(1000000 / 1945787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332833261 / 500000000) (665666523 / 1000000000) (Real.log (1945787 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1945787 / 1000000) = -Real.log (1000000 / 1945787) := by
    rw [show ((1945787 / 1000000) : ℝ) = ((1000000 / 1945787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182177159 / 62500000) ≤ -Real.log (54213 / 1000000) ∧
    -Real.log (54213 / 1000000) ≤ (2914834549 / 1000000000) := by
  have h := checkLog_sound (w := (8287 / 116713)) (n := 12)
    (lo := (2222591 / 15625000)) (hi := (5689833 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54213) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54213) = 1/(54213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2914834549 / 1000000000) (-182177159 / 62500000) (Real.log (54213 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (665946061 / 1000000000) ≤ -Real.log (1000000 / 1946331) ∧
    -Real.log (1000000 / 1946331) ≤ (332973031 / 500000000) := by
  have h := checkLog_sound (w := (946331 / 2946331)) (n := 12)
    (lo := (665946061 / 1000000000)) (hi := (332973031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946331 / 1000000) = 1/(1000000 / 1946331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (665946061 / 1000000000) (332973031 / 500000000) (Real.log (1946331 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1946331 / 1000000) = -Real.log (1000000 / 1946331) := by
    rw [show ((1946331 / 1000000) : ℝ) = ((1000000 / 1946331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2924919723 / 1000000000) ≤ -Real.log (53669 / 1000000) ∧
    -Real.log (53669 / 1000000) ≤ (182807483 / 62500000) := by
  have h := checkLog_sound (w := (8831 / 116169)) (n := 12)
    (lo := (152331003 / 1000000000)) (hi := (38082751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53669) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53669) = 1/(53669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182807483 / 62500000) (-2924919723 / 1000000000) (Real.log (53669 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133032857 / 200000000) ≤ -Real.log (100000 / 194481) ∧
    -Real.log (100000 / 194481) ≤ (332582143 / 500000000) := by
  have h := checkLog_sound (w := (94481 / 294481)) (n := 12)
    (lo := (133032857 / 200000000)) (hi := (332582143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194481 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194481 / 100000) = 1/(100000 / 194481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133032857 / 200000000) (332582143 / 500000000) (Real.log (194481 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (194481 / 100000) = -Real.log (100000 / 194481) := by
    rw [show ((194481 / 100000) : ℝ) = ((100000 / 194481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2896973499 / 1000000000) ≤ -Real.log (5519 / 100000) ∧
    -Real.log (5519 / 100000) ≤ (45265211 / 15625000) := by
  have h := checkLog_sound (w := (731 / 11769)) (n := 12)
    (lo := (124384779 / 1000000000)) (hi := (6219239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5519) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5519) = 1/(5519 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45265211 / 15625000) (-2896973499 / 1000000000) (Real.log (5519 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332728151 / 500000000) ≤ -Real.log (500000 / 972689) ∧
    -Real.log (500000 / 972689) ≤ (665456303 / 1000000000) := by
  have h := checkLog_sound (w := (472689 / 1472689)) (n := 12)
    (lo := (332728151 / 500000000)) (hi := (665456303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972689 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972689 / 500000) = 1/(500000 / 972689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332728151 / 500000000) (665456303 / 1000000000) (Real.log (972689 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (972689 / 500000) = -Real.log (500000 / 972689) := by
    rw [show ((972689 / 500000) : ℝ) = ((500000 / 972689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (181707409 / 62500000) ≤ -Real.log (27311 / 500000) ∧
    -Real.log (27311 / 500000) ≤ (2907318549 / 1000000000) := by
  have h := checkLog_sound (w := (3939 / 58561)) (n := 12)
    (lo := (4210307 / 31250000)) (hi := (5389193 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27311) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27311) = 1/(27311 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2907318549 / 1000000000) (-181707409 / 62500000) (Real.log (27311 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1790250533 / 500000000) ≤ -Real.log (62500000000 / 2243220030251) ∧
    -Real.log (62500000000 / 2243220030251) ≤ (223781317 / 62500000) := by
  have h := checkLog_sound (w := (243220030251 / 4243220030251)) (n := 12)
    (lo := (57382583 / 500000000)) (hi := (114765167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243220030251 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2243220030251 / 2000000000000) = 1/(62500000000 / 2243220030251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1790250533 / 500000000) (223781317 / 62500000) (Real.log (2243220030251 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2243220030251 / 62500000000) = -Real.log (62500000000 / 2243220030251) := by
    rw [show ((2243220030251 / 62500000000) : ℝ) = ((62500000000 / 2243220030251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (448858223 / 125000000) ≤ -Real.log (100000000000 / 3626546050793) ∧
    -Real.log (100000000000 / 3626546050793) ≤ (359086579 / 100000000) := by
  have h := checkLog_sound (w := (426546050793 / 6826546050793)) (n := 12)
    (lo := (31282471 / 250000000)) (hi := (25025977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3626546050793 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3626546050793 / 3200000000000) = 1/(100000000000 / 3626546050793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (448858223 / 125000000) (359086579 / 100000000) (Real.log (3626546050793 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3626546050793 / 100000000000) = -Real.log (100000000000 / 3626546050793) := by
    rw [show ((3626546050793 / 100000000000) : ℝ) = ((100000000000 / 3626546050793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (445267223 / 125000000) ≤ -Real.log (500000000000 / 17619224497191) ∧
    -Real.log (500000000000 / 17619224497191) ≤ (356213779 / 100000000) := by
  have h := checkLog_sound (w := (1619224497191 / 33619224497191)) (n := 12)
    (lo := (24100471 / 250000000)) (hi := (19280377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17619224497191 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17619224497191 / 16000000000000) = 1/(500000000000 / 17619224497191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (445267223 / 125000000) (356213779 / 100000000) (Real.log (17619224497191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17619224497191 / 500000000000) = -Real.log (500000000000 / 17619224497191) := by
    rw [show ((17619224497191 / 500000000000) : ℝ) = ((500000000000 / 17619224497191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1786387423 / 500000000) ≤ -Real.log (62500000000 / 2225955201201) ∧
    -Real.log (62500000000 / 2225955201201) ≤ (893193713 / 250000000) := by
  have h := checkLog_sound (w := (225955201201 / 4225955201201)) (n := 12)
    (lo := (53519473 / 500000000)) (hi := (107038947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2225955201201 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2225955201201 / 2000000000000) = 1/(62500000000 / 2225955201201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1786387423 / 500000000) (893193713 / 250000000) (Real.log (2225955201201 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2225955201201 / 62500000000) = -Real.log (62500000000 / 2225955201201) := by
    rw [show ((2225955201201 / 62500000000) : ℝ) = ((62500000000 / 2225955201201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0139
