import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138
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

theorem reflection_log_1_neg : (659198483 / 1000000000) ≤ -Real.log (25600 / 49491) ∧
    -Real.log (25600 / 49491) ≤ (164799621 / 250000000) := by
  have h := checkLog_sound (w := (23891 / 75091)) (n := 12)
    (lo := (659198483 / 1000000000)) (hi := (164799621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49491 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49491 / 25600) = 1/(25600 / 49491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (659198483 / 1000000000) (164799621 / 250000000) (Real.log (49491 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49491 / 25600) = -Real.log (25600 / 49491) := by
    rw [show ((49491 / 25600) : ℝ) = ((25600 / 49491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (541336789 / 200000000) ≤ -Real.log (1709 / 25600) ∧
    -Real.log (1709 / 25600) ≤ (2706683949 / 1000000000) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1709) = 1/(1709 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2706683949 / 1000000000) (-541336789 / 200000000) (Real.log (1709 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (658814501 / 1000000000) ≤ -Real.log (400 / 773) ∧
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


theorem reflection_log_3 : Bounds (658814501 / 1000000000) (329407251 / 500000000) (Real.log (773 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (773 / 400) = -Real.log (400 / 773) := by
    rw [show ((773 / 400) : ℝ) = ((400 / 773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2695627679 / 1000000000) ≤ -Real.log (27 / 400) ∧
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


theorem reflection_log_4 : Bounds (-2695627683 / 1000000000) (-2695627679 / 1000000000) (Real.log (27 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78007081 / 125000000) ≤ -Real.log (12800 / 23891) ∧
    -Real.log (12800 / 23891) ≤ (624056649 / 1000000000) := by
  have h := checkLog_sound (w := (11091 / 36691)) (n := 12)
    (lo := (78007081 / 125000000)) (hi := (624056649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23891 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23891 / 12800) = 1/(12800 / 23891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (78007081 / 125000000) (624056649 / 1000000000) (Real.log (23891 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23891 / 12800) = -Real.log (12800 / 23891) := by
    rw [show ((23891 / 12800) : ℝ) = ((12800 / 23891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (402707353 / 200000000) ≤ -Real.log (1709 / 12800) ∧
    -Real.log (1709 / 12800) ≤ (3932689 / 1953125) := by
  have h := checkLog_sound (w := (1491 / 4909)) (n := 12)
    (lo := (125448481 / 200000000)) (hi := (313621203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1709) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1709) = 1/(1709 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3932689 / 1953125) (-402707353 / 200000000) (Real.log (1709 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (623261053 / 1000000000) ≤ -Real.log (200 / 373) ∧
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


theorem reflection_log_7 : Bounds (623261053 / 1000000000) (311630527 / 500000000) (Real.log (373 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (373 / 200) = -Real.log (200 / 373) := by
    rw [show ((373 / 200) : ℝ) = ((200 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2002480499 / 1000000000) ≤ -Real.log (27 / 200) ∧
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


theorem reflection_log_8 : Bounds (-1001240251 / 500000000) (-2002480499 / 1000000000) (Real.log (27 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166486387 / 250000000) ≤ -Real.log (100000 / 194633) ∧
    -Real.log (100000 / 194633) ≤ (665945549 / 1000000000) := by
  have h := checkLog_sound (w := (94633 / 294633)) (n := 12)
    (lo := (166486387 / 250000000)) (hi := (665945549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194633 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194633 / 100000) = 1/(100000 / 194633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166486387 / 250000000) (665945549 / 1000000000) (Real.log (194633 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (194633 / 100000) = -Real.log (100000 / 194633) := by
    rw [show ((194633 / 100000) : ℝ) = ((100000 / 194633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (292490109 / 100000000) ≤ -Real.log (5367 / 100000) ∧
    -Real.log (5367 / 100000) ≤ (584980219 / 200000000) := by
  have h := checkLog_sound (w := (883 / 11617)) (n := 12)
    (lo := (15231237 / 100000000)) (hi := (152312371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5367) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 5367) = 1/(5367 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-584980219 / 200000000) (-292490109 / 100000000) (Real.log (5367 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (666225009 / 1000000000) ≤ -Real.log (500000 / 973437) ∧
    -Real.log (500000 / 973437) ≤ (66622501 / 100000000) := by
  have h := checkLog_sound (w := (473437 / 1473437)) (n := 12)
    (lo := (666225009 / 1000000000)) (hi := (66622501 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973437 / 500000) = 1/(500000 / 973437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (666225009 / 1000000000) (66622501 / 100000000) (Real.log (973437 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (973437 / 500000) = -Real.log (500000 / 973437) := by
    rw [show ((973437 / 500000) : ℝ) = ((500000 / 973437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1467544413 / 500000000) ≤ -Real.log (26563 / 500000) ∧
    -Real.log (26563 / 500000) ≤ (2935088831 / 1000000000) := by
  have h := checkLog_sound (w := (4687 / 57813)) (n := 12)
    (lo := (81250053 / 500000000)) (hi := (162500107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26563) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26563) = 1/(26563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2935088831 / 1000000000) (-1467544413 / 500000000) (Real.log (26563 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166363947 / 250000000) ≤ -Real.log (1000000 / 1945377) ∧
    -Real.log (1000000 / 1945377) ≤ (665455789 / 1000000000) := by
  have h := checkLog_sound (w := (945377 / 2945377)) (n := 12)
    (lo := (166363947 / 250000000)) (hi := (665455789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945377 / 1000000) = 1/(1000000 / 1945377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166363947 / 250000000) (665455789 / 1000000000) (Real.log (1945377 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1945377 / 1000000) = -Real.log (1000000 / 1945377) := by
    rw [show ((1945377 / 1000000) : ℝ) = ((1000000 / 1945377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2907300237 / 1000000000) ≤ -Real.log (54623 / 1000000) ∧
    -Real.log (54623 / 1000000) ≤ (1453650121 / 500000000) := by
  have h := checkLog_sound (w := (7877 / 117123)) (n := 12)
    (lo := (134711517 / 1000000000)) (hi := (67355759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54623) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54623) = 1/(54623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1453650121 / 500000000) (-2907300237 / 1000000000) (Real.log (54623 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16643693 / 25000000) ≤ -Real.log (200000 / 389189) ∧
    -Real.log (200000 / 389189) ≤ (665747721 / 1000000000) := by
  have h := checkLog_sound (w := (189189 / 589189)) (n := 12)
    (lo := (16643693 / 25000000)) (hi := (665747721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389189 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389189 / 200000) = 1/(200000 / 389189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16643693 / 25000000) (665747721 / 1000000000) (Real.log (389189 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (389189 / 200000) = -Real.log (200000 / 389189) := by
    rw [show ((389189 / 200000) : ℝ) = ((200000 / 389189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2917753229 / 1000000000) ≤ -Real.log (10811 / 200000) ∧
    -Real.log (10811 / 200000) ≤ (1458876617 / 500000000) := by
  have h := checkLog_sound (w := (1689 / 23311)) (n := 12)
    (lo := (145164509 / 1000000000)) (hi := (14516451 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10811) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 10811) = 1/(10811 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1458876617 / 500000000) (-2917753229 / 1000000000) (Real.log (10811 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1795423319 / 500000000) ≤ -Real.log (125000000000 / 4533095770449) ∧
    -Real.log (125000000000 / 4533095770449) ≤ (897711661 / 250000000) := by
  have h := checkLog_sound (w := (533095770449 / 8533095770449)) (n := 12)
    (lo := (62555369 / 500000000)) (hi := (125110739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4533095770449 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4533095770449 / 4000000000000) = 1/(125000000000 / 4533095770449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1795423319 / 500000000) (897711661 / 250000000) (Real.log (4533095770449 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4533095770449 / 125000000000) = -Real.log (125000000000 / 4533095770449) := by
    rw [show ((4533095770449 / 125000000000) : ℝ) = ((125000000000 / 4533095770449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1800656917 / 500000000) ≤ -Real.log (20000000000 / 732927003727) ∧
    -Real.log (20000000000 / 732927003727) ≤ (45016423 / 12500000) := by
  have h := checkLog_sound (w := (92927003727 / 1372927003727)) (n := 12)
    (lo := (67788967 / 500000000)) (hi := (27115587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732927003727 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(732927003727 / 640000000000) = 1/(20000000000 / 732927003727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1800656917 / 500000000) (45016423 / 12500000) (Real.log (732927003727 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (732927003727 / 20000000000) = -Real.log (20000000000 / 732927003727) := by
    rw [show ((732927003727 / 20000000000) : ℝ) = ((20000000000 / 732927003727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (142910241 / 40000000) ≤ -Real.log (250000000000 / 8903653223001) ∧
    -Real.log (250000000000 / 8903653223001) ≤ (3572756031 / 1000000000) := by
  have h := checkLog_sound (w := (903653223001 / 16903653223001)) (n := 12)
    (lo := (856161 / 8000000)) (hi := (53510063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8903653223001 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8903653223001 / 8000000000000) = 1/(250000000000 / 8903653223001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (142910241 / 40000000) (3572756031 / 1000000000) (Real.log (8903653223001 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8903653223001 / 250000000000) = -Real.log (250000000000 / 8903653223001) := by
    rw [show ((8903653223001 / 250000000000) : ℝ) = ((250000000000 / 8903653223001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3583500949 / 1000000000) ≤ -Real.log (250000000000 / 8999838127833) ∧
    -Real.log (250000000000 / 8999838127833) ≤ (716700191 / 200000000) := by
  have h := checkLog_sound (w := (999838127833 / 16999838127833)) (n := 12)
    (lo := (117765049 / 1000000000)) (hi := (2355301 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8999838127833 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8999838127833 / 8000000000000) = 1/(250000000000 / 8999838127833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3583500949 / 1000000000) (716700191 / 200000000) (Real.log (8999838127833 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8999838127833 / 250000000000) = -Real.log (250000000000 / 8999838127833) := by
    rw [show ((8999838127833 / 250000000000) : ℝ) = ((250000000000 / 8999838127833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0138
