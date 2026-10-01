import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0402
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

theorem reflection_log_1_neg : (199746973 / 1000000000) ≤ -Real.log (1280 / 1563) ∧
    -Real.log (1280 / 1563) ≤ (99873487 / 500000000) := by
  have h := checkLog_sound (w := (283 / 2843)) (n := 12)
    (lo := (199746973 / 1000000000)) (hi := (99873487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563 / 1280) = 1/(1280 / 1563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199746973 / 1000000000) (99873487 / 500000000) (Real.log (1563 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1563 / 1280) = -Real.log (1280 / 1563) := by
    rw [show ((1563 / 1280) : ℝ) = ((1280 / 1563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (124932293 / 500000000) ≤ -Real.log (997 / 1280) ∧
    -Real.log (997 / 1280) ≤ (249864587 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2277)) (n := 12)
    (lo := (124932293 / 500000000)) (hi := (249864587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 997) = 1/(997 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249864587 / 1000000000) (-124932293 / 500000000) (Real.log (997 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199507021 / 1000000000) ≤ -Real.log (10240 / 12501) ∧
    -Real.log (10240 / 12501) ≤ (99753511 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 22741)) (n := 12)
    (lo := (199507021 / 1000000000)) (hi := (99753511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 10240) = 1/(10240 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199507021 / 1000000000) (99753511 / 500000000) (Real.log (12501 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12501 / 10240) = -Real.log (10240 / 12501) := by
    rw [show ((12501 / 10240) : ℝ) = ((10240 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249488529 / 1000000000) ≤ -Real.log (7979 / 10240) ∧
    -Real.log (7979 / 10240) ≤ (24948853 / 100000000) := by
  have h := checkLog_sound (w := (2261 / 18219)) (n := 12)
    (lo := (249488529 / 1000000000)) (hi := (24948853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7979) = 1/(7979 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-24948853 / 100000000) (-249488529 / 1000000000) (Real.log (7979 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183080529 / 500000000) ≤ -Real.log (640 / 923) ∧
    -Real.log (640 / 923) ≤ (366161059 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1563)) (n := 12)
    (lo := (183080529 / 500000000)) (hi := (366161059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923 / 640) = 1/(640 / 923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183080529 / 500000000) (366161059 / 1000000000) (Real.log (923 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (923 / 640) = -Real.log (640 / 923) := by
    rw [show ((923 / 640) : ℝ) = ((640 / 923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (291866197 / 500000000) ≤ -Real.log (357 / 640) ∧
    -Real.log (357 / 640) ≤ (116746479 / 200000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 357) = 1/(357 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-116746479 / 200000000) (-291866197 / 500000000) (Real.log (357 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (365754691 / 1000000000) ≤ -Real.log (5120 / 7381) ∧
    -Real.log (5120 / 7381) ≤ (91438673 / 250000000) := by
  have h := checkLog_sound (w := (2261 / 12501)) (n := 12)
    (lo := (365754691 / 1000000000)) (hi := (91438673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7381 / 5120) = 1/(5120 / 7381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (365754691 / 1000000000) (91438673 / 250000000) (Real.log (7381 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7381 / 5120) = -Real.log (5120 / 7381) := by
    rw [show ((7381 / 5120) : ℝ) = ((5120 / 7381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23307301 / 40000000) ≤ -Real.log (2859 / 5120) ∧
    -Real.log (2859 / 5120) ≤ (291341263 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 7979)) (n := 12)
    (lo := (23307301 / 40000000)) (hi := (291341263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2859) = 1/(2859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-291341263 / 500000000) (-23307301 / 40000000) (Real.log (2859 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (273856437 / 1000000000) ≤ -Real.log (500000 / 657513) ∧
    -Real.log (500000 / 657513) ≤ (136928219 / 500000000) := by
  have h := checkLog_sound (w := (157513 / 1157513)) (n := 12)
    (lo := (273856437 / 1000000000)) (hi := (136928219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657513 / 500000) = 1/(500000 / 657513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (273856437 / 1000000000) (136928219 / 500000000) (Real.log (657513 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657513 / 500000) = -Real.log (500000 / 657513) := by
    rw [show ((657513 / 500000) : ℝ) = ((500000 / 657513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (378374397 / 1000000000) ≤ -Real.log (342487 / 500000) ∧
    -Real.log (342487 / 500000) ≤ (189187199 / 500000000) := by
  have h := checkLog_sound (w := (157513 / 842487)) (n := 12)
    (lo := (378374397 / 1000000000)) (hi := (189187199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342487) = 1/(342487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-189187199 / 500000000) (-378374397 / 1000000000) (Real.log (342487 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68545273 / 250000000) ≤ -Real.log (1000000 / 1315453) ∧
    -Real.log (1000000 / 1315453) ≤ (274181093 / 1000000000) := by
  have h := checkLog_sound (w := (315453 / 2315453)) (n := 12)
    (lo := (68545273 / 250000000)) (hi := (274181093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315453 / 1000000) = 1/(1000000 / 1315453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68545273 / 250000000) (274181093 / 1000000000) (Real.log (1315453 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315453 / 1000000) = -Real.log (1000000 / 1315453) := by
    rw [show ((1315453 / 1000000) : ℝ) = ((1000000 / 1315453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (378997973 / 1000000000) ≤ -Real.log (684547 / 1000000) ∧
    -Real.log (684547 / 1000000) ≤ (189498987 / 500000000) := by
  have h := checkLog_sound (w := (315453 / 1684547)) (n := 12)
    (lo := (378997973 / 1000000000)) (hi := (189498987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684547) = 1/(684547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189498987 / 500000000) (-378997973 / 1000000000) (Real.log (684547 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (206240699 / 1000000000) ≤ -Real.log (1000000 / 1229049) ∧
    -Real.log (1000000 / 1229049) ≤ (2062407 / 10000000) := by
  have h := checkLog_sound (w := (229049 / 2229049)) (n := 12)
    (lo := (206240699 / 1000000000)) (hi := (2062407 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229049 / 1000000) = 1/(1000000 / 1229049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (206240699 / 1000000000) (2062407 / 10000000) (Real.log (1229049 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1229049 / 1000000) = -Real.log (1000000 / 1229049) := by
    rw [show ((1229049 / 1000000) : ℝ) = ((1000000 / 1229049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (260130461 / 1000000000) ≤ -Real.log (770951 / 1000000) ∧
    -Real.log (770951 / 1000000) ≤ (130065231 / 500000000) := by
  have h := checkLog_sound (w := (229049 / 1770951)) (n := 12)
    (lo := (260130461 / 1000000000)) (hi := (130065231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770951) = 1/(770951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-130065231 / 500000000) (-260130461 / 1000000000) (Real.log (770951 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206507537 / 1000000000) ≤ -Real.log (1000000 / 1229377) ∧
    -Real.log (1000000 / 1229377) ≤ (103253769 / 500000000) := by
  have h := checkLog_sound (w := (229377 / 2229377)) (n := 12)
    (lo := (206507537 / 1000000000)) (hi := (103253769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229377 / 1000000) = 1/(1000000 / 1229377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206507537 / 1000000000) (103253769 / 500000000) (Real.log (1229377 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1229377 / 1000000) = -Real.log (1000000 / 1229377) := by
    rw [show ((1229377 / 1000000) : ℝ) = ((1000000 / 1229377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (65139 / 250000) ≤ -Real.log (770623 / 1000000) ∧
    -Real.log (770623 / 1000000) ≤ (260556001 / 1000000000) := by
  have h := checkLog_sound (w := (229377 / 1770623)) (n := 12)
    (lo := (65139 / 250000)) (hi := (260556001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770623) = 1/(770623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260556001 / 1000000000) (-65139 / 250000) (Real.log (770623 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (326115417 / 500000000) ≤ -Real.log (500000000000 / 959909427219) ∧
    -Real.log (500000000000 / 959909427219) ≤ (130446167 / 200000000) := by
  have h := checkLog_sound (w := (459909427219 / 1459909427219)) (n := 12)
    (lo := (326115417 / 500000000)) (hi := (130446167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959909427219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959909427219 / 500000000000) = 1/(500000000000 / 959909427219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (326115417 / 500000000) (130446167 / 200000000) (Real.log (959909427219 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (959909427219 / 500000000000) = -Real.log (500000000000 / 959909427219) := by
    rw [show ((959909427219 / 500000000000) : ℝ) = ((500000000000 / 959909427219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (326589533 / 500000000) ≤ -Real.log (250000000000 / 480410037587) ∧
    -Real.log (250000000000 / 480410037587) ≤ (653179067 / 1000000000) := by
  have h := checkLog_sound (w := (230410037587 / 730410037587)) (n := 12)
    (lo := (326589533 / 500000000)) (hi := (653179067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((480410037587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(480410037587 / 250000000000) = 1/(250000000000 / 480410037587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (326589533 / 500000000) (653179067 / 1000000000) (Real.log (480410037587 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (480410037587 / 250000000000) = -Real.log (250000000000 / 480410037587) := by
    rw [show ((480410037587 / 250000000000) : ℝ) = ((250000000000 / 480410037587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11659279 / 25000000) ≤ -Real.log (250000000000 / 398549648421) ∧
    -Real.log (250000000000 / 398549648421) ≤ (466371161 / 1000000000) := by
  have h := checkLog_sound (w := (148549648421 / 648549648421)) (n := 12)
    (lo := (11659279 / 25000000)) (hi := (466371161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398549648421 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398549648421 / 250000000000) = 1/(250000000000 / 398549648421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (11659279 / 25000000) (466371161 / 1000000000) (Real.log (398549648421 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (398549648421 / 250000000000) = -Real.log (250000000000 / 398549648421) := by
    rw [show ((398549648421 / 250000000000) : ℝ) = ((250000000000 / 398549648421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (467063537 / 1000000000) ≤ -Real.log (250000000000 / 398825690383) ∧
    -Real.log (250000000000 / 398825690383) ≤ (233531769 / 500000000) := by
  have h := checkLog_sound (w := (148825690383 / 648825690383)) (n := 12)
    (lo := (467063537 / 1000000000)) (hi := (233531769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398825690383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398825690383 / 250000000000) = 1/(250000000000 / 398825690383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (467063537 / 1000000000) (233531769 / 500000000) (Real.log (398825690383 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (398825690383 / 250000000000) = -Real.log (250000000000 / 398825690383) := by
    rw [show ((398825690383 / 250000000000) : ℝ) = ((250000000000 / 398825690383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0402
