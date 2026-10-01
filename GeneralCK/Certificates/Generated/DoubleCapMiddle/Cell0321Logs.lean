import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0321
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

theorem reflection_log_1_neg : (21899433 / 100000000) ≤ -Real.log (10240 / 12747) ∧
    -Real.log (10240 / 12747) ≤ (218994331 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 22987)) (n := 12)
    (lo := (21899433 / 100000000)) (hi := (218994331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12747 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12747 / 10240) = 1/(10240 / 12747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21899433 / 100000000) (218994331 / 1000000000) (Real.log (12747 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12747 / 10240) = -Real.log (10240 / 12747) := by
    rw [show ((12747 / 10240) : ℝ) = ((10240 / 12747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280804733 / 1000000000) ≤ -Real.log (7733 / 10240) ∧
    -Real.log (7733 / 10240) ≤ (140402367 / 500000000) := by
  have h := checkLog_sound (w := (2507 / 17973)) (n := 12)
    (lo := (280804733 / 1000000000)) (hi := (140402367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7733) = 1/(7733 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140402367 / 500000000) (-280804733 / 1000000000) (Real.log (7733 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27344869 / 125000000) ≤ -Real.log (1280 / 1593) ∧
    -Real.log (1280 / 1593) ≤ (218758953 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 2873)) (n := 12)
    (lo := (27344869 / 125000000)) (hi := (218758953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1280) = 1/(1280 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27344869 / 125000000) (218758953 / 1000000000) (Real.log (1593 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1593 / 1280) = -Real.log (1280 / 1593) := by
    rw [show ((1593 / 1280) : ℝ) = ((1280 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280416861 / 1000000000) ≤ -Real.log (967 / 1280) ∧
    -Real.log (967 / 1280) ≤ (140208431 / 500000000) := by
  have h := checkLog_sound (w := (313 / 2247)) (n := 12)
    (lo := (280416861 / 1000000000)) (hi := (140208431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 967) = 1/(967 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140208431 / 500000000) (-280416861 / 1000000000) (Real.log (967 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24908759 / 62500000) ≤ -Real.log (5120 / 7627) ∧
    -Real.log (5120 / 7627) ≤ (79708029 / 200000000) := by
  have h := checkLog_sound (w := (2507 / 12747)) (n := 12)
    (lo := (24908759 / 62500000)) (hi := (79708029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7627 / 5120) = 1/(5120 / 7627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24908759 / 62500000) (79708029 / 200000000) (Real.log (7627 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7627 / 5120) = -Real.log (5120 / 7627) := by
    rw [show ((7627 / 5120) : ℝ) = ((5120 / 7627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (168163863 / 250000000) ≤ -Real.log (2613 / 5120) ∧
    -Real.log (2613 / 5120) ≤ (672655453 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 7733)) (n := 12)
    (lo := (168163863 / 250000000)) (hi := (672655453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2613) = 1/(2613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-672655453 / 1000000000) (-168163863 / 250000000) (Real.log (2613 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (398146727 / 1000000000) ≤ -Real.log (640 / 953) ∧
    -Real.log (640 / 953) ≤ (49768341 / 125000000) := by
  have h := checkLog_sound (w := (313 / 1593)) (n := 12)
    (lo := (398146727 / 1000000000)) (hi := (49768341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953 / 640) = 1/(640 / 953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (398146727 / 1000000000) (49768341 / 125000000) (Real.log (953 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (953 / 640) = -Real.log (640 / 953) := by
    rw [show ((953 / 640) : ℝ) = ((640 / 953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (134301601 / 200000000) ≤ -Real.log (327 / 640) ∧
    -Real.log (327 / 640) ≤ (335754003 / 500000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 327) = 1/(327 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-335754003 / 500000000) (-134301601 / 200000000) (Real.log (327 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (299851967 / 1000000000) ≤ -Real.log (1000000 / 1349659) ∧
    -Real.log (1000000 / 1349659) ≤ (4685187 / 15625000) := by
  have h := checkLog_sound (w := (349659 / 2349659)) (n := 12)
    (lo := (299851967 / 1000000000)) (hi := (4685187 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349659 / 1000000) = 1/(1000000 / 1349659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (299851967 / 1000000000) (4685187 / 15625000) (Real.log (1349659 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1349659 / 1000000) = -Real.log (1000000 / 1349659) := by
    rw [show ((1349659 / 1000000) : ℝ) = ((1000000 / 1349659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (215129219 / 500000000) ≤ -Real.log (650341 / 1000000) ∧
    -Real.log (650341 / 1000000) ≤ (430258439 / 1000000000) := by
  have h := checkLog_sound (w := (349659 / 1650341)) (n := 12)
    (lo := (215129219 / 500000000)) (hi := (430258439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 650341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 650341) = 1/(650341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-430258439 / 1000000000) (-215129219 / 500000000) (Real.log (650341 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75042629 / 250000000) ≤ -Real.log (1000000 / 1350089) ∧
    -Real.log (1000000 / 1350089) ≤ (300170517 / 1000000000) := by
  have h := checkLog_sound (w := (350089 / 2350089)) (n := 12)
    (lo := (75042629 / 250000000)) (hi := (300170517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350089 / 1000000) = 1/(1000000 / 1350089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75042629 / 250000000) (300170517 / 1000000000) (Real.log (1350089 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1350089 / 1000000) = -Real.log (1000000 / 1350089) := by
    rw [show ((1350089 / 1000000) : ℝ) = ((1000000 / 1350089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53864981 / 125000000) ≤ -Real.log (649911 / 1000000) ∧
    -Real.log (649911 / 1000000) ≤ (430919849 / 1000000000) := by
  have h := checkLog_sound (w := (350089 / 1649911)) (n := 12)
    (lo := (53864981 / 125000000)) (hi := (430919849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649911) = 1/(649911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-430919849 / 1000000000) (-53864981 / 125000000) (Real.log (649911 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45570967 / 200000000) ≤ -Real.log (1000000 / 1255903) ∧
    -Real.log (1000000 / 1255903) ≤ (56963709 / 250000000) := by
  have h := checkLog_sound (w := (255903 / 2255903)) (n := 12)
    (lo := (45570967 / 200000000)) (hi := (56963709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255903 / 1000000) = 1/(1000000 / 1255903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45570967 / 200000000) (56963709 / 250000000) (Real.log (1255903 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255903 / 1000000) = -Real.log (1000000 / 1255903) := by
    rw [show ((1255903 / 1000000) : ℝ) = ((1000000 / 1255903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (73895969 / 250000000) ≤ -Real.log (744097 / 1000000) ∧
    -Real.log (744097 / 1000000) ≤ (295583877 / 1000000000) := by
  have h := checkLog_sound (w := (255903 / 1744097)) (n := 12)
    (lo := (73895969 / 250000000)) (hi := (295583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744097) = 1/(744097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-295583877 / 1000000000) (-73895969 / 250000000) (Real.log (744097 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (57030783 / 250000000) ≤ -Real.log (12500 / 15703) ∧
    -Real.log (12500 / 15703) ≤ (228123133 / 1000000000) := by
  have h := checkLog_sound (w := (3203 / 28203)) (n := 12)
    (lo := (57030783 / 250000000)) (hi := (228123133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15703 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15703 / 12500) = 1/(12500 / 15703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (57030783 / 250000000) (228123133 / 1000000000) (Real.log (15703 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15703 / 12500) = -Real.log (12500 / 15703) := by
    rw [show ((15703 / 12500) : ℝ) = ((12500 / 15703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (74009219 / 250000000) ≤ -Real.log (9297 / 12500) ∧
    -Real.log (9297 / 12500) ≤ (296036877 / 1000000000) := by
  have h := checkLog_sound (w := (3203 / 21797)) (n := 12)
    (lo := (74009219 / 250000000)) (hi := (296036877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9297) = 1/(9297 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-296036877 / 1000000000) (-74009219 / 250000000) (Real.log (9297 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (146022081 / 200000000) ≤ -Real.log (100000000000 / 207530972213) ∧
    -Real.log (100000000000 / 207530972213) ≤ (730110407 / 1000000000) := by
  have h := checkLog_sound (w := (7530972213 / 407530972213)) (n := 12)
    (lo := (1478529 / 40000000)) (hi := (18481613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207530972213 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207530972213 / 200000000000) = 1/(100000000000 / 207530972213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (146022081 / 200000000) (730110407 / 1000000000) (Real.log (207530972213 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (207530972213 / 100000000000) = -Real.log (100000000000 / 207530972213) := by
    rw [show ((207530972213 / 100000000000) : ℝ) = ((100000000000 / 207530972213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182772591 / 250000000) ≤ -Real.log (500000000000 / 1038672218197) ∧
    -Real.log (500000000000 / 1038672218197) ≤ (365545183 / 500000000) := by
  have h := checkLog_sound (w := (38672218197 / 2038672218197)) (n := 12)
    (lo := (2371449 / 62500000)) (hi := (7588637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038672218197 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038672218197 / 1000000000000) = 1/(500000000000 / 1038672218197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182772591 / 250000000) (365545183 / 500000000) (Real.log (1038672218197 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1038672218197 / 500000000000) = -Real.log (500000000000 / 1038672218197) := by
    rw [show ((1038672218197 / 500000000000) : ℝ) = ((500000000000 / 1038672218197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (65429839 / 125000000) ≤ -Real.log (500000000000 / 843910807327) ∧
    -Real.log (500000000000 / 843910807327) ≤ (523438713 / 1000000000) := by
  have h := checkLog_sound (w := (343910807327 / 1343910807327)) (n := 12)
    (lo := (65429839 / 125000000)) (hi := (523438713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843910807327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843910807327 / 500000000000) = 1/(500000000000 / 843910807327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (65429839 / 125000000) (523438713 / 1000000000) (Real.log (843910807327 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (843910807327 / 500000000000) = -Real.log (500000000000 / 843910807327) := by
    rw [show ((843910807327 / 500000000000) : ℝ) = ((500000000000 / 843910807327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524160009 / 1000000000) ≤ -Real.log (10000000000 / 16890394751) ∧
    -Real.log (10000000000 / 16890394751) ≤ (52416001 / 100000000) := by
  have h := checkLog_sound (w := (6890394751 / 26890394751)) (n := 12)
    (lo := (524160009 / 1000000000)) (hi := (52416001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16890394751 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16890394751 / 10000000000) = 1/(10000000000 / 16890394751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524160009 / 1000000000) (52416001 / 100000000) (Real.log (16890394751 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16890394751 / 10000000000) = -Real.log (10000000000 / 16890394751) := by
    rw [show ((16890394751 / 10000000000) : ℝ) = ((10000000000 / 16890394751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0321
