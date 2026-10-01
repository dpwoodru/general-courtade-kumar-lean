import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15744_neg : (499249 / 500000000) ≤ -Real.log (499501 / 500000) ∧
    -Real.log (499501 / 500000) ≤ (998499 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 999501)) (n := 12)
    (lo := (499249 / 500000000)) (hi := (998499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499501) = 1/(499501 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15744 : Bounds (-998499 / 1000000000) (-499249 / 500000000) (Real.log (499501 / 500000)) := by
  have h := reflection_log_15744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15745_neg : (503278213 / 1000000000) ≤ -Real.log (200000 / 330827) ∧
    -Real.log (200000 / 330827) ≤ (251639107 / 500000000) := by
  have h := checkLog_sound (w := (130827 / 530827)) (n := 12)
    (lo := (503278213 / 1000000000)) (hi := (251639107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330827 / 200000) = 1/(200000 / 330827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15745 : Bounds (503278213 / 1000000000) (251639107 / 500000000) (Real.log (330827 / 200000)) := by
  have h := reflection_log_15745_neg
  have he : Real.log (330827 / 200000) = -Real.log (200000 / 330827) := by
    rw [show ((330827 / 200000) : ℝ) = ((200000 / 330827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15746_neg : (2073646 / 1953125) ≤ -Real.log (69173 / 200000) ∧
    -Real.log (69173 / 200000) ≤ (530853377 / 500000000) := by
  have h := checkLog_sound (w := (30827 / 169173)) (n := 12)
    (lo := (92139893 / 250000000)) (hi := (368559573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69173) = 1/(69173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15746 : Bounds (-530853377 / 500000000) (-2073646 / 1953125) (Real.log (69173 / 200000)) := by
  have h := reflection_log_15746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15747_neg : (503873513 / 1000000000) ≤ -Real.log (12500 / 20689) ∧
    -Real.log (12500 / 20689) ≤ (251936757 / 500000000) := by
  have h := checkLog_sound (w := (8189 / 33189)) (n := 12)
    (lo := (503873513 / 1000000000)) (hi := (251936757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20689 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20689 / 12500) = 1/(12500 / 20689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15747 : Bounds (503873513 / 1000000000) (251936757 / 500000000) (Real.log (20689 / 12500)) := by
  have h := reflection_log_15747_neg
  have he : Real.log (20689 / 12500) = -Real.log (12500 / 20689) := by
    rw [show ((20689 / 12500) : ℝ) = ((12500 / 20689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15748_neg : (1064558747 / 1000000000) ≤ -Real.log (4311 / 12500) ∧
    -Real.log (4311 / 12500) ≤ (1064558749 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 10561)) (n := 12)
    (lo := (371411567 / 1000000000)) (hi := (23213223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4311) = 1/(4311 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15748 : Bounds (-1064558749 / 1000000000) (-1064558747 / 1000000000) (Real.log (4311 / 12500)) := by
  have h := reflection_log_15748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15749_neg : (280342617 / 500000000) ≤ -Real.log (89190279 / 156250000) ∧
    -Real.log (89190279 / 156250000) ≤ (112137047 / 200000000) := by
  have h := checkLog_sound (w := (67059721 / 245440279)) (n := 12)
    (lo := (280342617 / 500000000)) (hi := (112137047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 89190279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 89190279) = 1/(89190279 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15749 : Bounds (-112137047 / 200000000) (-280342617 / 500000000) (Real.log (89190279 / 156250000)) := by
  have h := reflection_log_15749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15750_neg : (558428539 / 1000000000) ≤ -Real.log (22884296071 / 40000000000) ∧
    -Real.log (22884296071 / 40000000000) ≤ (27921427 / 50000000) := by
  have h := checkLog_sound (w := (17115703929 / 62884296071)) (n := 12)
    (lo := (558428539 / 1000000000)) (hi := (27921427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22884296071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22884296071) = 1/(22884296071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15750 : Bounds (-27921427 / 50000000) (-558428539 / 1000000000) (Real.log (22884296071 / 40000000000)) := by
  have h := reflection_log_15750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15751_neg : (312996993 / 200000000) ≤ -Real.log (250000000000 / 1195650759689) ∧
    -Real.log (250000000000 / 1195650759689) ≤ (195623121 / 125000000) := by
  have h := checkLog_sound (w := (195650759689 / 2195650759689)) (n := 12)
    (lo := (35738121 / 200000000)) (hi := (89345303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195650759689 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1195650759689 / 1000000000000) = 1/(250000000000 / 1195650759689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15751 : Bounds (312996993 / 200000000) (195623121 / 125000000) (Real.log (1195650759689 / 250000000000)) := by
  have h := reflection_log_15751_neg
  have he : Real.log (1195650759689 / 250000000000) = -Real.log (250000000000 / 1195650759689) := by
    rw [show ((1195650759689 / 250000000000) : ℝ) = ((250000000000 / 1195650759689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15752_neg : (1568432261 / 1000000000) ≤ -Real.log (31250000000 / 149972454187) ∧
    -Real.log (31250000000 / 149972454187) ≤ (196054033 / 125000000) := by
  have h := checkLog_sound (w := (24972454187 / 274972454187)) (n := 12)
    (lo := (182137901 / 1000000000)) (hi := (91068951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149972454187 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(149972454187 / 125000000000) = 1/(31250000000 / 149972454187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15752 : Bounds (1568432261 / 1000000000) (196054033 / 125000000) (Real.log (149972454187 / 31250000000)) := by
  have h := reflection_log_15752_neg
  have he : Real.log (149972454187 / 31250000000) = -Real.log (31250000000 / 149972454187) := by
    rw [show ((149972454187 / 31250000000) : ℝ) = ((31250000000 / 149972454187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15753_neg : (851418061 / 125000000) ≤ -Real.log (250000000000 / 227022727272727) ∧
    -Real.log (250000000000 / 227022727272727) ≤ (3405672249 / 500000000) := by
  have h := checkLog_sound (w := (99022727272727 / 355022727272727)) (n := 12)
    (lo := (143254967 / 250000000)) (hi := (573019869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227022727272727 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(227022727272727 / 128000000000000) = 1/(250000000000 / 227022727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15753 : Bounds (851418061 / 125000000) (3405672249 / 500000000) (Real.log (227022727272727 / 250000000000)) := by
  have h := reflection_log_15753_neg
  have he : Real.log (227022727272727 / 250000000000) = -Real.log (250000000000 / 227022727272727) := by
    rw [show ((227022727272727 / 250000000000) : ℝ) = ((250000000000 / 227022727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15754_neg : (6906754773 / 1000000000) ≤ -Real.log (1 / 999) ∧
    -Real.log (1 / 999) ≤ (6906754783 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 1511)) (n := 12)
    (lo := (668430153 / 1000000000)) (hi := (334215077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999 / 512) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(999 / 512) = 1/(1 / 999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15754 : Bounds (6906754773 / 1000000000) (6906754783 / 1000000000) (Real.log (999 / 1)) := by
  have h := reflection_log_15754_neg
  have he : Real.log (999 / 1) = -Real.log (1 / 999) := by
    rw [show ((999 / 1) : ℝ) = ((1 / 999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15755_neg : (27689871 / 40000000) ≤ -Real.log (5000 / 9991) ∧
    -Real.log (5000 / 9991) ≤ (86530847 / 125000000) := by
  have h := checkLog_sound (w := (4991 / 14991)) (n := 12)
    (lo := (27689871 / 40000000)) (hi := (86530847 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9991 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9991 / 5000) = 1/(5000 / 9991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15755 : Bounds (27689871 / 40000000) (86530847 / 125000000) (Real.log (9991 / 5000)) := by
  have h := reflection_log_15755_neg
  have he : Real.log (9991 / 5000) = -Real.log (5000 / 9991) := by
    rw [show ((9991 / 5000) : ℝ) = ((5000 / 9991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15756_neg : (6319968609 / 1000000000) ≤ -Real.log (9 / 5000) ∧
    -Real.log (9 / 5000) ≤ (6319968619 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 576) = 1/(9 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15756 : Bounds (-6319968619 / 1000000000) (-6319968609 / 1000000000) (Real.log (9 / 5000)) := by
  have h := reflection_log_15756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15757_neg : (498851 / 500000000) ≤ -Real.log (5000000 / 5004991) ∧
    -Real.log (5000000 / 5004991) ≤ (997703 / 1000000000) := by
  have h := checkLog_sound (w := (4991 / 10004991)) (n := 12)
    (lo := (498851 / 500000000)) (hi := (997703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004991 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004991 / 5000000) = 1/(5000000 / 5004991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15757 : Bounds (498851 / 500000000) (997703 / 1000000000) (Real.log (5004991 / 5000000)) := by
  have h := reflection_log_15757_neg
  have he : Real.log (5004991 / 5000000) = -Real.log (5000000 / 5004991) := by
    rw [show ((5004991 / 5000000) : ℝ) = ((5000000 / 5004991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15758_neg : (499349 / 500000000) ≤ -Real.log (4995009 / 5000000) ∧
    -Real.log (4995009 / 5000000) ≤ (998699 / 1000000000) := by
  have h := checkLog_sound (w := (4991 / 9995009)) (n := 12)
    (lo := (499349 / 500000000)) (hi := (998699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995009) = 1/(4995009 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15758 : Bounds (-998699 / 1000000000) (-499349 / 500000000) (Real.log (4995009 / 5000000)) := by
  have h := reflection_log_15758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15759_neg : (15734339 / 31250000) ≤ -Real.log (2000 / 3309) ∧
    -Real.log (2000 / 3309) ≤ (503498849 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 5309)) (n := 12)
    (lo := (15734339 / 31250000)) (hi := (503498849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2000) = 1/(2000 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15759 : Bounds (15734339 / 31250000) (503498849 / 1000000000) (Real.log (3309 / 2000)) := by
  have h := reflection_log_15759_neg
  have he : Real.log (3309 / 2000) = -Real.log (2000 / 3309) := by
    rw [show ((3309 / 2000) : ℝ) = ((2000 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15760_neg : (212552527 / 200000000) ≤ -Real.log (691 / 2000) ∧
    -Real.log (691 / 2000) ≤ (1062762637 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 1691)) (n := 12)
    (lo := (73923091 / 200000000)) (hi := (11550483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000 / 691) = 1/(691 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15760 : Bounds (-1062762637 / 1000000000) (-212552527 / 200000000) (Real.log (691 / 2000)) := by
  have h := reflection_log_15760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15761_neg : (504096433 / 1000000000) ≤ -Real.log (1000000 / 1655489) ∧
    -Real.log (1000000 / 1655489) ≤ (252048217 / 500000000) := by
  have h := checkLog_sound (w := (655489 / 2655489)) (n := 12)
    (lo := (504096433 / 1000000000)) (hi := (252048217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655489 / 1000000) = 1/(1000000 / 1655489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15761 : Bounds (504096433 / 1000000000) (252048217 / 500000000) (Real.log (1655489 / 1000000)) := by
  have h := reflection_log_15761_neg
  have he : Real.log (1655489 / 1000000) = -Real.log (1000000 / 1655489) := by
    rw [show ((1655489 / 1000000) : ℝ) = ((1000000 / 1655489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15762_neg : (532814629 / 500000000) ≤ -Real.log (344511 / 1000000) ∧
    -Real.log (344511 / 1000000) ≤ (53281463 / 50000000) := by
  have h := checkLog_sound (w := (155489 / 844511)) (n := 12)
    (lo := (186241039 / 500000000)) (hi := (372482079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344511) = 1/(344511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15762 : Bounds (-53281463 / 50000000) (-532814629 / 500000000) (Real.log (344511 / 1000000)) := by
  have h := reflection_log_15762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15763_neg : (22461313 / 40000000) ≤ -Real.log (570334170879 / 1000000000000) ∧
    -Real.log (570334170879 / 1000000000000) ≤ (280766413 / 500000000) := by
  have h := checkLog_sound (w := (429665829121 / 1570334170879)) (n := 12)
    (lo := (22461313 / 40000000)) (hi := (280766413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 570334170879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 570334170879) = 1/(570334170879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15763 : Bounds (-280766413 / 500000000) (-22461313 / 40000000) (Real.log (570334170879 / 1000000000000)) := by
  have h := reflection_log_15763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15764_neg : (559263787 / 1000000000) ≤ -Real.log (2286519 / 4000000) ∧
    -Real.log (2286519 / 4000000) ≤ (139815947 / 250000000) := by
  have h := checkLog_sound (w := (1713481 / 6286519)) (n := 12)
    (lo := (559263787 / 1000000000)) (hi := (139815947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 2286519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 2286519) = 1/(2286519 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15764 : Bounds (-139815947 / 250000000) (-559263787 / 1000000000) (Real.log (2286519 / 4000000)) := by
  have h := reflection_log_15764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15765_neg : (1566261483 / 1000000000) ≤ -Real.log (125000000000 / 598589001447) ∧
    -Real.log (125000000000 / 598589001447) ≤ (783130743 / 500000000) := by
  have h := checkLog_sound (w := (98589001447 / 1098589001447)) (n := 12)
    (lo := (179967123 / 1000000000)) (hi := (44991781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598589001447 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(598589001447 / 500000000000) = 1/(125000000000 / 598589001447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15765 : Bounds (1566261483 / 1000000000) (783130743 / 500000000) (Real.log (598589001447 / 125000000000)) := by
  have h := reflection_log_15765_neg
  have he : Real.log (598589001447 / 125000000000) = -Real.log (125000000000 / 598589001447) := by
    rw [show ((598589001447 / 125000000000) : ℝ) = ((125000000000 / 598589001447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15766_neg : (1569725691 / 1000000000) ≤ -Real.log (500000000000 / 2402664936679) ∧
    -Real.log (500000000000 / 2402664936679) ≤ (784862847 / 500000000) := by
  have h := checkLog_sound (w := (402664936679 / 4402664936679)) (n := 12)
    (lo := (183431331 / 1000000000)) (hi := (45857833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2402664936679 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2402664936679 / 2000000000000) = 1/(500000000000 / 2402664936679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15766 : Bounds (1569725691 / 1000000000) (784862847 / 500000000) (Real.log (2402664936679 / 500000000000)) := by
  have h := reflection_log_15766_neg
  have he : Real.log (2402664936679 / 500000000000) = -Real.log (500000000000 / 2402664936679) := by
    rw [show ((2402664936679 / 500000000000) : ℝ) = ((500000000000 / 2402664936679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15767_neg : (7012215383 / 1000000000) ≤ -Real.log (125000000000 / 138763888888889) ∧
    -Real.log (125000000000 / 138763888888889) ≤ (3506107697 / 500000000) := by
  have h := checkLog_sound (w := (10763888888889 / 266763888888889)) (n := 12)
    (lo := (80743583 / 1000000000)) (hi := (2523237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138763888888889 / 128000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(138763888888889 / 128000000000000) = 1/(125000000000 / 138763888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15767 : Bounds (7012215383 / 1000000000) (3506107697 / 500000000) (Real.log (138763888888889 / 125000000000)) := by
  have h := reflection_log_15767_neg
  have he : Real.log (138763888888889 / 125000000000) = -Real.log (125000000000 / 138763888888889) := by
    rw [show ((138763888888889 / 125000000000) : ℝ) = ((125000000000 / 138763888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15768_neg : (34617343 / 50000000) ≤ -Real.log (625 / 1249) ∧
    -Real.log (625 / 1249) ≤ (692346861 / 1000000000) := by
  have h := checkLog_sound (w := (312 / 937)) (n := 12)
    (lo := (34617343 / 50000000)) (hi := (692346861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249 / 625) = 1/(625 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15768 : Bounds (34617343 / 50000000) (692346861 / 1000000000) (Real.log (1249 / 625)) := by
  have h := reflection_log_15768_neg
  have he : Real.log (1249 / 625) = -Real.log (625 / 1249) := by
    rw [show ((1249 / 625) : ℝ) = ((625 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15769_neg : (1609437911 / 250000000) ≤ -Real.log (1 / 625) ∧
    -Real.log (1 / 625) ≤ (3218875827 / 500000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 512) = 1/(1 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15769 : Bounds (-3218875827 / 500000000) (-1609437911 / 250000000) (Real.log (1 / 625)) := by
  have h := reflection_log_15769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15770_neg : (997901 / 1000000000) ≤ -Real.log (78125 / 78203) ∧
    -Real.log (78125 / 78203) ≤ (498951 / 500000000) := by
  have h := checkLog_sound (w := (39 / 78164)) (n := 12)
    (lo := (997901 / 1000000000)) (hi := (498951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78203 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78203 / 78125) = 1/(78125 / 78203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15770 : Bounds (997901 / 1000000000) (498951 / 500000000) (Real.log (78203 / 78125)) := by
  have h := reflection_log_15770_neg
  have he : Real.log (78203 / 78125) = -Real.log (78125 / 78203) := by
    rw [show ((78203 / 78125) : ℝ) = ((78125 / 78203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15771_neg : (499449 / 500000000) ≤ -Real.log (78047 / 78125) ∧
    -Real.log (78047 / 78125) ≤ (998899 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 78086)) (n := 12)
    (lo := (499449 / 500000000)) (hi := (998899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78047) = 1/(78047 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15771 : Bounds (-998899 / 1000000000) (-499449 / 500000000) (Real.log (78047 / 78125)) := by
  have h := reflection_log_15771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15772_neg : (503721851 / 1000000000) ≤ -Real.log (1000000 / 1654869) ∧
    -Real.log (1000000 / 1654869) ≤ (125930463 / 250000000) := by
  have h := checkLog_sound (w := (654869 / 2654869)) (n := 12)
    (lo := (503721851 / 1000000000)) (hi := (125930463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1654869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1654869 / 1000000) = 1/(1000000 / 1654869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15772 : Bounds (503721851 / 1000000000) (125930463 / 250000000) (Real.log (1654869 / 1000000)) := by
  have h := reflection_log_15772_neg
  have he : Real.log (1654869 / 1000000) = -Real.log (1000000 / 1654869) := by
    rw [show ((1654869 / 1000000) : ℝ) = ((1000000 / 1654869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15773_neg : (1063831223 / 1000000000) ≤ -Real.log (345131 / 1000000) ∧
    -Real.log (345131 / 1000000) ≤ (42553249 / 40000000) := by
  have h := checkLog_sound (w := (154869 / 845131)) (n := 12)
    (lo := (370684043 / 1000000000)) (hi := (92671011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 345131) = 1/(345131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15773 : Bounds (-42553249 / 40000000) (-1063831223 / 1000000000) (Real.log (345131 / 1000000)) := by
  have h := reflection_log_15773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15774_neg : (504322323 / 1000000000) ≤ -Real.log (1000000 / 1655863) ∧
    -Real.log (1000000 / 1655863) ≤ (126080581 / 250000000) := by
  have h := checkLog_sound (w := (655863 / 2655863)) (n := 12)
    (lo := (504322323 / 1000000000)) (hi := (126080581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655863 / 1000000) = 1/(1000000 / 1655863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15774 : Bounds (504322323 / 1000000000) (126080581 / 250000000) (Real.log (1655863 / 1000000)) := by
  have h := reflection_log_15774_neg
  have he : Real.log (1655863 / 1000000) = -Real.log (1000000 / 1655863) := by
    rw [show ((1655863 / 1000000) : ℝ) = ((1000000 / 1655863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15775_neg : (266678861 / 250000000) ≤ -Real.log (344137 / 1000000) ∧
    -Real.log (344137 / 1000000) ≤ (533357723 / 500000000) := by
  have h := checkLog_sound (w := (155863 / 844137)) (n := 12)
    (lo := (46696033 / 125000000)) (hi := (74713653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344137) = 1/(344137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15775 : Bounds (-533357723 / 500000000) (-266678861 / 250000000) (Real.log (344137 / 1000000)) := by
  have h := reflection_log_15775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15776_neg : (281196561 / 500000000) ≤ -Real.log (569843725231 / 1000000000000) ∧
    -Real.log (569843725231 / 1000000000000) ≤ (562393123 / 1000000000) := by
  have h := checkLog_sound (w := (430156274769 / 1569843725231)) (n := 12)
    (lo := (281196561 / 500000000)) (hi := (562393123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 569843725231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 569843725231) = 1/(569843725231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15776 : Bounds (-562393123 / 1000000000) (-281196561 / 500000000) (Real.log (569843725231 / 1000000000000)) := by
  have h := reflection_log_15776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15777_neg : (140027343 / 250000000) ≤ -Real.log (571146592839 / 1000000000000) ∧
    -Real.log (571146592839 / 1000000000000) ≤ (560109373 / 1000000000) := by
  have h := checkLog_sound (w := (428853407161 / 1571146592839)) (n := 12)
    (lo := (140027343 / 250000000)) (hi := (560109373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 571146592839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 571146592839) = 1/(571146592839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15777 : Bounds (-560109373 / 1000000000) (-140027343 / 250000000) (Real.log (571146592839 / 1000000000000)) := by
  have h := reflection_log_15777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15778_neg : (783776537 / 500000000) ≤ -Real.log (20000000000 / 95898021331) ∧
    -Real.log (20000000000 / 95898021331) ≤ (1567553077 / 1000000000) := by
  have h := checkLog_sound (w := (15898021331 / 175898021331)) (n := 12)
    (lo := (90629357 / 500000000)) (hi := (36251743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95898021331 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(95898021331 / 80000000000) = 1/(20000000000 / 95898021331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15778 : Bounds (783776537 / 500000000) (1567553077 / 1000000000) (Real.log (95898021331 / 20000000000)) := by
  have h := reflection_log_15778_neg
  have he : Real.log (95898021331 / 20000000000) = -Real.log (20000000000 / 95898021331) := by
    rw [show ((95898021331 / 20000000000) : ℝ) = ((20000000000 / 95898021331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15779_neg : (1571037767 / 1000000000) ≤ -Real.log (250000000000 / 1202909742341) ∧
    -Real.log (250000000000 / 1202909742341) ≤ (157103777 / 100000000) := by
  have h := checkLog_sound (w := (202909742341 / 2202909742341)) (n := 12)
    (lo := (184743407 / 1000000000)) (hi := (11546463 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202909742341 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1202909742341 / 1000000000000) = 1/(250000000000 / 1202909742341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15779 : Bounds (1571037767 / 1000000000) (157103777 / 100000000) (Real.log (1202909742341 / 250000000000)) := by
  have h := reflection_log_15779_neg
  have he : Real.log (1202909742341 / 250000000000) = -Real.log (250000000000 / 1202909742341) := by
    rw [show ((1202909742341 / 250000000000) : ℝ) = ((250000000000 / 1202909742341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15780_neg : (7012215383 / 1000000000) ≤ -Real.log (100000000000 / 111011111111111) ∧
    -Real.log (100000000000 / 111011111111111) ≤ (3506107697 / 500000000) := by
  have h := checkLog_sound (w := (8611111111111 / 213411111111111)) (n := 12)
    (lo := (80743583 / 1000000000)) (hi := (2523237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111011111111111 / 102400000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(111011111111111 / 102400000000000) = 1/(100000000000 / 111011111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15780 : Bounds (7012215383 / 1000000000) (3506107697 / 500000000) (Real.log (111011111111111 / 100000000000)) := by
  have h := reflection_log_15780_neg
  have he : Real.log (111011111111111 / 100000000000) = -Real.log (100000000000 / 111011111111111) := by
    rw [show ((111011111111111 / 100000000000) : ℝ) = ((100000000000 / 111011111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15781_neg : (891262313 / 125000000) ≤ -Real.log (1 / 1249) ∧
    -Real.log (1 / 1249) ≤ (1426019703 / 200000000) := by
  have h := checkLog_sound (w := (225 / 2273)) (n := 12)
    (lo := (12414169 / 62500000)) (hi := (39725341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 1024) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(1249 / 1024) = 1/(1 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15781 : Bounds (891262313 / 125000000) (1426019703 / 200000000) (Real.log (1249 / 1)) := by
  have h := reflection_log_15781_neg
  have he : Real.log (1249 / 1) = -Real.log (1 / 1249) := by
    rw [show ((1249 / 1) : ℝ) = ((1 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15782_neg : (138489387 / 200000000) ≤ -Real.log (5000 / 9993) ∧
    -Real.log (5000 / 9993) ≤ (86555867 / 125000000) := by
  have h := checkLog_sound (w := (4993 / 14993)) (n := 12)
    (lo := (138489387 / 200000000)) (hi := (86555867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9993 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9993 / 5000) = 1/(5000 / 9993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15782 : Bounds (138489387 / 200000000) (86555867 / 125000000) (Real.log (9993 / 5000)) := by
  have h := reflection_log_15782_neg
  have he : Real.log (9993 / 5000) = -Real.log (5000 / 9993) := by
    rw [show ((9993 / 5000) : ℝ) = ((5000 / 9993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15783_neg : (6571283037 / 1000000000) ≤ -Real.log (7 / 5000) ∧
    -Real.log (7 / 5000) ≤ (6571283047 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 448) = 1/(7 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15783 : Bounds (-6571283047 / 1000000000) (-6571283037 / 1000000000) (Real.log (7 / 5000)) := by
  have h := reflection_log_15783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15784_neg : (998101 / 1000000000) ≤ -Real.log (5000000 / 5004993) ∧
    -Real.log (5000000 / 5004993) ≤ (499051 / 500000000) := by
  have h := checkLog_sound (w := (4993 / 10004993)) (n := 12)
    (lo := (998101 / 1000000000)) (hi := (499051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004993 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004993 / 5000000) = 1/(5000000 / 5004993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15784 : Bounds (998101 / 1000000000) (499051 / 500000000) (Real.log (5004993 / 5000000)) := by
  have h := reflection_log_15784_neg
  have he : Real.log (5004993 / 5000000) = -Real.log (5000000 / 5004993) := by
    rw [show ((5004993 / 5000000) : ℝ) = ((5000000 / 5004993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15785_neg : (499549 / 500000000) ≤ -Real.log (4995007 / 5000000) ∧
    -Real.log (4995007 / 5000000) ≤ (999099 / 1000000000) := by
  have h := checkLog_sound (w := (4993 / 9995007)) (n := 12)
    (lo := (499549 / 500000000)) (hi := (999099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995007) = 1/(4995007 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15785 : Bounds (-999099 / 1000000000) (-499549 / 500000000) (Real.log (4995007 / 5000000)) := by
  have h := reflection_log_15785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15786_neg : (503948429 / 1000000000) ≤ -Real.log (250000 / 413811) ∧
    -Real.log (250000 / 413811) ≤ (50394843 / 100000000) := by
  have h := checkLog_sound (w := (163811 / 663811)) (n := 12)
    (lo := (503948429 / 1000000000)) (hi := (50394843 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413811 / 250000) = 1/(250000 / 413811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15786 : Bounds (503948429 / 1000000000) (50394843 / 100000000) (Real.log (413811 / 250000)) := by
  have h := reflection_log_15786_neg
  have he : Real.log (413811 / 250000) = -Real.log (250000 / 413811) := by
    rw [show ((413811 / 250000) : ℝ) = ((250000 / 413811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15787_neg : (1064918357 / 1000000000) ≤ -Real.log (86189 / 250000) ∧
    -Real.log (86189 / 250000) ≤ (1064918359 / 1000000000) := by
  have h := checkLog_sound (w := (38811 / 211189)) (n := 12)
    (lo := (371771177 / 1000000000)) (hi := (185885589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86189) = 1/(86189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15787 : Bounds (-1064918359 / 1000000000) (-1064918357 / 1000000000) (Real.log (86189 / 250000)) := by
  have h := reflection_log_15787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15788_neg : (63068973 / 125000000) ≤ -Real.log (1000000 / 1656243) ∧
    -Real.log (1000000 / 1656243) ≤ (100910357 / 200000000) := by
  have h := checkLog_sound (w := (656243 / 2656243)) (n := 12)
    (lo := (63068973 / 125000000)) (hi := (100910357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1656243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1656243 / 1000000) = 1/(1000000 / 1656243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15788 : Bounds (63068973 / 125000000) (100910357 / 200000000) (Real.log (1656243 / 1000000)) := by
  have h := reflection_log_15788_neg
  have he : Real.log (1656243 / 1000000) = -Real.log (1000000 / 1656243) := by
    rw [show ((1656243 / 1000000) : ℝ) = ((1000000 / 1656243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15789_neg : (533910133 / 500000000) ≤ -Real.log (343757 / 1000000) ∧
    -Real.log (343757 / 1000000) ≤ (266955067 / 250000000) := by
  have h := checkLog_sound (w := (156243 / 843757)) (n := 12)
    (lo := (187336543 / 500000000)) (hi := (374673087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 343757) = 1/(343757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15789 : Bounds (-266955067 / 250000000) (-533910133 / 500000000) (Real.log (343757 / 1000000)) := by
  have h := reflection_log_15789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15790_neg : (281634241 / 500000000) ≤ -Real.log (569345124951 / 1000000000000) ∧
    -Real.log (569345124951 / 1000000000000) ≤ (563268483 / 1000000000) := by
  have h := checkLog_sound (w := (430654875049 / 1569345124951)) (n := 12)
    (lo := (281634241 / 500000000)) (hi := (563268483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 569345124951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 569345124951) = 1/(569345124951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15790 : Bounds (-563268483 / 1000000000) (-281634241 / 500000000) (Real.log (569345124951 / 1000000000000)) := by
  have h := reflection_log_15790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15791_neg : (70121241 / 125000000) ≤ -Real.log (35665956279 / 62500000000) ∧
    -Real.log (35665956279 / 62500000000) ≤ (560969929 / 1000000000) := by
  have h := checkLog_sound (w := (26834043721 / 98165956279)) (n := 12)
    (lo := (70121241 / 125000000)) (hi := (560969929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35665956279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35665956279) = 1/(35665956279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15791 : Bounds (-560969929 / 1000000000) (-70121241 / 125000000) (Real.log (35665956279 / 62500000000)) := by
  have h := reflection_log_15791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15792_neg : (1568866787 / 1000000000) ≤ -Real.log (500000000000 / 2400602165009) ∧
    -Real.log (500000000000 / 2400602165009) ≤ (156886679 / 100000000) := by
  have h := checkLog_sound (w := (400602165009 / 4400602165009)) (n := 12)
    (lo := (182572427 / 1000000000)) (hi := (45643107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400602165009 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2400602165009 / 2000000000000) = 1/(500000000000 / 2400602165009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15792 : Bounds (1568866787 / 1000000000) (156886679 / 100000000) (Real.log (2400602165009 / 500000000000)) := by
  have h := reflection_log_15792_neg
  have he : Real.log (2400602165009 / 500000000000) = -Real.log (500000000000 / 2400602165009) := by
    rw [show ((2400602165009 / 500000000000) : ℝ) = ((500000000000 / 2400602165009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15793_neg : (1572372049 / 1000000000) ≤ -Real.log (125000000000 / 602257917657) ∧
    -Real.log (125000000000 / 602257917657) ≤ (393093013 / 250000000) := by
  have h := checkLog_sound (w := (102257917657 / 1102257917657)) (n := 12)
    (lo := (186077689 / 1000000000)) (hi := (18607769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602257917657 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(602257917657 / 500000000000) = 1/(125000000000 / 602257917657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15793 : Bounds (1572372049 / 1000000000) (393093013 / 250000000) (Real.log (602257917657 / 125000000000)) := by
  have h := reflection_log_15793_neg
  have he : Real.log (602257917657 / 125000000000) = -Real.log (125000000000 / 602257917657) := by
    rw [show ((602257917657 / 125000000000) : ℝ) = ((125000000000 / 602257917657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15794_neg : (1815932493 / 250000000) ≤ -Real.log (100000000000 / 142757142857143) ∧
    -Real.log (100000000000 / 142757142857143) ≤ (7263729983 / 1000000000) := by
  have h := checkLog_sound (w := (40357142857143 / 245157142857143)) (n := 12)
    (lo := (83064543 / 250000000)) (hi := (332258173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142757142857143 / 102400000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(142757142857143 / 102400000000000) = 1/(100000000000 / 142757142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15794 : Bounds (1815932493 / 250000000) (7263729983 / 1000000000) (Real.log (142757142857143 / 100000000000)) := by
  have h := reflection_log_15794_neg
  have he : Real.log (142757142857143 / 100000000000) = -Real.log (100000000000 / 142757142857143) := by
    rw [show ((142757142857143 / 100000000000) : ℝ) = ((100000000000 / 142757142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15795_neg : (692547 / 1000000) ≤ -Real.log (2500 / 4997) ∧
    -Real.log (2500 / 4997) ≤ (692547001 / 1000000000) := by
  have h := checkLog_sound (w := (2497 / 7497)) (n := 12)
    (lo := (692547 / 1000000)) (hi := (692547001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4997 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4997 / 2500) = 1/(2500 / 4997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15795 : Bounds (692547 / 1000000) (692547001 / 1000000000) (Real.log (4997 / 2500)) := by
  have h := reflection_log_15795_neg
  have he : Real.log (4997 / 2500) = -Real.log (2500 / 4997) := by
    rw [show ((4997 / 2500) : ℝ) = ((2500 / 4997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15796_neg : (6725433717 / 1000000000) ≤ -Real.log (3 / 2500) ∧
    -Real.log (3 / 2500) ≤ (6725433727 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 384) = 1/(3 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15796 : Bounds (-6725433727 / 1000000000) (-6725433717 / 1000000000) (Real.log (3 / 2500)) := by
  have h := reflection_log_15796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15797_neg : (998301 / 1000000000) ≤ -Real.log (2500000 / 2502497) ∧
    -Real.log (2500000 / 2502497) ≤ (499151 / 500000000) := by
  have h := checkLog_sound (w := (2497 / 5002497)) (n := 12)
    (lo := (998301 / 1000000000)) (hi := (499151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502497 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502497 / 2500000) = 1/(2500000 / 2502497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15797 : Bounds (998301 / 1000000000) (499151 / 500000000) (Real.log (2502497 / 2500000)) := by
  have h := reflection_log_15797_neg
  have he : Real.log (2502497 / 2500000) = -Real.log (2500000 / 2502497) := by
    rw [show ((2502497 / 2500000) : ℝ) = ((2500000 / 2502497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15798_neg : (999299 / 1000000000) ≤ -Real.log (2497503 / 2500000) ∧
    -Real.log (2497503 / 2500000) ≤ (9993 / 10000000) := by
  have h := checkLog_sound (w := (2497 / 4997503)) (n := 12)
    (lo := (999299 / 1000000000)) (hi := (9993 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497503) = 1/(2497503 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15798 : Bounds (-9993 / 10000000) (-999299 / 1000000000) (Real.log (2497503 / 2500000)) := by
  have h := reflection_log_15798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15799_neg : (504177977 / 1000000000) ≤ -Real.log (125000 / 206953) ∧
    -Real.log (125000 / 206953) ≤ (252088989 / 500000000) := by
  have h := checkLog_sound (w := (81953 / 331953)) (n := 12)
    (lo := (504177977 / 1000000000)) (hi := (252088989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206953 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206953 / 125000) = 1/(125000 / 206953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15799 : Bounds (504177977 / 1000000000) (252088989 / 500000000) (Real.log (206953 / 125000)) := by
  have h := reflection_log_15799_neg
  have he : Real.log (206953 / 125000) = -Real.log (125000 / 206953) := by
    rw [show ((206953 / 125000) : ℝ) = ((125000 / 206953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15800_neg : (533010597 / 500000000) ≤ -Real.log (43047 / 125000) ∧
    -Real.log (43047 / 125000) ≤ (266505299 / 250000000) := by
  have h := checkLog_sound (w := (19453 / 105547)) (n := 12)
    (lo := (186437007 / 500000000)) (hi := (74574803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43047) = 1/(43047 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15800 : Bounds (-266505299 / 250000000) (-533010597 / 500000000) (Real.log (43047 / 125000)) := by
  have h := reflection_log_15800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15801_neg : (252392407 / 500000000) ≤ -Real.log (1000000 / 1656629) ∧
    -Real.log (1000000 / 1656629) ≤ (100956963 / 200000000) := by
  have h := checkLog_sound (w := (656629 / 2656629)) (n := 12)
    (lo := (252392407 / 500000000)) (hi := (100956963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1656629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1656629 / 1000000) = 1/(1000000 / 1656629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15801 : Bounds (252392407 / 500000000) (100956963 / 200000000) (Real.log (1656629 / 1000000)) := by
  have h := reflection_log_15801_neg
  have he : Real.log (1656629 / 1000000) = -Real.log (1000000 / 1656629) := by
    rw [show ((1656629 / 1000000) : ℝ) = ((1000000 / 1656629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15802_neg : (1068943783 / 1000000000) ≤ -Real.log (343371 / 1000000) ∧
    -Real.log (343371 / 1000000) ≤ (213788757 / 200000000) := by
  have h := checkLog_sound (w := (156629 / 843371)) (n := 12)
    (lo := (375796603 / 1000000000)) (hi := (93949151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 343371) = 1/(343371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15802 : Bounds (-213788757 / 200000000) (-1068943783 / 1000000000) (Real.log (343371 / 1000000)) := by
  have h := reflection_log_15802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15803_neg : (70519871 / 125000000) ≤ -Real.log (568838356359 / 1000000000000) ∧
    -Real.log (568838356359 / 1000000000000) ≤ (564158969 / 1000000000) := by
  have h := checkLog_sound (w := (431161643641 / 1568838356359)) (n := 12)
    (lo := (70519871 / 125000000)) (hi := (564158969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 568838356359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 568838356359) = 1/(568838356359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15803 : Bounds (-564158969 / 1000000000) (-70519871 / 125000000) (Real.log (568838356359 / 1000000000000)) := by
  have h := reflection_log_15803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15804_neg : (280921609 / 500000000) ≤ -Real.log (8908705791 / 15625000000) ∧
    -Real.log (8908705791 / 15625000000) ≤ (561843219 / 1000000000) := by
  have h := checkLog_sound (w := (6716294209 / 24533705791)) (n := 12)
    (lo := (280921609 / 500000000)) (hi := (561843219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 8908705791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 8908705791) = 1/(8908705791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15804 : Bounds (-561843219 / 1000000000) (-280921609 / 500000000) (Real.log (8908705791 / 15625000000)) := by
  have h := reflection_log_15804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15805_neg : (1570199171 / 1000000000) ≤ -Real.log (500000000000 / 2403802820173) ∧
    -Real.log (500000000000 / 2403802820173) ≤ (785099587 / 500000000) := by
  have h := checkLog_sound (w := (403802820173 / 4403802820173)) (n := 12)
    (lo := (183904811 / 1000000000)) (hi := (45976203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2403802820173 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2403802820173 / 2000000000000) = 1/(500000000000 / 2403802820173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15805 : Bounds (1570199171 / 1000000000) (785099587 / 500000000) (Real.log (2403802820173 / 500000000000)) := by
  have h := reflection_log_15805_neg
  have he : Real.log (2403802820173 / 500000000000) = -Real.log (500000000000 / 2403802820173) := by
    rw [show ((2403802820173 / 500000000000) : ℝ) = ((500000000000 / 2403802820173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15806_neg : (1573728597 / 1000000000) ≤ -Real.log (500000000000 / 2412301854263) ∧
    -Real.log (500000000000 / 2412301854263) ≤ (7868643 / 5000000) := by
  have h := checkLog_sound (w := (412301854263 / 4412301854263)) (n := 12)
    (lo := (187434237 / 1000000000)) (hi := (93717119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2412301854263 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2412301854263 / 2000000000000) = 1/(500000000000 / 2412301854263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15806 : Bounds (1573728597 / 1000000000) (7868643 / 5000000) (Real.log (2412301854263 / 500000000000)) := by
  have h := reflection_log_15806_neg
  have he : Real.log (2412301854263 / 500000000000) = -Real.log (500000000000 / 2412301854263) := by
    rw [show ((2412301854263 / 500000000000) : ℝ) = ((500000000000 / 2412301854263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15807_neg : (1815932493 / 250000000) ≤ -Real.log (250000000000 / 356892857142857) ∧
    -Real.log (250000000000 / 356892857142857) ≤ (7263729983 / 1000000000) := by
  have h := checkLog_sound (w := (100892857142857 / 612892857142857)) (n := 12)
    (lo := (83064543 / 250000000)) (hi := (332258173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356892857142857 / 256000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(356892857142857 / 256000000000000) = 1/(250000000000 / 356892857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15807 : Bounds (1815932493 / 250000000) (7263729983 / 1000000000) (Real.log (356892857142857 / 250000000000)) := by
  have h := reflection_log_15807_neg
  have he : Real.log (356892857142857 / 250000000000) = -Real.log (250000000000 / 356892857142857) := by
    rw [show ((356892857142857 / 250000000000) : ℝ) = ((250000000000 / 356892857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
