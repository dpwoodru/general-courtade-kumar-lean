import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0143
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

theorem reflection_log_1_neg : (37078291 / 125000000) ≤ -Real.log (640 / 861) ∧
    -Real.log (640 / 861) ≤ (296626329 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1501)) (n := 12)
    (lo := (37078291 / 125000000)) (hi := (296626329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861 / 640) = 1/(640 / 861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37078291 / 125000000) (296626329 / 1000000000) (Real.log (861 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (861 / 640) = -Real.log (640 / 861) := by
    rw [show ((861 / 640) : ℝ) = ((640 / 861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52949657 / 125000000) ≤ -Real.log (419 / 640) ∧
    -Real.log (419 / 640) ≤ (423597257 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1059)) (n := 12)
    (lo := (52949657 / 125000000)) (hi := (423597257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 419) = 1/(419 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-423597257 / 1000000000) (-52949657 / 125000000) (Real.log (419 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73938717 / 250000000) ≤ -Real.log (2560 / 3441) ∧
    -Real.log (2560 / 3441) ≤ (295754869 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 6001)) (n := 12)
    (lo := (73938717 / 250000000)) (hi := (295754869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3441 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3441 / 2560) = 1/(2560 / 3441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73938717 / 250000000) (295754869 / 1000000000) (Real.log (3441 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3441 / 2560) = -Real.log (2560 / 3441) := by
    rw [show ((3441 / 2560) : ℝ) = ((2560 / 3441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5272611 / 12500000) ≤ -Real.log (1679 / 2560) ∧
    -Real.log (1679 / 2560) ≤ (421808881 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 4239)) (n := 12)
    (lo := (5272611 / 12500000)) (hi := (421808881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1679) = 1/(1679 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-421808881 / 1000000000) (-5272611 / 12500000) (Real.log (1679 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (525098283 / 1000000000) ≤ -Real.log (320 / 541) ∧
    -Real.log (320 / 541) ≤ (131274571 / 250000000) := by
  have h := checkLog_sound (w := (221 / 861)) (n := 12)
    (lo := (525098283 / 1000000000)) (hi := (131274571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541 / 320) = 1/(320 / 541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (525098283 / 1000000000) (131274571 / 250000000) (Real.log (541 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (541 / 320) = -Real.log (320 / 541) := by
    rw [show ((541 / 320) : ℝ) = ((320 / 541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (234640229 / 200000000) ≤ -Real.log (99 / 320) ∧
    -Real.log (99 / 320) ≤ (1173201147 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 99) = 1/(99 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1173201147 / 1000000000) (-234640229 / 200000000) (Real.log (99 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (523710999 / 1000000000) ≤ -Real.log (1280 / 2161) ∧
    -Real.log (1280 / 2161) ≤ (523711 / 1000000) := by
  have h := checkLog_sound (w := (881 / 3441)) (n := 12)
    (lo := (523710999 / 1000000000)) (hi := (523711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2161 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2161 / 1280) = 1/(1280 / 2161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (523710999 / 1000000000) (523711 / 1000000) (Real.log (2161 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2161 / 1280) = -Real.log (1280 / 2161) := by
    rw [show ((2161 / 1280) : ℝ) = ((1280 / 2161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1165653939 / 1000000000) ≤ -Real.log (399 / 1280) ∧
    -Real.log (399 / 1280) ≤ (1165653941 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 399) = 1/(399 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1165653941 / 1000000000) (-1165653939 / 1000000000) (Real.log (399 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (404725501 / 1000000000) ≤ -Real.log (1000000 / 1498891) ∧
    -Real.log (1000000 / 1498891) ≤ (202362751 / 500000000) := by
  have h := checkLog_sound (w := (498891 / 2498891)) (n := 12)
    (lo := (404725501 / 1000000000)) (hi := (202362751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1498891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1498891 / 1000000) = 1/(1000000 / 1498891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (404725501 / 1000000000) (202362751 / 500000000) (Real.log (1498891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1498891 / 1000000) = -Real.log (1000000 / 1498891) := by
    rw [show ((1498891 / 1000000) : ℝ) = ((1000000 / 1498891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (172732909 / 250000000) ≤ -Real.log (501109 / 1000000) ∧
    -Real.log (501109 / 1000000) ≤ (690931637 / 1000000000) := by
  have h := checkLog_sound (w := (498891 / 1501109)) (n := 12)
    (lo := (172732909 / 250000000)) (hi := (690931637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 501109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 501109) = 1/(501109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-690931637 / 1000000000) (-172732909 / 250000000) (Real.log (501109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (405930999 / 1000000000) ≤ -Real.log (1000000 / 1500699) ∧
    -Real.log (1000000 / 1500699) ≤ (405931 / 1000000) := by
  have h := checkLog_sound (w := (500699 / 2500699)) (n := 12)
    (lo := (405930999 / 1000000000)) (hi := (405931 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1500699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1500699 / 1000000) = 1/(1000000 / 1500699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (405930999 / 1000000000) (405931 / 1000000) (Real.log (1500699 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1500699 / 1000000) = -Real.log (1000000 / 1500699) := by
    rw [show ((1500699 / 1000000) : ℝ) = ((1000000 / 1500699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347273079 / 500000000) ≤ -Real.log (499301 / 1000000) ∧
    -Real.log (499301 / 1000000) ≤ (8681827 / 12500000) := by
  have h := checkLog_sound (w := (699 / 999301)) (n := 12)
    (lo := (699489 / 500000000)) (hi := (1398979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 499301) = 1/(499301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8681827 / 12500000) (-347273079 / 500000000) (Real.log (499301 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (321191797 / 1000000000) ≤ -Real.log (100000 / 137877) ∧
    -Real.log (100000 / 137877) ≤ (160595899 / 500000000) := by
  have h := checkLog_sound (w := (37877 / 237877)) (n := 12)
    (lo := (321191797 / 1000000000)) (hi := (160595899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137877 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137877 / 100000) = 1/(100000 / 137877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (321191797 / 1000000000) (160595899 / 500000000) (Real.log (137877 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (137877 / 100000) = -Real.log (100000 / 137877) := by
    rw [show ((137877 / 100000) : ℝ) = ((100000 / 137877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (95210779 / 200000000) ≤ -Real.log (62123 / 100000) ∧
    -Real.log (62123 / 100000) ≤ (59506737 / 125000000) := by
  have h := checkLog_sound (w := (37877 / 162123)) (n := 12)
    (lo := (95210779 / 200000000)) (hi := (59506737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62123) = 1/(62123 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59506737 / 125000000) (-95210779 / 200000000) (Real.log (62123 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20145887 / 62500000) ≤ -Real.log (500000 / 690173) ∧
    -Real.log (500000 / 690173) ≤ (322334193 / 1000000000) := by
  have h := checkLog_sound (w := (190173 / 1190173)) (n := 12)
    (lo := (20145887 / 62500000)) (hi := (322334193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690173 / 500000) = 1/(500000 / 690173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20145887 / 62500000) (322334193 / 1000000000) (Real.log (690173 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (690173 / 500000) = -Real.log (500000 / 690173) := by
    rw [show ((690173 / 500000) : ℝ) = ((500000 / 690173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (478594021 / 1000000000) ≤ -Real.log (309827 / 500000) ∧
    -Real.log (309827 / 500000) ≤ (239297011 / 500000000) := by
  have h := checkLog_sound (w := (190173 / 809827)) (n := 12)
    (lo := (478594021 / 1000000000)) (hi := (239297011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 309827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 309827) = 1/(309827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-239297011 / 500000000) (-478594021 / 1000000000) (Real.log (309827 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1095657137 / 1000000000) ≤ -Real.log (500000000000 / 1495573817273) ∧
    -Real.log (500000000000 / 1495573817273) ≤ (1095657139 / 1000000000) := by
  have h := checkLog_sound (w := (495573817273 / 2495573817273)) (n := 12)
    (lo := (402509957 / 1000000000)) (hi := (201254979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495573817273 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495573817273 / 1000000000000) = 1/(500000000000 / 1495573817273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1095657137 / 1000000000) (1095657139 / 1000000000) (Real.log (1495573817273 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1495573817273 / 500000000000) = -Real.log (500000000000 / 1495573817273) := by
    rw [show ((1495573817273 / 500000000000) : ℝ) = ((500000000000 / 1495573817273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1100477157 / 1000000000) ≤ -Real.log (500000000000 / 1502799914281) ∧
    -Real.log (500000000000 / 1502799914281) ≤ (1100477159 / 1000000000) := by
  have h := checkLog_sound (w := (502799914281 / 2502799914281)) (n := 12)
    (lo := (407329977 / 1000000000)) (hi := (203664989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502799914281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1502799914281 / 1000000000000) = 1/(500000000000 / 1502799914281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1100477157 / 1000000000) (1100477159 / 1000000000) (Real.log (1502799914281 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1502799914281 / 500000000000) = -Real.log (500000000000 / 1502799914281) := by
    rw [show ((1502799914281 / 500000000000) : ℝ) = ((500000000000 / 1502799914281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (199311423 / 250000000) ≤ -Real.log (31250000000 / 69356860583) ∧
    -Real.log (31250000000 / 69356860583) ≤ (398622847 / 500000000) := by
  have h := checkLog_sound (w := (6856860583 / 131856860583)) (n := 12)
    (lo := (6506157 / 62500000)) (hi := (104098513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69356860583 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69356860583 / 62500000000) = 1/(31250000000 / 69356860583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (199311423 / 250000000) (398622847 / 500000000) (Real.log (69356860583 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (69356860583 / 31250000000) = -Real.log (31250000000 / 69356860583) := by
    rw [show ((69356860583 / 31250000000) : ℝ) = ((31250000000 / 69356860583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (800928213 / 1000000000) ≤ -Real.log (250000000000 / 556901916231) ∧
    -Real.log (250000000000 / 556901916231) ≤ (160185643 / 200000000) := by
  have h := checkLog_sound (w := (56901916231 / 1056901916231)) (n := 12)
    (lo := (107781033 / 1000000000)) (hi := (53890517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556901916231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556901916231 / 500000000000) = 1/(250000000000 / 556901916231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (800928213 / 1000000000) (160185643 / 200000000) (Real.log (556901916231 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (556901916231 / 250000000000) = -Real.log (250000000000 / 556901916231) := by
    rw [show ((556901916231 / 250000000000) : ℝ) = ((250000000000 / 556901916231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0143
