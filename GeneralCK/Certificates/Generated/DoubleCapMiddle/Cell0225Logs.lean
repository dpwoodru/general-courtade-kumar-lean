import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0225
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

theorem reflection_log_1_neg : (63592413 / 250000000) ≤ -Real.log (5120 / 6603) ∧
    -Real.log (5120 / 6603) ≤ (254369653 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 11723)) (n := 12)
    (lo := (63592413 / 250000000)) (hi := (254369653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6603 / 5120) = 1/(5120 / 6603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (63592413 / 250000000) (254369653 / 1000000000) (Real.log (6603 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6603 / 5120) = -Real.log (5120 / 6603) := by
    rw [show ((6603 / 5120) : ℝ) = ((5120 / 6603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (341995273 / 1000000000) ≤ -Real.log (3637 / 5120) ∧
    -Real.log (3637 / 5120) ≤ (170997637 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 8757)) (n := 12)
    (lo := (341995273 / 1000000000)) (hi := (170997637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3637) = 1/(3637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170997637 / 500000000) (-341995273 / 1000000000) (Real.log (3637 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253915209 / 1000000000) ≤ -Real.log (128 / 165) ∧
    -Real.log (128 / 165) ≤ (25391521 / 100000000) := by
  have h := checkLog_sound (w := (37 / 293)) (n := 12)
    (lo := (253915209 / 1000000000)) (hi := (25391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165 / 128) = 1/(128 / 165) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253915209 / 1000000000) (25391521 / 100000000) (Real.log (165 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (165 / 128) = -Real.log (128 / 165) := by
    rw [show ((165 / 128) : ℝ) = ((128 / 165) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (341170757 / 1000000000) ≤ -Real.log (91 / 128) ∧
    -Real.log (91 / 128) ≤ (170585379 / 500000000) := by
  have h := checkLog_sound (w := (37 / 219)) (n := 12)
    (lo := (341170757 / 1000000000)) (hi := (170585379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 91) = 1/(91 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170585379 / 500000000) (-341170757 / 1000000000) (Real.log (91 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (114244933 / 250000000) ≤ -Real.log (2560 / 4043) ∧
    -Real.log (2560 / 4043) ≤ (456979733 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 6603)) (n := 12)
    (lo := (114244933 / 250000000)) (hi := (456979733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4043 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4043 / 2560) = 1/(2560 / 4043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (114244933 / 250000000) (456979733 / 1000000000) (Real.log (4043 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4043 / 2560) = -Real.log (2560 / 4043) := by
    rw [show ((4043 / 2560) : ℝ) = ((2560 / 4043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (865827859 / 1000000000) ≤ -Real.log (1077 / 2560) ∧
    -Real.log (1077 / 2560) ≤ (865827861 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2357)) (n := 12)
    (lo := (172680679 / 1000000000)) (hi := (4317017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1077) = 1/(1077 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-865827861 / 1000000000) (-865827859 / 1000000000) (Real.log (1077 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (456237433 / 1000000000) ≤ -Real.log (64 / 101) ∧
    -Real.log (64 / 101) ≤ (228118717 / 500000000) := by
  have h := checkLog_sound (w := (37 / 165)) (n := 12)
    (lo := (456237433 / 1000000000)) (hi := (228118717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101 / 64) = 1/(64 / 101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (456237433 / 1000000000) (228118717 / 500000000) (Real.log (101 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (101 / 64) = -Real.log (64 / 101) := by
    rw [show ((101 / 64) : ℝ) = ((64 / 101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (107880777 / 125000000) ≤ -Real.log (27 / 64) ∧
    -Real.log (27 / 64) ≤ (431523109 / 500000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 27) = 1/(27 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-431523109 / 500000000) (-107880777 / 125000000) (Real.log (27 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17372693 / 50000000) ≤ -Real.log (1000000 / 1415459) ∧
    -Real.log (1000000 / 1415459) ≤ (347453861 / 1000000000) := by
  have h := checkLog_sound (w := (415459 / 2415459)) (n := 12)
    (lo := (17372693 / 50000000)) (hi := (347453861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415459 / 1000000) = 1/(1000000 / 1415459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17372693 / 50000000) (347453861 / 1000000000) (Real.log (1415459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1415459 / 1000000) = -Real.log (1000000 / 1415459) := by
    rw [show ((1415459 / 1000000) : ℝ) = ((1000000 / 1415459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107385671 / 200000000) ≤ -Real.log (584541 / 1000000) ∧
    -Real.log (584541 / 1000000) ≤ (134232089 / 250000000) := by
  have h := checkLog_sound (w := (415459 / 1584541)) (n := 12)
    (lo := (107385671 / 200000000)) (hi := (134232089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 584541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 584541) = 1/(584541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-134232089 / 250000000) (-107385671 / 200000000) (Real.log (584541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (348072549 / 1000000000) ≤ -Real.log (200000 / 283267) ∧
    -Real.log (200000 / 283267) ≤ (6961451 / 20000000) := by
  have h := checkLog_sound (w := (83267 / 483267)) (n := 12)
    (lo := (348072549 / 1000000000)) (hi := (6961451 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283267 / 200000) = 1/(200000 / 283267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (348072549 / 1000000000) (6961451 / 20000000) (Real.log (283267 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (283267 / 200000) = -Real.log (200000 / 283267) := by
    rw [show ((283267 / 200000) : ℝ) = ((200000 / 283267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53842809 / 100000000) ≤ -Real.log (116733 / 200000) ∧
    -Real.log (116733 / 200000) ≤ (538428091 / 1000000000) := by
  have h := checkLog_sound (w := (83267 / 316733)) (n := 12)
    (lo := (53842809 / 100000000)) (hi := (538428091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 116733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 116733) = 1/(116733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-538428091 / 1000000000) (-53842809 / 100000000) (Real.log (116733 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1344369 / 5000000) ≤ -Real.log (100000 / 130849) ∧
    -Real.log (100000 / 130849) ≤ (268873801 / 1000000000) := by
  have h := checkLog_sound (w := (30849 / 230849)) (n := 12)
    (lo := (1344369 / 5000000)) (hi := (268873801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130849 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130849 / 100000) = 1/(100000 / 130849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1344369 / 5000000) (268873801 / 1000000000) (Real.log (130849 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (130849 / 100000) = -Real.log (100000 / 130849) := by
    rw [show ((130849 / 100000) : ℝ) = ((100000 / 130849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (184438833 / 500000000) ≤ -Real.log (69151 / 100000) ∧
    -Real.log (69151 / 100000) ≤ (368877667 / 1000000000) := by
  have h := checkLog_sound (w := (30849 / 169151)) (n := 12)
    (lo := (184438833 / 500000000)) (hi := (368877667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 69151) = 1/(69151 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-368877667 / 1000000000) (-184438833 / 500000000) (Real.log (69151 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134710041 / 500000000) ≤ -Real.log (200000 / 261841) ∧
    -Real.log (200000 / 261841) ≤ (269420083 / 1000000000) := by
  have h := checkLog_sound (w := (61841 / 461841)) (n := 12)
    (lo := (134710041 / 500000000)) (hi := (269420083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261841 / 200000) = 1/(200000 / 261841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134710041 / 500000000) (269420083 / 1000000000) (Real.log (261841 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (261841 / 200000) = -Real.log (200000 / 261841) := by
    rw [show ((261841 / 200000) : ℝ) = ((200000 / 261841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (36991217 / 100000000) ≤ -Real.log (138159 / 200000) ∧
    -Real.log (138159 / 200000) ≤ (369912171 / 1000000000) := by
  have h := checkLog_sound (w := (61841 / 338159)) (n := 12)
    (lo := (36991217 / 100000000)) (hi := (369912171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138159) = 1/(138159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-369912171 / 1000000000) (-36991217 / 100000000) (Real.log (138159 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442191107 / 500000000) ≤ -Real.log (500000000000 / 1210743985451) ∧
    -Real.log (500000000000 / 1210743985451) ≤ (110547777 / 125000000) := by
  have h := checkLog_sound (w := (210743985451 / 2210743985451)) (n := 12)
    (lo := (95617517 / 500000000)) (hi := (38247007 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210743985451 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1210743985451 / 1000000000000) = 1/(500000000000 / 1210743985451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442191107 / 500000000) (110547777 / 125000000) (Real.log (1210743985451 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1210743985451 / 500000000000) = -Real.log (500000000000 / 1210743985451) := by
    rw [show ((1210743985451 / 500000000000) : ℝ) = ((500000000000 / 1210743985451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (886500639 / 1000000000) ≤ -Real.log (500000000000 / 1213311574277) ∧
    -Real.log (500000000000 / 1213311574277) ≤ (886500641 / 1000000000) := by
  have h := checkLog_sound (w := (213311574277 / 2213311574277)) (n := 12)
    (lo := (193353459 / 1000000000)) (hi := (9667673 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213311574277 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1213311574277 / 1000000000000) = 1/(500000000000 / 1213311574277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (886500639 / 1000000000) (886500641 / 1000000000) (Real.log (1213311574277 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1213311574277 / 500000000000) = -Real.log (500000000000 / 1213311574277) := by
    rw [show ((1213311574277 / 500000000000) : ℝ) = ((500000000000 / 1213311574277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (637751467 / 1000000000) ≤ -Real.log (500000000000 / 946110685311) ∧
    -Real.log (500000000000 / 946110685311) ≤ (159437867 / 250000000) := by
  have h := checkLog_sound (w := (446110685311 / 1446110685311)) (n := 12)
    (lo := (637751467 / 1000000000)) (hi := (159437867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946110685311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946110685311 / 500000000000) = 1/(500000000000 / 946110685311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (637751467 / 1000000000) (159437867 / 250000000) (Real.log (946110685311 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (946110685311 / 500000000000) = -Real.log (500000000000 / 946110685311) := by
    rw [show ((946110685311 / 500000000000) : ℝ) = ((500000000000 / 946110685311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (639332253 / 1000000000) ≤ -Real.log (12500000000 / 23690186669) ∧
    -Real.log (12500000000 / 23690186669) ≤ (319666127 / 500000000) := by
  have h := checkLog_sound (w := (11190186669 / 36190186669)) (n := 12)
    (lo := (639332253 / 1000000000)) (hi := (319666127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23690186669 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23690186669 / 12500000000) = 1/(12500000000 / 23690186669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (639332253 / 1000000000) (319666127 / 500000000) (Real.log (23690186669 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23690186669 / 12500000000) = -Real.log (12500000000 / 23690186669) := by
    rw [show ((23690186669 / 12500000000) : ℝ) = ((12500000000 / 23690186669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0225
