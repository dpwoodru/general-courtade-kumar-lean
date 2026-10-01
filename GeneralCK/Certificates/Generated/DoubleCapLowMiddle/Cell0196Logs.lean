import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0196
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

theorem reflection_log_1_neg : (120058983 / 200000000) ≤ -Real.log (1280 / 2333) ∧
    -Real.log (1280 / 2333) ≤ (150073729 / 250000000) := by
  have h := checkLog_sound (w := (1053 / 3613)) (n := 12)
    (lo := (120058983 / 200000000)) (hi := (150073729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 1280) = 1/(1280 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (120058983 / 200000000) (150073729 / 250000000) (Real.log (2333 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2333 / 1280) = -Real.log (1280 / 2333) := by
    rw [show ((2333 / 1280) : ℝ) = ((1280 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (864832669 / 500000000) ≤ -Real.log (227 / 1280) ∧
    -Real.log (227 / 1280) ≤ (1729665341 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 227) = 1/(227 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1729665341 / 1000000000) (-864832669 / 500000000) (Real.log (227 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (598664783 / 1000000000) ≤ -Real.log (3200 / 5823) ∧
    -Real.log (3200 / 5823) ≤ (37416549 / 62500000) := by
  have h := checkLog_sound (w := (2623 / 9023)) (n := 12)
    (lo := (598664783 / 1000000000)) (hi := (37416549 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 3200) = 1/(3200 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (598664783 / 1000000000) (37416549 / 62500000) (Real.log (5823 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5823 / 3200) = -Real.log (3200 / 5823) := by
    rw [show ((5823 / 3200) : ℝ) = ((3200 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1713063821 / 1000000000) ≤ -Real.log (577 / 3200) ∧
    -Real.log (577 / 3200) ≤ (107066489 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 577) = 1/(577 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-107066489 / 62500000) (-1713063821 / 1000000000) (Real.log (577 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99586067 / 200000000) ≤ -Real.log (640 / 1053) ∧
    -Real.log (640 / 1053) ≤ (15560323 / 31250000) := by
  have h := checkLog_sound (w := (413 / 1693)) (n := 12)
    (lo := (99586067 / 200000000)) (hi := (15560323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1053 / 640) = 1/(640 / 1053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99586067 / 200000000) (15560323 / 31250000) (Real.log (1053 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1053 / 640) = -Real.log (640 / 1053) := by
    rw [show ((1053 / 640) : ℝ) = ((640 / 1053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518259079 / 500000000) ≤ -Real.log (227 / 640) ∧
    -Real.log (227 / 640) ≤ (12956477 / 12500000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 227) = 1/(227 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12956477 / 12500000) (-518259079 / 500000000) (Real.log (227 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (494315071 / 1000000000) ≤ -Real.log (1600 / 2623) ∧
    -Real.log (1600 / 2623) ≤ (7723673 / 15625000) := by
  have h := checkLog_sound (w := (1023 / 4223)) (n := 12)
    (lo := (494315071 / 1000000000)) (hi := (7723673 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2623 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2623 / 1600) = 1/(1600 / 2623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (494315071 / 1000000000) (7723673 / 15625000) (Real.log (2623 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2623 / 1600) = -Real.log (1600 / 2623) := by
    rw [show ((2623 / 1600) : ℝ) = ((1600 / 2623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1019916641 / 1000000000) ≤ -Real.log (577 / 1600) ∧
    -Real.log (577 / 1600) ≤ (1019916643 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 577) = 1/(577 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1019916643 / 1000000000) (-1019916641 / 1000000000) (Real.log (577 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (313881217 / 500000000) ≤ -Real.log (500000 / 936707) ∧
    -Real.log (500000 / 936707) ≤ (125552487 / 200000000) := by
  have h := checkLog_sound (w := (436707 / 1436707)) (n := 12)
    (lo := (313881217 / 500000000)) (hi := (125552487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((936707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(936707 / 500000) = 1/(500000 / 936707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (313881217 / 500000000) (125552487 / 200000000) (Real.log (936707 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (936707 / 500000) = -Real.log (500000 / 936707) := by
    rw [show ((936707 / 500000) : ℝ) = ((500000 / 936707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1033416679 / 500000000) ≤ -Real.log (63293 / 500000) ∧
    -Real.log (63293 / 500000) ≤ (2066833361 / 1000000000) := by
  have h := checkLog_sound (w := (61707 / 188293)) (n := 12)
    (lo := (340269499 / 500000000)) (hi := (680538999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63293) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 63293) = 1/(63293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2066833361 / 1000000000) (-1033416679 / 500000000) (Real.log (63293 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (314328329 / 500000000) ≤ -Real.log (100000 / 187509) ∧
    -Real.log (100000 / 187509) ≤ (628656659 / 1000000000) := by
  have h := checkLog_sound (w := (87509 / 287509)) (n := 12)
    (lo := (314328329 / 500000000)) (hi := (628656659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187509 / 100000) = 1/(100000 / 187509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (314328329 / 500000000) (628656659 / 1000000000) (Real.log (187509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (187509 / 100000) = -Real.log (100000 / 187509) := by
    rw [show ((187509 / 100000) : ℝ) = ((100000 / 187509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2080161799 / 1000000000) ≤ -Real.log (12491 / 100000) ∧
    -Real.log (12491 / 100000) ≤ (2080161803 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 24991)) (n := 12)
    (lo := (720259 / 1000000000)) (hi := (36013 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12491) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 12491) = 1/(12491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2080161803 / 1000000000) (-2080161799 / 1000000000) (Real.log (12491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155659853 / 250000000) ≤ -Real.log (1000000 / 1863841) ∧
    -Real.log (1000000 / 1863841) ≤ (622639413 / 1000000000) := by
  have h := checkLog_sound (w := (863841 / 2863841)) (n := 12)
    (lo := (155659853 / 250000000)) (hi := (622639413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863841 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863841 / 1000000) = 1/(1000000 / 1863841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155659853 / 250000000) (622639413 / 1000000000) (Real.log (1863841 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1863841 / 1000000) = -Real.log (1000000 / 1863841) := by
    rw [show ((1863841 / 1000000) : ℝ) = ((1000000 / 1863841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1993931957 / 1000000000) ≤ -Real.log (136159 / 1000000) ∧
    -Real.log (136159 / 1000000) ≤ (49848299 / 25000000) := by
  have h := checkLog_sound (w := (113841 / 386159)) (n := 12)
    (lo := (607637597 / 1000000000)) (hi := (303818799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 136159) = 1/(136159 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-49848299 / 25000000) (-1993931957 / 1000000000) (Real.log (136159 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (311869611 / 500000000) ≤ -Real.log (250000 / 466473) ∧
    -Real.log (250000 / 466473) ≤ (623739223 / 1000000000) := by
  have h := checkLog_sound (w := (216473 / 716473)) (n := 12)
    (lo := (311869611 / 500000000)) (hi := (623739223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466473 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466473 / 250000) = 1/(250000 / 466473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (311869611 / 500000000) (623739223 / 1000000000) (Real.log (466473 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (466473 / 250000) = -Real.log (250000 / 466473) := by
    rw [show ((466473 / 250000) : ℝ) = ((250000 / 466473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (251138729 / 125000000) ≤ -Real.log (33527 / 250000) ∧
    -Real.log (33527 / 250000) ≤ (401821967 / 200000000) := by
  have h := checkLog_sound (w := (28973 / 96027)) (n := 12)
    (lo := (38925967 / 62500000)) (hi := (622815473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 33527) = 1/(33527 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-401821967 / 200000000) (-251138729 / 125000000) (Real.log (33527 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2694595793 / 1000000000) ≤ -Real.log (125000000000 / 1849941936707) ∧
    -Real.log (125000000000 / 1849941936707) ≤ (2694595797 / 1000000000) := by
  have h := checkLog_sound (w := (849941936707 / 2849941936707)) (n := 12)
    (lo := (615154253 / 1000000000)) (hi := (307577127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849941936707 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1849941936707 / 1000000000000) = 1/(125000000000 / 1849941936707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2694595793 / 1000000000) (2694595797 / 1000000000) (Real.log (1849941936707 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1849941936707 / 125000000000) = -Real.log (125000000000 / 1849941936707) := by
    rw [show ((1849941936707 / 125000000000) : ℝ) = ((125000000000 / 1849941936707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2708818457 / 1000000000) ≤ -Real.log (500000000000 / 7505764150189) ∧
    -Real.log (500000000000 / 7505764150189) ≤ (2708818461 / 1000000000) := by
  have h := checkLog_sound (w := (3505764150189 / 11505764150189)) (n := 12)
    (lo := (629376917 / 1000000000)) (hi := (314688459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7505764150189 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7505764150189 / 4000000000000) = 1/(500000000000 / 7505764150189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2708818457 / 1000000000) (2708818461 / 1000000000) (Real.log (7505764150189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7505764150189 / 500000000000) = -Real.log (500000000000 / 7505764150189) := by
    rw [show ((7505764150189 / 500000000000) : ℝ) = ((500000000000 / 7505764150189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2616571369 / 1000000000) ≤ -Real.log (31250000000 / 427772172607) ∧
    -Real.log (31250000000 / 427772172607) ≤ (2616571373 / 1000000000) := by
  have h := checkLog_sound (w := (177772172607 / 677772172607)) (n := 12)
    (lo := (537129829 / 1000000000)) (hi := (53712983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427772172607 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(427772172607 / 250000000000) = 1/(31250000000 / 427772172607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2616571369 / 1000000000) (2616571373 / 1000000000) (Real.log (427772172607 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (427772172607 / 31250000000) = -Real.log (31250000000 / 427772172607) := by
    rw [show ((427772172607 / 31250000000) : ℝ) = ((31250000000 / 427772172607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1316424527 / 500000000) ≤ -Real.log (20000000000 / 278267068333) ∧
    -Real.log (20000000000 / 278267068333) ≤ (1316424529 / 500000000) := by
  have h := checkLog_sound (w := (118267068333 / 438267068333)) (n := 12)
    (lo := (276703757 / 500000000)) (hi := (110681503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278267068333 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(278267068333 / 160000000000) = 1/(20000000000 / 278267068333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1316424527 / 500000000) (1316424529 / 500000000) (Real.log (278267068333 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (278267068333 / 20000000000) = -Real.log (20000000000 / 278267068333) := by
    rw [show ((278267068333 / 20000000000) : ℝ) = ((20000000000 / 278267068333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0196
