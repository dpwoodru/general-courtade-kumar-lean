import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell234
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (163822161 / 500000000) ≤ -Real.log (1024 / 1421) ∧
    -Real.log (1024 / 1421) ≤ (327644323 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2445)) (n := 12)
    (lo := (163822161 / 500000000)) (hi := (327644323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1024) = 1/(1024 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (163822161 / 500000000) (327644323 / 1000000000) (Real.log (1421 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1421 / 1024) = -Real.log (1024 / 1421) := by
    rw [show ((1421 / 1024) : ℝ) = ((1024 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30657829 / 62500000) ≤ -Real.log (627 / 1024) ∧
    -Real.log (627 / 1024) ≤ (98105053 / 200000000) := by
  have h := checkLog_sound (w := (397 / 1651)) (n := 12)
    (lo := (30657829 / 62500000)) (hi := (98105053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 627) = 1/(627 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-98105053 / 200000000) (-30657829 / 62500000) (Real.log (627 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65444399 / 200000000) ≤ -Real.log (2560 / 3551) ∧
    -Real.log (2560 / 3551) ≤ (81805499 / 250000000) := by
  have h := checkLog_sound (w := (991 / 6111)) (n := 12)
    (lo := (65444399 / 200000000)) (hi := (81805499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3551 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3551 / 2560) = 1/(2560 / 3551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65444399 / 200000000) (81805499 / 250000000) (Real.log (3551 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3551 / 2560) = -Real.log (2560 / 3551) := by
    rw [show ((3551 / 2560) : ℝ) = ((2560 / 3551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30598049 / 62500000) ≤ -Real.log (1569 / 2560) ∧
    -Real.log (1569 / 2560) ≤ (97913757 / 200000000) := by
  have h := checkLog_sound (w := (991 / 4129)) (n := 12)
    (lo := (30598049 / 62500000)) (hi := (97913757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1569) = 1/(1569 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-97913757 / 200000000) (-30598049 / 62500000) (Real.log (1569 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121689513 / 500000000) ≤ -Real.log (31250 / 39861) ∧
    -Real.log (31250 / 39861) ≤ (243379027 / 1000000000) := by
  have h := checkLog_sound (w := (8611 / 71111)) (n := 12)
    (lo := (121689513 / 500000000)) (hi := (243379027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39861 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39861 / 31250) = 1/(31250 / 39861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121689513 / 500000000) (243379027 / 1000000000) (Real.log (39861 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (39861 / 31250) = -Real.log (31250 / 39861) := by
    rw [show ((39861 / 31250) : ℝ) = ((31250 / 39861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (322345293 / 1000000000) ≤ -Real.log (22639 / 31250) ∧
    -Real.log (22639 / 31250) ≤ (161172647 / 500000000) := by
  have h := checkLog_sound (w := (8611 / 53889)) (n := 12)
    (lo := (322345293 / 1000000000)) (hi := (161172647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22639) = 1/(22639 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-161172647 / 500000000) (-322345293 / 1000000000) (Real.log (22639 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1949691 / 8000000) ≤ -Real.log (125000 / 159497) ∧
    -Real.log (125000 / 159497) ≤ (15231961 / 62500000) := by
  have h := checkLog_sound (w := (34497 / 284497)) (n := 12)
    (lo := (1949691 / 8000000)) (hi := (15231961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159497 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159497 / 125000) = 1/(125000 / 159497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1949691 / 8000000) (15231961 / 62500000) (Real.log (159497 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (159497 / 125000) = -Real.log (125000 / 159497) := by
    rw [show ((159497 / 125000) : ℝ) = ((125000 / 159497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (322930737 / 1000000000) ≤ -Real.log (90503 / 125000) ∧
    -Real.log (90503 / 125000) ≤ (161465369 / 500000000) := by
  have h := checkLog_sound (w := (34497 / 215503)) (n := 12)
    (lo := (322930737 / 1000000000)) (hi := (161465369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90503) = 1/(90503 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-161465369 / 500000000) (-322930737 / 1000000000) (Real.log (90503 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2836139 / 15625000) ≤ -Real.log (100000 / 119903) ∧
    -Real.log (100000 / 119903) ≤ (181512897 / 1000000000) := by
  have h := checkLog_sound (w := (19903 / 219903)) (n := 12)
    (lo := (2836139 / 15625000)) (hi := (181512897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119903 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119903 / 100000) = 1/(100000 / 119903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2836139 / 15625000) (181512897 / 1000000000) (Real.log (119903 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119903 / 100000) = -Real.log (100000 / 119903) := by
    rw [show ((119903 / 100000) : ℝ) = ((100000 / 119903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44386357 / 200000000) ≤ -Real.log (80097 / 100000) ∧
    -Real.log (80097 / 100000) ≤ (110965893 / 500000000) := by
  have h := checkLog_sound (w := (19903 / 180097)) (n := 12)
    (lo := (44386357 / 200000000)) (hi := (110965893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80097) = 1/(80097 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110965893 / 500000000) (-44386357 / 200000000) (Real.log (80097 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (181778909 / 1000000000) ≤ -Real.log (1000000 / 1199349) ∧
    -Real.log (1000000 / 1199349) ≤ (18177891 / 100000000) := by
  have h := checkLog_sound (w := (199349 / 2199349)) (n := 12)
    (lo := (181778909 / 1000000000)) (hi := (18177891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199349 / 1000000) = 1/(1000000 / 1199349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (181778909 / 1000000000) (18177891 / 100000000) (Real.log (1199349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1199349 / 1000000) = -Real.log (1000000 / 1199349) := by
    rw [show ((1199349 / 1000000) : ℝ) = ((1000000 / 1199349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (55582533 / 250000000) ≤ -Real.log (800651 / 1000000) ∧
    -Real.log (800651 / 1000000) ≤ (222330133 / 1000000000) := by
  have h := checkLog_sound (w := (199349 / 1800651)) (n := 12)
    (lo := (55582533 / 250000000)) (hi := (222330133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800651) = 1/(800651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-222330133 / 1000000000) (-55582533 / 250000000) (Real.log (800651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (816790779 / 1000000000) ≤ -Real.log (500000000000 / 1131612492033) ∧
    -Real.log (500000000000 / 1131612492033) ≤ (816790781 / 1000000000) := by
  have h := checkLog_sound (w := (131612492033 / 2131612492033)) (n := 12)
    (lo := (123643599 / 1000000000)) (hi := (309109 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131612492033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131612492033 / 1000000000000) = 1/(500000000000 / 1131612492033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (816790779 / 1000000000) (816790781 / 1000000000) (Real.log (1131612492033 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1131612492033 / 500000000000) = -Real.log (500000000000 / 1131612492033) := by
    rw [show ((1131612492033 / 500000000000) : ℝ) = ((500000000000 / 1131612492033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (409084793 / 500000000) ≤ -Real.log (500000000000 / 1133173843701) ∧
    -Real.log (500000000000 / 1133173843701) ≤ (204542397 / 250000000) := by
  have h := checkLog_sound (w := (133173843701 / 2133173843701)) (n := 12)
    (lo := (62511203 / 500000000)) (hi := (125022407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133173843701 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1133173843701 / 1000000000000) = 1/(500000000000 / 1133173843701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (409084793 / 500000000) (204542397 / 250000000) (Real.log (1133173843701 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1133173843701 / 500000000000) = -Real.log (500000000000 / 1133173843701) := by
    rw [show ((1133173843701 / 500000000000) : ℝ) = ((500000000000 / 1133173843701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (565724319 / 1000000000) ≤ -Real.log (25000000000 / 44018066169) ∧
    -Real.log (25000000000 / 44018066169) ≤ (3535777 / 6250000) := by
  have h := checkLog_sound (w := (19018066169 / 69018066169)) (n := 12)
    (lo := (565724319 / 1000000000)) (hi := (3535777 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44018066169 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44018066169 / 25000000000) = 1/(25000000000 / 44018066169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (565724319 / 1000000000) (3535777 / 6250000) (Real.log (44018066169 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (44018066169 / 25000000000) = -Real.log (25000000000 / 44018066169) := by
    rw [show ((44018066169 / 25000000000) : ℝ) = ((25000000000 / 44018066169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (566642113 / 1000000000) ≤ -Real.log (500000000000 / 881169684983) ∧
    -Real.log (500000000000 / 881169684983) ≤ (283321057 / 500000000) := by
  have h := checkLog_sound (w := (381169684983 / 1381169684983)) (n := 12)
    (lo := (566642113 / 1000000000)) (hi := (283321057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881169684983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881169684983 / 500000000000) = 1/(500000000000 / 881169684983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (566642113 / 1000000000) (283321057 / 500000000) (Real.log (881169684983 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (881169684983 / 500000000000) = -Real.log (500000000000 / 881169684983) := by
    rw [show ((881169684983 / 500000000000) : ℝ) = ((500000000000 / 881169684983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (201722341 / 500000000) ≤ -Real.log (500000000000 / 748486210469) ∧
    -Real.log (500000000000 / 748486210469) ≤ (403444683 / 1000000000) := by
  have h := checkLog_sound (w := (248486210469 / 1248486210469)) (n := 12)
    (lo := (201722341 / 500000000)) (hi := (403444683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748486210469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748486210469 / 500000000000) = 1/(500000000000 / 748486210469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (201722341 / 500000000) (403444683 / 1000000000) (Real.log (748486210469 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (748486210469 / 500000000000) = -Real.log (500000000000 / 748486210469) := by
    rw [show ((748486210469 / 500000000000) : ℝ) = ((500000000000 / 748486210469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404109041 / 1000000000) ≤ -Real.log (125000000000 / 187245909891) ∧
    -Real.log (125000000000 / 187245909891) ≤ (202054521 / 500000000) := by
  have h := checkLog_sound (w := (62245909891 / 312245909891)) (n := 12)
    (lo := (404109041 / 1000000000)) (hi := (202054521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187245909891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187245909891 / 125000000000) = 1/(125000000000 / 187245909891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404109041 / 1000000000) (202054521 / 500000000) (Real.log (187245909891 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (187245909891 / 125000000000) = -Real.log (125000000000 / 187245909891) := by
    rw [show ((187245909891 / 125000000000) : ℝ) = ((125000000000 / 187245909891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20275611 / 500000000) ≤ -Real.log (960259976199 / 1000000000000) ∧
    -Real.log (960259976199 / 1000000000000) ≤ (40551223 / 1000000000) := by
  have h := checkLog_sound (w := (39740023801 / 1960259976199)) (n := 12)
    (lo := (20275611 / 500000000)) (hi := (40551223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960259976199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960259976199) = 1/(960259976199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40551223 / 1000000000) (-20275611 / 500000000) (Real.log (960259976199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40418889 / 1000000000) ≤ -Real.log (9603870591 / 10000000000) ∧
    -Real.log (9603870591 / 10000000000) ≤ (4041889 / 100000000) := by
  have h := checkLog_sound (w := (396129409 / 19603870591)) (n := 12)
    (lo := (40418889 / 1000000000)) (hi := (4041889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9603870591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9603870591) = 1/(9603870591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4041889 / 100000000) (-40418889 / 1000000000) (Real.log (9603870591 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell234
