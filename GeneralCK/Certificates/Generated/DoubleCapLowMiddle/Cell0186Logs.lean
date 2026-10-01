import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0186
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

theorem reflection_log_1_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2401749 / 3906250) ≤ -Real.log (1600 / 2959) ∧
    -Real.log (1600 / 2959) ≤ (122969549 / 200000000) := by
  have h := checkLog_sound (w := (1359 / 4559)) (n := 12)
    (lo := (2401749 / 3906250)) (hi := (122969549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2959 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2959 / 1600) = 1/(1600 / 2959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2401749 / 3906250) (122969549 / 200000000) (Real.log (2959 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2959 / 1600) = -Real.log (1600 / 2959) := by
    rw [show ((2959 / 1600) : ℝ) = ((1600 / 2959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1892961973 / 1000000000) ≤ -Real.log (241 / 1600) ∧
    -Real.log (241 / 1600) ≤ (236620247 / 125000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 241) = 1/(241 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236620247 / 125000000) (-1892961973 / 1000000000) (Real.log (241 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (264946343 / 500000000) ≤ -Real.log (800 / 1359) ∧
    -Real.log (800 / 1359) ≤ (529892687 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 2159)) (n := 12)
    (lo := (264946343 / 500000000)) (hi := (529892687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 800) = 1/(800 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (264946343 / 500000000) (529892687 / 1000000000) (Real.log (1359 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1359 / 800) = -Real.log (800 / 1359) := by
    rw [show ((1359 / 800) : ℝ) = ((800 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1199814793 / 1000000000) ≤ -Real.log (241 / 800) ∧
    -Real.log (241 / 800) ≤ (239962959 / 200000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 241) = 1/(241 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-239962959 / 200000000) (-1199814793 / 1000000000) (Real.log (241 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (636980451 / 1000000000) ≤ -Real.log (1000000 / 1890763) ∧
    -Real.log (1000000 / 1890763) ≤ (159245113 / 250000000) := by
  have h := checkLog_sound (w := (890763 / 2890763)) (n := 12)
    (lo := (636980451 / 1000000000)) (hi := (159245113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1890763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1890763 / 1000000) = 1/(1000000 / 1890763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (636980451 / 1000000000) (159245113 / 250000000) (Real.log (1890763 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1890763 / 1000000) = -Real.log (1000000 / 1890763) := by
    rw [show ((1890763 / 1000000) : ℝ) = ((1000000 / 1890763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2214235443 / 1000000000) ≤ -Real.log (109237 / 1000000) ∧
    -Real.log (109237 / 1000000) ≤ (2214235447 / 1000000000) := by
  have h := checkLog_sound (w := (15763 / 234237)) (n := 12)
    (lo := (134793903 / 1000000000)) (hi := (8424619 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109237) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 109237) = 1/(109237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2214235447 / 1000000000) (-2214235443 / 1000000000) (Real.log (109237 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318968111 / 500000000) ≤ -Real.log (1000000 / 1892571) ∧
    -Real.log (1000000 / 1892571) ≤ (637936223 / 1000000000) := by
  have h := checkLog_sound (w := (892571 / 2892571)) (n := 12)
    (lo := (318968111 / 500000000)) (hi := (637936223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1892571 / 1000000) = 1/(1000000 / 1892571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318968111 / 500000000) (637936223 / 1000000000) (Real.log (1892571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1892571 / 1000000) = -Real.log (1000000 / 1892571) := by
    rw [show ((1892571 / 1000000) : ℝ) = ((1000000 / 1892571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2230925113 / 1000000000) ≤ -Real.log (107429 / 1000000) ∧
    -Real.log (107429 / 1000000) ≤ (2230925117 / 1000000000) := by
  have h := checkLog_sound (w := (17571 / 232429)) (n := 12)
    (lo := (151483573 / 1000000000)) (hi := (75741787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 107429) = 1/(107429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2230925117 / 1000000000) (-2230925113 / 1000000000) (Real.log (107429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (633685881 / 1000000000) ≤ -Real.log (15625 / 29446) ∧
    -Real.log (15625 / 29446) ≤ (316842941 / 500000000) := by
  have h := checkLog_sound (w := (13821 / 45071)) (n := 12)
    (lo := (633685881 / 1000000000)) (hi := (316842941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29446 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29446 / 15625) = 1/(15625 / 29446) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (633685881 / 1000000000) (316842941 / 500000000) (Real.log (29446 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (29446 / 15625) = -Real.log (15625 / 29446) := by
    rw [show ((29446 / 15625) : ℝ) = ((15625 / 29446) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (539716443 / 250000000) ≤ -Real.log (1804 / 15625) ∧
    -Real.log (1804 / 15625) ≤ (134929111 / 62500000) := by
  have h := checkLog_sound (w := (1193 / 30057)) (n := 12)
    (lo := (9928029 / 125000000)) (hi := (79424233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14432) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 14432) = 1/(1804 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-134929111 / 62500000) (-539716443 / 250000000) (Real.log (1804 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (634797469 / 1000000000) ≤ -Real.log (12500 / 23583) ∧
    -Real.log (12500 / 23583) ≤ (63479747 / 100000000) := by
  have h := checkLog_sound (w := (11083 / 36083)) (n := 12)
    (lo := (634797469 / 1000000000)) (hi := (63479747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23583 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23583 / 12500) = 1/(12500 / 23583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (634797469 / 1000000000) (63479747 / 100000000) (Real.log (23583 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (23583 / 12500) = -Real.log (12500 / 23583) := by
    rw [show ((23583 / 12500) : ℝ) = ((12500 / 23583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2177186681 / 1000000000) ≤ -Real.log (1417 / 12500) ∧
    -Real.log (1417 / 12500) ≤ (435437337 / 200000000) := by
  have h := checkLog_sound (w := (291 / 5959)) (n := 12)
    (lo := (97745141 / 1000000000)) (hi := (48872571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2834) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2834) = 1/(1417 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-435437337 / 200000000) (-2177186681 / 1000000000) (Real.log (1417 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1425607947 / 500000000) ≤ -Real.log (500000000000 / 8654407389437) ∧
    -Real.log (500000000000 / 8654407389437) ≤ (2851215899 / 1000000000) := by
  have h := checkLog_sound (w := (654407389437 / 16654407389437)) (n := 12)
    (lo := (39313587 / 500000000)) (hi := (3145087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8654407389437 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8654407389437 / 8000000000000) = 1/(500000000000 / 8654407389437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1425607947 / 500000000) (2851215899 / 1000000000) (Real.log (8654407389437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8654407389437 / 500000000000) = -Real.log (500000000000 / 8654407389437) := by
    rw [show ((8654407389437 / 500000000000) : ℝ) = ((500000000000 / 8654407389437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1434430667 / 500000000) ≤ -Real.log (500000000000 / 8808473503431) ∧
    -Real.log (500000000000 / 8808473503431) ≤ (2868861339 / 1000000000) := by
  have h := checkLog_sound (w := (808473503431 / 16808473503431)) (n := 12)
    (lo := (48136307 / 500000000)) (hi := (19254523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8808473503431 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8808473503431 / 8000000000000) = 1/(500000000000 / 8808473503431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1434430667 / 500000000) (2868861339 / 1000000000) (Real.log (8808473503431 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8808473503431 / 500000000000) = -Real.log (500000000000 / 8808473503431) := by
    rw [show ((8808473503431 / 500000000000) : ℝ) = ((500000000000 / 8808473503431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2792551653 / 1000000000) ≤ -Real.log (500000000000 / 8161308203991) ∧
    -Real.log (500000000000 / 8161308203991) ≤ (1396275829 / 500000000) := by
  have h := checkLog_sound (w := (161308203991 / 16161308203991)) (n := 12)
    (lo := (19962933 / 1000000000)) (hi := (9981467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8161308203991 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8161308203991 / 8000000000000) = 1/(500000000000 / 8161308203991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2792551653 / 1000000000) (1396275829 / 500000000) (Real.log (8161308203991 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8161308203991 / 500000000000) = -Real.log (500000000000 / 8161308203991) := by
    rw [show ((8161308203991 / 500000000000) : ℝ) = ((500000000000 / 8161308203991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (56239683 / 20000000) ≤ -Real.log (500000000000 / 8321453775583) ∧
    -Real.log (500000000000 / 8321453775583) ≤ (562396831 / 200000000) := by
  have h := checkLog_sound (w := (321453775583 / 16321453775583)) (n := 12)
    (lo := (3939543 / 100000000)) (hi := (39395431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8321453775583 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8321453775583 / 8000000000000) = 1/(500000000000 / 8321453775583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (56239683 / 20000000) (562396831 / 200000000) (Real.log (8321453775583 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8321453775583 / 500000000000) = -Real.log (500000000000 / 8321453775583) := by
    rw [show ((8321453775583 / 500000000000) : ℝ) = ((500000000000 / 8321453775583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0186
