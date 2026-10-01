import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0355
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

theorem reflection_log_1_neg : (10548013 / 50000000) ≤ -Real.log (2048 / 2529) ∧
    -Real.log (2048 / 2529) ≤ (210960261 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4577)) (n := 12)
    (lo := (10548013 / 50000000)) (hi := (210960261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2529 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2529 / 2048) = 1/(2048 / 2529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10548013 / 50000000) (210960261 / 1000000000) (Real.log (2529 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2529 / 2048) = -Real.log (2048 / 2529) := by
    rw [show ((2529 / 2048) : ℝ) = ((2048 / 2529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (267700743 / 1000000000) ≤ -Real.log (1567 / 2048) ∧
    -Real.log (1567 / 2048) ≤ (33462593 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3615)) (n := 12)
    (lo := (267700743 / 1000000000)) (hi := (33462593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1567) = 1/(1567 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33462593 / 125000000) (-267700743 / 1000000000) (Real.log (1567 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26340373 / 125000000) ≤ -Real.log (5120 / 6321) ∧
    -Real.log (5120 / 6321) ≤ (42144597 / 200000000) := by
  have h := checkLog_sound (w := (1201 / 11441)) (n := 12)
    (lo := (26340373 / 125000000)) (hi := (42144597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6321 / 5120) = 1/(5120 / 6321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26340373 / 125000000) (42144597 / 200000000) (Real.log (6321 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6321 / 5120) = -Real.log (5120 / 6321) := by
    rw [show ((6321 / 5120) : ℝ) = ((5120 / 6321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (267317919 / 1000000000) ≤ -Real.log (3919 / 5120) ∧
    -Real.log (3919 / 5120) ≤ (1670737 / 6250000) := by
  have h := checkLog_sound (w := (1201 / 9039)) (n := 12)
    (lo := (267317919 / 1000000000)) (hi := (1670737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3919) = 1/(3919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1670737 / 6250000) (-267317919 / 1000000000) (Real.log (3919 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (385076371 / 1000000000) ≤ -Real.log (1024 / 1505) ∧
    -Real.log (1024 / 1505) ≤ (96269093 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2529)) (n := 12)
    (lo := (385076371 / 1000000000)) (hi := (96269093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1505 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1505 / 1024) = 1/(1024 / 1505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (385076371 / 1000000000) (96269093 / 250000000) (Real.log (1505 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1505 / 1024) = -Real.log (1024 / 1505) := by
    rw [show ((1505 / 1024) : ℝ) = ((1024 / 1505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126872497 / 200000000) ≤ -Real.log (543 / 1024) ∧
    -Real.log (543 / 1024) ≤ (317181243 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1567)) (n := 12)
    (lo := (126872497 / 200000000)) (hi := (317181243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 543) = 1/(543 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317181243 / 500000000) (-126872497 / 200000000) (Real.log (543 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19233881 / 50000000) ≤ -Real.log (2560 / 3761) ∧
    -Real.log (2560 / 3761) ≤ (384677621 / 1000000000) := by
  have h := checkLog_sound (w := (1201 / 6321)) (n := 12)
    (lo := (19233881 / 50000000)) (hi := (384677621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3761 / 2560) = 1/(2560 / 3761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19233881 / 50000000) (384677621 / 1000000000) (Real.log (3761 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3761 / 2560) = -Real.log (2560 / 3761) := by
    rw [show ((3761 / 2560) : ℝ) = ((2560 / 3761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (633258123 / 1000000000) ≤ -Real.log (1359 / 2560) ∧
    -Real.log (1359 / 2560) ≤ (158314531 / 250000000) := by
  have h := checkLog_sound (w := (1201 / 3919)) (n := 12)
    (lo := (633258123 / 1000000000)) (hi := (158314531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1359) = 1/(1359 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-158314531 / 250000000) (-633258123 / 1000000000) (Real.log (1359 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57799741 / 200000000) ≤ -Real.log (100000 / 133509) ∧
    -Real.log (100000 / 133509) ≤ (144499353 / 500000000) := by
  have h := checkLog_sound (w := (33509 / 233509)) (n := 12)
    (lo := (57799741 / 200000000)) (hi := (144499353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133509 / 100000) = 1/(100000 / 133509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57799741 / 200000000) (144499353 / 500000000) (Real.log (133509 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (133509 / 100000) = -Real.log (100000 / 133509) := by
    rw [show ((133509 / 100000) : ℝ) = ((100000 / 133509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81620717 / 200000000) ≤ -Real.log (66491 / 100000) ∧
    -Real.log (66491 / 100000) ≤ (204051793 / 500000000) := by
  have h := checkLog_sound (w := (33509 / 166491)) (n := 12)
    (lo := (81620717 / 200000000)) (hi := (204051793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66491) = 1/(66491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-204051793 / 500000000) (-81620717 / 200000000) (Real.log (66491 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14465999 / 50000000) ≤ -Real.log (1000000 / 1335519) ∧
    -Real.log (1000000 / 1335519) ≤ (289319981 / 1000000000) := by
  have h := checkLog_sound (w := (335519 / 2335519)) (n := 12)
    (lo := (14465999 / 50000000)) (hi := (289319981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335519 / 1000000) = 1/(1000000 / 1335519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14465999 / 50000000) (289319981 / 1000000000) (Real.log (1335519 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1335519 / 1000000) = -Real.log (1000000 / 1335519) := by
    rw [show ((1335519 / 1000000) : ℝ) = ((1000000 / 1335519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (204374497 / 500000000) ≤ -Real.log (664481 / 1000000) ∧
    -Real.log (664481 / 1000000) ≤ (81749799 / 200000000) := by
  have h := checkLog_sound (w := (335519 / 1664481)) (n := 12)
    (lo := (204374497 / 500000000)) (hi := (81749799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 664481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 664481) = 1/(664481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-81749799 / 200000000) (-204374497 / 500000000) (Real.log (664481 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109384197 / 500000000) ≤ -Real.log (1000000 / 1244543) ∧
    -Real.log (1000000 / 1244543) ≤ (43753679 / 200000000) := by
  have h := checkLog_sound (w := (244543 / 2244543)) (n := 12)
    (lo := (109384197 / 500000000)) (hi := (43753679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244543 / 1000000) = 1/(1000000 / 1244543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109384197 / 500000000) (43753679 / 200000000) (Real.log (1244543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1244543 / 1000000) = -Real.log (1000000 / 1244543) := by
    rw [show ((1244543 / 1000000) : ℝ) = ((1000000 / 1244543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (140216207 / 500000000) ≤ -Real.log (755457 / 1000000) ∧
    -Real.log (755457 / 1000000) ≤ (56086483 / 200000000) := by
  have h := checkLog_sound (w := (244543 / 1755457)) (n := 12)
    (lo := (140216207 / 500000000)) (hi := (56086483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755457) = 1/(755457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56086483 / 200000000) (-140216207 / 500000000) (Real.log (755457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219036729 / 1000000000) ≤ -Real.log (1000000 / 1244877) ∧
    -Real.log (1000000 / 1244877) ≤ (21903673 / 100000000) := by
  have h := checkLog_sound (w := (244877 / 2244877)) (n := 12)
    (lo := (219036729 / 1000000000)) (hi := (21903673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244877 / 1000000) = 1/(1000000 / 1244877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219036729 / 1000000000) (21903673 / 100000000) (Real.log (1244877 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1244877 / 1000000) = -Real.log (1000000 / 1244877) := by
    rw [show ((1244877 / 1000000) : ℝ) = ((1000000 / 1244877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (280874629 / 1000000000) ≤ -Real.log (755123 / 1000000) ∧
    -Real.log (755123 / 1000000) ≤ (28087463 / 100000000) := by
  have h := checkLog_sound (w := (244877 / 1755123)) (n := 12)
    (lo := (280874629 / 1000000000)) (hi := (28087463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755123) = 1/(755123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28087463 / 100000000) (-280874629 / 1000000000) (Real.log (755123 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (69710229 / 100000000) ≤ -Real.log (500000000000 / 1003962942353) ∧
    -Real.log (500000000000 / 1003962942353) ≤ (174275573 / 250000000) := by
  have h := checkLog_sound (w := (3962942353 / 2003962942353)) (n := 12)
    (lo := (395511 / 100000000)) (hi := (3955111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003962942353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003962942353 / 1000000000000) = 1/(500000000000 / 1003962942353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (69710229 / 100000000) (174275573 / 250000000) (Real.log (1003962942353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1003962942353 / 500000000000) = -Real.log (500000000000 / 1003962942353) := by
    rw [show ((1003962942353 / 500000000000) : ℝ) = ((500000000000 / 1003962942353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (698068973 / 1000000000) ≤ -Real.log (125000000000 / 251233481469) ∧
    -Real.log (125000000000 / 251233481469) ≤ (27922759 / 40000000) := by
  have h := checkLog_sound (w := (1233481469 / 501233481469)) (n := 12)
    (lo := (4921793 / 1000000000)) (hi := (2460897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251233481469 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(251233481469 / 250000000000) = 1/(125000000000 / 251233481469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (698068973 / 1000000000) (27922759 / 40000000) (Real.log (251233481469 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (251233481469 / 125000000000) = -Real.log (125000000000 / 251233481469) := by
    rw [show ((251233481469 / 125000000000) : ℝ) = ((125000000000 / 251233481469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (499200809 / 1000000000) ≤ -Real.log (25000000000 / 41185103851) ∧
    -Real.log (25000000000 / 41185103851) ≤ (49920081 / 100000000) := by
  have h := checkLog_sound (w := (16185103851 / 66185103851)) (n := 12)
    (lo := (499200809 / 1000000000)) (hi := (49920081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41185103851 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41185103851 / 25000000000) = 1/(25000000000 / 41185103851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (499200809 / 1000000000) (49920081 / 100000000) (Real.log (41185103851 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (41185103851 / 25000000000) = -Real.log (25000000000 / 41185103851) := by
    rw [show ((41185103851 / 25000000000) : ℝ) = ((25000000000 / 41185103851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (249955679 / 500000000) ≤ -Real.log (500000000000 / 824287566397) ∧
    -Real.log (500000000000 / 824287566397) ≤ (499911359 / 1000000000) := by
  have h := checkLog_sound (w := (324287566397 / 1324287566397)) (n := 12)
    (lo := (249955679 / 500000000)) (hi := (499911359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824287566397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824287566397 / 500000000000) = 1/(500000000000 / 824287566397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (249955679 / 500000000) (499911359 / 1000000000) (Real.log (824287566397 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (824287566397 / 500000000000) = -Real.log (500000000000 / 824287566397) := by
    rw [show ((824287566397 / 500000000000) : ℝ) = ((500000000000 / 824287566397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0355
