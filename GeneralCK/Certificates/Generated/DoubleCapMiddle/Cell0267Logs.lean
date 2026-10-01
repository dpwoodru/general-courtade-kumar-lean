import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0267
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

theorem reflection_log_1_neg : (235103001 / 1000000000) ≤ -Real.log (5120 / 6477) ∧
    -Real.log (5120 / 6477) ≤ (117551501 / 500000000) := by
  have h := checkLog_sound (w := (1357 / 11597)) (n := 12)
    (lo := (235103001 / 1000000000)) (hi := (117551501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6477 / 5120) = 1/(5120 / 6477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (235103001 / 1000000000) (117551501 / 500000000) (Real.log (6477 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6477 / 5120) = -Real.log (5120 / 6477) := by
    rw [show ((6477 / 5120) : ℝ) = ((5120 / 6477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307937927 / 1000000000) ≤ -Real.log (3763 / 5120) ∧
    -Real.log (3763 / 5120) ≤ (38492241 / 125000000) := by
  have h := checkLog_sound (w := (1357 / 8883)) (n := 12)
    (lo := (307937927 / 1000000000)) (hi := (38492241 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3763) = 1/(3763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-38492241 / 125000000) (-307937927 / 1000000000) (Real.log (3763 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58659929 / 250000000) ≤ -Real.log (2560 / 3237) ∧
    -Real.log (2560 / 3237) ≤ (234639717 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 5797)) (n := 12)
    (lo := (58659929 / 250000000)) (hi := (234639717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3237 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3237 / 2560) = 1/(2560 / 3237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58659929 / 250000000) (234639717 / 1000000000) (Real.log (3237 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3237 / 2560) = -Real.log (2560 / 3237) := by
    rw [show ((3237 / 2560) : ℝ) = ((2560 / 3237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19196313 / 62500000) ≤ -Real.log (1883 / 2560) ∧
    -Real.log (1883 / 2560) ≤ (307141009 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 4443)) (n := 12)
    (lo := (19196313 / 62500000)) (hi := (307141009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1883) = 1/(1883 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-307141009 / 1000000000) (-19196313 / 62500000) (Real.log (1883 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106329699 / 250000000) ≤ -Real.log (2560 / 3917) ∧
    -Real.log (2560 / 3917) ≤ (425318797 / 1000000000) := by
  have h := checkLog_sound (w := (1357 / 6477)) (n := 12)
    (lo := (106329699 / 250000000)) (hi := (425318797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3917 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3917 / 2560) = 1/(2560 / 3917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106329699 / 250000000) (425318797 / 1000000000) (Real.log (3917 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3917 / 2560) = -Real.log (2560 / 3917) := by
    rw [show ((3917 / 2560) : ℝ) = ((2560 / 3917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (37759441 / 50000000) ≤ -Real.log (1203 / 2560) ∧
    -Real.log (1203 / 2560) ≤ (377594411 / 500000000) := by
  have h := checkLog_sound (w := (77 / 2483)) (n := 12)
    (lo := (1551041 / 25000000)) (hi := (62041641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1203) = 1/(1203 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-377594411 / 500000000) (-37759441 / 50000000) (Real.log (1203 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42455261 / 100000000) ≤ -Real.log (1280 / 1957) ∧
    -Real.log (1280 / 1957) ≤ (424552611 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 3237)) (n := 12)
    (lo := (42455261 / 100000000)) (hi := (424552611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1280) = 1/(1280 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42455261 / 100000000) (424552611 / 1000000000) (Real.log (1957 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1957 / 1280) = -Real.log (1280 / 1957) := by
    rw [show ((1957 / 1280) : ℝ) = ((1280 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (752698159 / 1000000000) ≤ -Real.log (603 / 1280) ∧
    -Real.log (603 / 1280) ≤ (752698161 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 1243)) (n := 12)
    (lo := (59550979 / 1000000000)) (hi := (2977549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 603) = 1/(603 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-752698161 / 1000000000) (-752698159 / 1000000000) (Real.log (603 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (321322339 / 1000000000) ≤ -Real.log (20000 / 27579) ∧
    -Real.log (20000 / 27579) ≤ (16066117 / 50000000) := by
  have h := checkLog_sound (w := (7579 / 47579)) (n := 12)
    (lo := (321322339 / 1000000000)) (hi := (16066117 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27579 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27579 / 20000) = 1/(20000 / 27579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (321322339 / 1000000000) (16066117 / 50000000) (Real.log (27579 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27579 / 20000) = -Real.log (20000 / 27579) := by
    rw [show ((27579 / 20000) : ℝ) = ((20000 / 27579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (119085921 / 250000000) ≤ -Real.log (12421 / 20000) ∧
    -Real.log (12421 / 20000) ≤ (95268737 / 200000000) := by
  have h := checkLog_sound (w := (7579 / 32421)) (n := 12)
    (lo := (119085921 / 250000000)) (hi := (95268737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12421) = 1/(12421 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95268737 / 200000000) (-119085921 / 250000000) (Real.log (12421 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (80487539 / 250000000) ≤ -Real.log (125000 / 172477) ∧
    -Real.log (125000 / 172477) ≤ (321950157 / 1000000000) := by
  have h := checkLog_sound (w := (47477 / 297477)) (n := 12)
    (lo := (80487539 / 250000000)) (hi := (321950157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172477 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172477 / 125000) = 1/(125000 / 172477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (80487539 / 250000000) (321950157 / 1000000000) (Real.log (172477 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (172477 / 125000) = -Real.log (125000 / 172477) := by
    rw [show ((172477 / 125000) : ℝ) = ((125000 / 172477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (47773907 / 100000000) ≤ -Real.log (77523 / 125000) ∧
    -Real.log (77523 / 125000) ≤ (477739071 / 1000000000) := by
  have h := checkLog_sound (w := (47477 / 202523)) (n := 12)
    (lo := (47773907 / 100000000)) (hi := (477739071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 77523) = 1/(77523 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-477739071 / 1000000000) (-47773907 / 100000000) (Real.log (77523 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (61527449 / 250000000) ≤ -Real.log (3125 / 3997) ∧
    -Real.log (3125 / 3997) ≤ (246109797 / 1000000000) := by
  have h := checkLog_sound (w := (436 / 3561)) (n := 12)
    (lo := (61527449 / 250000000)) (hi := (246109797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3997 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3997 / 3125) = 1/(3125 / 3997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (61527449 / 250000000) (246109797 / 1000000000) (Real.log (3997 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3997 / 3125) = -Real.log (3125 / 3997) := by
    rw [show ((3997 / 3125) : ℝ) = ((3125 / 3997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (327171621 / 1000000000) ≤ -Real.log (2253 / 3125) ∧
    -Real.log (2253 / 3125) ≤ (163585811 / 500000000) := by
  have h := checkLog_sound (w := (436 / 2689)) (n := 12)
    (lo := (327171621 / 1000000000)) (hi := (163585811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2253) = 1/(2253 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-163585811 / 500000000) (-327171621 / 1000000000) (Real.log (2253 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (246649899 / 1000000000) ≤ -Real.log (1000000 / 1279731) ∧
    -Real.log (1000000 / 1279731) ≤ (2466499 / 10000000) := by
  have h := checkLog_sound (w := (279731 / 2279731)) (n := 12)
    (lo := (246649899 / 1000000000)) (hi := (2466499 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279731 / 1000000) = 1/(1000000 / 1279731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (246649899 / 1000000000) (2466499 / 10000000) (Real.log (1279731 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1279731 / 1000000) = -Real.log (1000000 / 1279731) := by
    rw [show ((1279731 / 1000000) : ℝ) = ((1000000 / 1279731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (13125221 / 40000000) ≤ -Real.log (720269 / 1000000) ∧
    -Real.log (720269 / 1000000) ≤ (164065263 / 500000000) := by
  have h := checkLog_sound (w := (279731 / 1720269)) (n := 12)
    (lo := (13125221 / 40000000)) (hi := (164065263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720269) = 1/(720269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-164065263 / 500000000) (-13125221 / 40000000) (Real.log (720269 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (99708253 / 125000000) ≤ -Real.log (250000000000 / 555088157153) ∧
    -Real.log (250000000000 / 555088157153) ≤ (398833013 / 500000000) := by
  have h := checkLog_sound (w := (55088157153 / 1055088157153)) (n := 12)
    (lo := (26129711 / 250000000)) (hi := (20903769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555088157153 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555088157153 / 500000000000) = 1/(250000000000 / 555088157153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (99708253 / 125000000) (398833013 / 500000000) (Real.log (555088157153 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (555088157153 / 250000000000) = -Real.log (250000000000 / 555088157153) := by
    rw [show ((555088157153 / 250000000000) : ℝ) = ((250000000000 / 555088157153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (799689227 / 1000000000) ≤ -Real.log (500000000000 / 1112424699767) ∧
    -Real.log (500000000000 / 1112424699767) ≤ (799689229 / 1000000000) := by
  have h := checkLog_sound (w := (112424699767 / 2112424699767)) (n := 12)
    (lo := (106542047 / 1000000000)) (hi := (3329439 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112424699767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112424699767 / 1000000000000) = 1/(500000000000 / 1112424699767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (799689227 / 1000000000) (799689229 / 1000000000) (Real.log (1112424699767 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1112424699767 / 500000000000) = -Real.log (500000000000 / 1112424699767) := by
    rw [show ((1112424699767 / 500000000000) : ℝ) = ((500000000000 / 1112424699767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (286640709 / 500000000) ≤ -Real.log (100000000000 / 177407900577) ∧
    -Real.log (100000000000 / 177407900577) ≤ (573281419 / 1000000000) := by
  have h := checkLog_sound (w := (77407900577 / 277407900577)) (n := 12)
    (lo := (286640709 / 500000000)) (hi := (573281419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177407900577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177407900577 / 100000000000) = 1/(100000000000 / 177407900577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (286640709 / 500000000) (573281419 / 1000000000) (Real.log (177407900577 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (177407900577 / 100000000000) = -Real.log (100000000000 / 177407900577) := by
    rw [show ((177407900577 / 100000000000) : ℝ) = ((100000000000 / 177407900577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (22991217 / 40000000) ≤ -Real.log (125000000000 / 222092544591) ∧
    -Real.log (125000000000 / 222092544591) ≤ (287390213 / 500000000) := by
  have h := checkLog_sound (w := (97092544591 / 347092544591)) (n := 12)
    (lo := (22991217 / 40000000)) (hi := (287390213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222092544591 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222092544591 / 125000000000) = 1/(125000000000 / 222092544591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (22991217 / 40000000) (287390213 / 500000000) (Real.log (222092544591 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (222092544591 / 125000000000) = -Real.log (125000000000 / 222092544591) := by
    rw [show ((222092544591 / 125000000000) : ℝ) = ((125000000000 / 222092544591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0267
