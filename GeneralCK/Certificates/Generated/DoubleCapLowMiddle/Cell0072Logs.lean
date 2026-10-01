import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0072
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

theorem reflection_log_1_neg : (676704137 / 1000000000) ≤ -Real.log (5120 / 10073) ∧
    -Real.log (5120 / 10073) ≤ (338352069 / 500000000) := by
  have h := checkLog_sound (w := (4953 / 15193)) (n := 12)
    (lo := (676704137 / 1000000000)) (hi := (338352069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10073 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10073 / 5120) = 1/(5120 / 10073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676704137 / 1000000000) (338352069 / 500000000) (Real.log (10073 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (10073 / 5120) = -Real.log (5120 / 10073) := by
    rw [show ((10073 / 5120) : ℝ) = ((5120 / 10073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3422915903 / 1000000000) ≤ -Real.log (167 / 5120) ∧
    -Real.log (167 / 5120) ≤ (855728977 / 250000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 167) = 1/(167 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-855728977 / 250000000) (-3422915903 / 1000000000) (Real.log (167 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676515497 / 1000000000) ≤ -Real.log (51200 / 100711) ∧
    -Real.log (51200 / 100711) ≤ (338257749 / 500000000) := by
  have h := checkLog_sound (w := (49511 / 151911)) (n := 12)
    (lo := (676515497 / 1000000000)) (hi := (338257749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100711 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100711 / 51200) = 1/(51200 / 100711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676515497 / 1000000000) (338257749 / 500000000) (Real.log (100711 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100711 / 51200) = -Real.log (51200 / 100711) := by
    rw [show ((100711 / 51200) : ℝ) = ((51200 / 100711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3411602891 / 1000000000) ≤ -Real.log (1689 / 51200) ∧
    -Real.log (1689 / 51200) ≤ (213225181 / 62500000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1689) = 1/(1689 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-213225181 / 62500000) (-3411602891 / 1000000000) (Real.log (1689 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131997239 / 200000000) ≤ -Real.log (2560 / 4953) ∧
    -Real.log (2560 / 4953) ≤ (164996549 / 250000000) := by
  have h := checkLog_sound (w := (2393 / 7513)) (n := 12)
    (lo := (131997239 / 200000000)) (hi := (164996549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4953 / 2560) = 1/(2560 / 4953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131997239 / 200000000) (164996549 / 250000000) (Real.log (4953 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4953 / 2560) = -Real.log (2560 / 4953) := by
    rw [show ((4953 / 2560) : ℝ) = ((2560 / 4953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2729768723 / 1000000000) ≤ -Real.log (167 / 2560) ∧
    -Real.log (167 / 2560) ≤ (2729768727 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 167) = 1/(167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2729768727 / 1000000000) (-2729768723 / 1000000000) (Real.log (167 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131920503 / 200000000) ≤ -Real.log (25600 / 49511) ∧
    -Real.log (25600 / 49511) ≤ (164900629 / 250000000) := by
  have h := checkLog_sound (w := (23911 / 75111)) (n := 12)
    (lo := (131920503 / 200000000)) (hi := (164900629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49511 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49511 / 25600) = 1/(25600 / 49511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131920503 / 200000000) (164900629 / 250000000) (Real.log (49511 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49511 / 25600) = -Real.log (25600 / 49511) := by
    rw [show ((49511 / 25600) : ℝ) = ((25600 / 49511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2718455711 / 1000000000) ≤ -Real.log (1689 / 25600) ∧
    -Real.log (1689 / 25600) ≤ (543691143 / 200000000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1689) = 1/(1689 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-543691143 / 200000000) (-2718455711 / 1000000000) (Real.log (1689 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (679327121 / 1000000000) ≤ -Real.log (20000 / 39451) ∧
    -Real.log (20000 / 39451) ≤ (339663561 / 500000000) := by
  have h := checkLog_sound (w := (19451 / 59451)) (n := 12)
    (lo := (679327121 / 1000000000)) (hi := (339663561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39451 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39451 / 20000) = 1/(20000 / 39451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (679327121 / 1000000000) (339663561 / 500000000) (Real.log (39451 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (39451 / 20000) = -Real.log (20000 / 39451) := by
    rw [show ((39451 / 20000) : ℝ) = ((20000 / 39451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (898847277 / 250000000) ≤ -Real.log (549 / 20000) ∧
    -Real.log (549 / 20000) ≤ (1797694557 / 500000000) := by
  have h := checkLog_sound (w := (38 / 587)) (n := 12)
    (lo := (16206651 / 125000000)) (hi := (129653209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 549) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 549) = 1/(549 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1797694557 / 500000000) (-898847277 / 250000000) (Real.log (549 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169869039 / 250000000) ≤ -Real.log (250000 / 493211) ∧
    -Real.log (250000 / 493211) ≤ (679476157 / 1000000000) := by
  have h := checkLog_sound (w := (243211 / 743211)) (n := 12)
    (lo := (169869039 / 250000000)) (hi := (679476157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493211 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493211 / 250000) = 1/(250000 / 493211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169869039 / 250000000) (679476157 / 1000000000) (Real.log (493211 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (493211 / 250000) = -Real.log (250000 / 493211) := by
    rw [show ((493211 / 250000) : ℝ) = ((250000 / 493211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3606157259 / 1000000000) ≤ -Real.log (6789 / 250000) ∧
    -Real.log (6789 / 250000) ≤ (721231453 / 200000000) := by
  have h := checkLog_sound (w := (2047 / 29203)) (n := 12)
    (lo := (140421359 / 1000000000)) (hi := (1755267 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13578) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13578) = 1/(6789 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-721231453 / 200000000) (-3606157259 / 1000000000) (Real.log (6789 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679231809 / 1000000000) ≤ -Real.log (500000 / 986181) ∧
    -Real.log (500000 / 986181) ≤ (67923181 / 100000000) := by
  have h := checkLog_sound (w := (486181 / 1486181)) (n := 12)
    (lo := (679231809 / 1000000000)) (hi := (67923181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986181 / 500000) = 1/(500000 / 986181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679231809 / 1000000000) (67923181 / 100000000) (Real.log (986181 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986181 / 500000) = -Real.log (500000 / 986181) := by
    rw [show ((986181 / 500000) : ℝ) = ((500000 / 986181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1794281819 / 500000000) ≤ -Real.log (13819 / 500000) ∧
    -Real.log (13819 / 500000) ≤ (897140911 / 250000000) := by
  have h := checkLog_sound (w := (903 / 14722)) (n := 12)
    (lo := (61413869 / 500000000)) (hi := (122827739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13819) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13819) = 1/(13819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-897140911 / 250000000) (-1794281819 / 500000000) (Real.log (13819 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21230731 / 31250000) ≤ -Real.log (1000000 / 1972661) ∧
    -Real.log (1000000 / 1972661) ≤ (679383393 / 1000000000) := by
  have h := checkLog_sound (w := (972661 / 2972661)) (n := 12)
    (lo := (21230731 / 31250000)) (hi := (679383393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972661 / 1000000) = 1/(1000000 / 1972661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21230731 / 31250000) (679383393 / 1000000000) (Real.log (1972661 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972661 / 1000000) = -Real.log (1000000 / 1972661) := by
    rw [show ((1972661 / 1000000) : ℝ) = ((1000000 / 1972661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1799720511 / 500000000) ≤ -Real.log (27339 / 1000000) ∧
    -Real.log (27339 / 1000000) ≤ (899860257 / 250000000) := by
  have h := checkLog_sound (w := (3911 / 58589)) (n := 12)
    (lo := (66852561 / 500000000)) (hi := (133705123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27339) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27339) = 1/(27339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-899860257 / 250000000) (-1799720511 / 500000000) (Real.log (27339 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4274716229 / 1000000000) ≤ -Real.log (250000000000 / 17964936247723) ∧
    -Real.log (250000000000 / 17964936247723) ≤ (1068679059 / 250000000) := by
  have h := checkLog_sound (w := (1964936247723 / 33964936247723)) (n := 12)
    (lo := (115833149 / 1000000000)) (hi := (2316663 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17964936247723 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17964936247723 / 16000000000000) = 1/(250000000000 / 17964936247723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4274716229 / 1000000000) (1068679059 / 250000000) (Real.log (17964936247723 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (17964936247723 / 250000000000) = -Real.log (250000000000 / 17964936247723) := by
    rw [show ((17964936247723 / 250000000000) : ℝ) = ((250000000000 / 17964936247723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (857126683 / 200000000) ≤ -Real.log (1953125000 / 141891697507) ∧
    -Real.log (1953125000 / 141891697507) ≤ (2142816711 / 500000000) := by
  have h := checkLog_sound (w := (16891697507 / 266891697507)) (n := 12)
    (lo := (25350067 / 200000000)) (hi := (990237 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141891697507 / 125000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(141891697507 / 125000000000) = 1/(1953125000 / 141891697507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (857126683 / 200000000) (2142816711 / 500000000) (Real.log (141891697507 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141891697507 / 1953125000) = -Real.log (1953125000 / 141891697507) := by
    rw [show ((141891697507 / 1953125000) : ℝ) = ((1953125000 / 141891697507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4267795447 / 1000000000) ≤ -Real.log (62500000000 / 4460258520877) ∧
    -Real.log (62500000000 / 4460258520877) ≤ (2133897727 / 500000000) := by
  have h := checkLog_sound (w := (460258520877 / 8460258520877)) (n := 12)
    (lo := (108912367 / 1000000000)) (hi := (6807023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4460258520877 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4460258520877 / 4000000000000) = 1/(62500000000 / 4460258520877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4267795447 / 1000000000) (2133897727 / 500000000) (Real.log (4460258520877 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4460258520877 / 62500000000) = -Real.log (62500000000 / 4460258520877) := by
    rw [show ((4460258520877 / 62500000000) : ℝ) = ((62500000000 / 4460258520877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2139412207 / 500000000) ≤ -Real.log (15625000000 / 1127430707963) ∧
    -Real.log (15625000000 / 1127430707963) ≤ (4278824421 / 1000000000) := by
  have h := checkLog_sound (w := (127430707963 / 2127430707963)) (n := 12)
    (lo := (59970667 / 500000000)) (hi := (23988267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127430707963 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1127430707963 / 1000000000000) = 1/(15625000000 / 1127430707963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2139412207 / 500000000) (4278824421 / 1000000000) (Real.log (1127430707963 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1127430707963 / 15625000000) = -Real.log (15625000000 / 1127430707963) := by
    rw [show ((1127430707963 / 15625000000) : ℝ) = ((15625000000 / 1127430707963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0072
