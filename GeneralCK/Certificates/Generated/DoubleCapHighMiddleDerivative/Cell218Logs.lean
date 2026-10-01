import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell218
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

theorem reflection_log_1_neg : (40108199 / 125000000) ≤ -Real.log (5120 / 7057) ∧
    -Real.log (5120 / 7057) ≤ (320865593 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 12177)) (n := 12)
    (lo := (40108199 / 125000000)) (hi := (320865593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7057 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7057 / 5120) = 1/(5120 / 7057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40108199 / 125000000) (320865593 / 1000000000) (Real.log (7057 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7057 / 5120) = -Real.log (5120 / 7057) := by
    rw [show ((7057 / 5120) : ℝ) = ((5120 / 7057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47533029 / 100000000) ≤ -Real.log (3183 / 5120) ∧
    -Real.log (3183 / 5120) ≤ (475330291 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 8303)) (n := 12)
    (lo := (47533029 / 100000000)) (hi := (475330291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3183) = 1/(3183 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-475330291 / 1000000000) (-47533029 / 100000000) (Real.log (3183 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40055049 / 125000000) ≤ -Real.log (2560 / 3527) ∧
    -Real.log (2560 / 3527) ≤ (320440393 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 6087)) (n := 12)
    (lo := (40055049 / 125000000)) (hi := (320440393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3527 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3527 / 2560) = 1/(2560 / 3527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40055049 / 125000000) (320440393 / 1000000000) (Real.log (3527 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3527 / 2560) = -Real.log (2560 / 3527) := by
    rw [show ((3527 / 2560) : ℝ) = ((2560 / 3527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (474388227 / 1000000000) ≤ -Real.log (1593 / 2560) ∧
    -Real.log (1593 / 2560) ≤ (118597057 / 250000000) := by
  have h := checkLog_sound (w := (967 / 4153)) (n := 12)
    (lo := (474388227 / 1000000000)) (hi := (118597057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1593) = 1/(1593 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118597057 / 250000000) (-474388227 / 1000000000) (Real.log (1593 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119031057 / 500000000) ≤ -Real.log (250000 / 317197) ∧
    -Real.log (250000 / 317197) ≤ (47612423 / 200000000) := by
  have h := checkLog_sound (w := (67197 / 567197)) (n := 12)
    (lo := (119031057 / 500000000)) (hi := (47612423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317197 / 250000) = 1/(250000 / 317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119031057 / 500000000) (47612423 / 200000000) (Real.log (317197 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (317197 / 250000) = -Real.log (250000 / 317197) := by
    rw [show ((317197 / 250000) : ℝ) = ((250000 / 317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (313051847 / 1000000000) ≤ -Real.log (182803 / 250000) ∧
    -Real.log (182803 / 250000) ≤ (39131481 / 125000000) := by
  have h := checkLog_sound (w := (67197 / 432803)) (n := 12)
    (lo := (313051847 / 1000000000)) (hi := (39131481 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 182803) = 1/(182803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39131481 / 125000000) (-313051847 / 1000000000) (Real.log (182803 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (238395447 / 1000000000) ≤ -Real.log (1000000 / 1269211) ∧
    -Real.log (1000000 / 1269211) ≤ (29799431 / 125000000) := by
  have h := checkLog_sound (w := (269211 / 2269211)) (n := 12)
    (lo := (238395447 / 1000000000)) (hi := (29799431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269211 / 1000000) = 1/(1000000 / 1269211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (238395447 / 1000000000) (29799431 / 125000000) (Real.log (1269211 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1269211 / 1000000) = -Real.log (1000000 / 1269211) := by
    rw [show ((1269211 / 1000000) : ℝ) = ((1000000 / 1269211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156815253 / 500000000) ≤ -Real.log (730789 / 1000000) ∧
    -Real.log (730789 / 1000000) ≤ (313630507 / 1000000000) := by
  have h := checkLog_sound (w := (269211 / 1730789)) (n := 12)
    (lo := (156815253 / 500000000)) (hi := (313630507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730789) = 1/(730789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-313630507 / 1000000000) (-156815253 / 500000000) (Real.log (730789 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177260437 / 1000000000) ≤ -Real.log (500000 / 596971) ∧
    -Real.log (500000 / 596971) ≤ (88630219 / 500000000) := by
  have h := checkLog_sound (w := (96971 / 1096971)) (n := 12)
    (lo := (177260437 / 1000000000)) (hi := (88630219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596971 / 500000) = 1/(500000 / 596971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177260437 / 1000000000) (88630219 / 500000000) (Real.log (596971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (596971 / 500000) = -Real.log (500000 / 596971) := by
    rw [show ((596971 / 500000) : ℝ) = ((500000 / 596971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107799789 / 500000000) ≤ -Real.log (403029 / 500000) ∧
    -Real.log (403029 / 500000) ≤ (215599579 / 1000000000) := by
  have h := checkLog_sound (w := (96971 / 903029)) (n := 12)
    (lo := (107799789 / 500000000)) (hi := (215599579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403029) = 1/(403029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-215599579 / 1000000000) (-107799789 / 500000000) (Real.log (403029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5547737 / 31250000) ≤ -Real.log (1000000 / 1194261) ∧
    -Real.log (1000000 / 1194261) ≤ (35505517 / 200000000) := by
  have h := checkLog_sound (w := (194261 / 2194261)) (n := 12)
    (lo := (5547737 / 31250000)) (hi := (35505517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194261 / 1000000) = 1/(1000000 / 1194261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5547737 / 31250000) (35505517 / 200000000) (Real.log (1194261 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1194261 / 1000000) = -Real.log (1000000 / 1194261) := by
    rw [show ((1194261 / 1000000) : ℝ) = ((1000000 / 1194261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21599541 / 100000000) ≤ -Real.log (805739 / 1000000) ∧
    -Real.log (805739 / 1000000) ≤ (215995411 / 1000000000) := by
  have h := checkLog_sound (w := (194261 / 1805739)) (n := 12)
    (lo := (21599541 / 100000000)) (hi := (215995411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805739) = 1/(805739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-215995411 / 1000000000) (-21599541 / 100000000) (Real.log (805739 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (794828619 / 1000000000) ≤ -Real.log (500000000000 / 1107030759573) ∧
    -Real.log (500000000000 / 1107030759573) ≤ (794828621 / 1000000000) := by
  have h := checkLog_sound (w := (107030759573 / 2107030759573)) (n := 12)
    (lo := (101681439 / 1000000000)) (hi := (635509 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107030759573 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1107030759573 / 1000000000000) = 1/(500000000000 / 1107030759573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (794828619 / 1000000000) (794828621 / 1000000000) (Real.log (1107030759573 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1107030759573 / 500000000000) = -Real.log (500000000000 / 1107030759573) := by
    rw [show ((1107030759573 / 500000000000) : ℝ) = ((500000000000 / 1107030759573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (796195883 / 1000000000) ≤ -Real.log (31250000000 / 69284087339) ∧
    -Real.log (31250000000 / 69284087339) ≤ (159239177 / 200000000) := by
  have h := checkLog_sound (w := (6784087339 / 131784087339)) (n := 12)
    (lo := (103048703 / 1000000000)) (hi := (201267 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69284087339 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69284087339 / 62500000000) = 1/(31250000000 / 69284087339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (796195883 / 1000000000) (159239177 / 200000000) (Real.log (69284087339 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (69284087339 / 31250000000) = -Real.log (31250000000 / 69284087339) := by
    rw [show ((69284087339 / 31250000000) : ℝ) = ((31250000000 / 69284087339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (551113961 / 1000000000) ≤ -Real.log (125000000000 / 216898108893) ∧
    -Real.log (125000000000 / 216898108893) ≤ (275556981 / 500000000) := by
  have h := checkLog_sound (w := (91898108893 / 341898108893)) (n := 12)
    (lo := (551113961 / 1000000000)) (hi := (275556981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216898108893 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216898108893 / 125000000000) = 1/(125000000000 / 216898108893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (551113961 / 1000000000) (275556981 / 500000000) (Real.log (216898108893 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (216898108893 / 125000000000) = -Real.log (125000000000 / 216898108893) := by
    rw [show ((216898108893 / 125000000000) : ℝ) = ((125000000000 / 216898108893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276012977 / 500000000) ≤ -Real.log (500000000000 / 868384034243) ∧
    -Real.log (500000000000 / 868384034243) ≤ (110405191 / 200000000) := by
  have h := checkLog_sound (w := (368384034243 / 1368384034243)) (n := 12)
    (lo := (276012977 / 500000000)) (hi := (110405191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868384034243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868384034243 / 500000000000) = 1/(500000000000 / 868384034243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (276012977 / 500000000) (110405191 / 200000000) (Real.log (868384034243 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (868384034243 / 500000000000) = -Real.log (500000000000 / 868384034243) := by
    rw [show ((868384034243 / 500000000000) : ℝ) = ((500000000000 / 868384034243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (24553751 / 62500000) ≤ -Real.log (500000000000 / 740605514739) ∧
    -Real.log (500000000000 / 740605514739) ≤ (392860017 / 1000000000) := by
  have h := checkLog_sound (w := (240605514739 / 1240605514739)) (n := 12)
    (lo := (24553751 / 62500000)) (hi := (392860017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740605514739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740605514739 / 500000000000) = 1/(500000000000 / 740605514739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24553751 / 62500000) (392860017 / 1000000000) (Real.log (740605514739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (740605514739 / 500000000000) = -Real.log (500000000000 / 740605514739) := by
    rw [show ((740605514739 / 500000000000) : ℝ) = ((500000000000 / 740605514739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (196761497 / 500000000) ≤ -Real.log (500000000000 / 741096682673) ∧
    -Real.log (500000000000 / 741096682673) ≤ (78704599 / 200000000) := by
  have h := checkLog_sound (w := (241096682673 / 1241096682673)) (n := 12)
    (lo := (196761497 / 500000000)) (hi := (78704599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741096682673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741096682673 / 500000000000) = 1/(500000000000 / 741096682673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (196761497 / 500000000) (78704599 / 200000000) (Real.log (741096682673 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741096682673 / 500000000000) = -Real.log (500000000000 / 741096682673) := by
    rw [show ((741096682673 / 500000000000) : ℝ) = ((500000000000 / 741096682673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19233913 / 500000000) ≤ -Real.log (962262663879 / 1000000000000) ∧
    -Real.log (962262663879 / 1000000000000) ≤ (38467827 / 1000000000) := by
  have h := checkLog_sound (w := (37737336121 / 1962262663879)) (n := 12)
    (lo := (19233913 / 500000000)) (hi := (38467827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962262663879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962262663879) = 1/(962262663879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38467827 / 1000000000) (-19233913 / 500000000) (Real.log (962262663879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38339141 / 1000000000) ≤ -Real.log (240596625159 / 250000000000) ∧
    -Real.log (240596625159 / 250000000000) ≤ (19169571 / 500000000) := by
  have h := checkLog_sound (w := (9403374841 / 490596625159)) (n := 12)
    (lo := (38339141 / 1000000000)) (hi := (19169571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240596625159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240596625159) = 1/(240596625159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19169571 / 500000000) (-38339141 / 1000000000) (Real.log (240596625159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell218
