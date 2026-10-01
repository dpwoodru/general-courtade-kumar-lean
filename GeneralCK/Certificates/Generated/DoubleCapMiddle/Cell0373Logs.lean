import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0373
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

theorem reflection_log_1_neg : (206680653 / 1000000000) ≤ -Real.log (10240 / 12591) ∧
    -Real.log (10240 / 12591) ≤ (103340327 / 500000000) := by
  have h := checkLog_sound (w := (2351 / 22831)) (n := 12)
    (lo := (206680653 / 1000000000)) (hi := (103340327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12591 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12591 / 10240) = 1/(10240 / 12591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (206680653 / 1000000000) (103340327 / 500000000) (Real.log (12591 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12591 / 10240) = -Real.log (10240 / 12591) := by
    rw [show ((12591 / 10240) : ℝ) = ((10240 / 12591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52166447 / 200000000) ≤ -Real.log (7889 / 10240) ∧
    -Real.log (7889 / 10240) ≤ (65208059 / 250000000) := by
  have h := checkLog_sound (w := (2351 / 18129)) (n := 12)
    (lo := (52166447 / 200000000)) (hi := (65208059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7889) = 1/(7889 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65208059 / 250000000) (-52166447 / 200000000) (Real.log (7889 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (206442359 / 1000000000) ≤ -Real.log (2560 / 3147) ∧
    -Real.log (2560 / 3147) ≤ (5161059 / 25000000) := by
  have h := checkLog_sound (w := (587 / 5707)) (n := 12)
    (lo := (206442359 / 1000000000)) (hi := (5161059 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3147 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3147 / 2560) = 1/(2560 / 3147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (206442359 / 1000000000) (5161059 / 25000000) (Real.log (3147 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3147 / 2560) = -Real.log (2560 / 3147) := by
    rw [show ((3147 / 2560) : ℝ) = ((2560 / 3147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (260452031 / 1000000000) ≤ -Real.log (1973 / 2560) ∧
    -Real.log (1973 / 2560) ≤ (4069563 / 15625000) := by
  have h := checkLog_sound (w := (587 / 4533)) (n := 12)
    (lo := (260452031 / 1000000000)) (hi := (4069563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1973) = 1/(1973 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4069563 / 15625000) (-260452031 / 1000000000) (Real.log (1973 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (377874419 / 1000000000) ≤ -Real.log (5120 / 7471) ∧
    -Real.log (5120 / 7471) ≤ (18893721 / 50000000) := by
  have h := checkLog_sound (w := (2351 / 12591)) (n := 12)
    (lo := (377874419 / 1000000000)) (hi := (18893721 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7471 / 5120) = 1/(5120 / 7471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (377874419 / 1000000000) (18893721 / 50000000) (Real.log (7471 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7471 / 5120) = -Real.log (5120 / 7471) := by
    rw [show ((7471 / 5120) : ℝ) = ((5120 / 7471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (307334097 / 500000000) ≤ -Real.log (2769 / 5120) ∧
    -Real.log (2769 / 5120) ≤ (122933639 / 200000000) := by
  have h := checkLog_sound (w := (2351 / 7889)) (n := 12)
    (lo := (307334097 / 500000000)) (hi := (122933639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2769) = 1/(2769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122933639 / 200000000) (-307334097 / 500000000) (Real.log (2769 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (188736393 / 500000000) ≤ -Real.log (1280 / 1867) ∧
    -Real.log (1280 / 1867) ≤ (377472787 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3147)) (n := 12)
    (lo := (188736393 / 500000000)) (hi := (377472787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867 / 1280) = 1/(1280 / 1867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (188736393 / 500000000) (377472787 / 1000000000) (Real.log (1867 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1867 / 1280) = -Real.log (1280 / 1867) := by
    rw [show ((1867 / 1280) : ℝ) = ((1280 / 1867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (613585357 / 1000000000) ≤ -Real.log (693 / 1280) ∧
    -Real.log (693 / 1280) ≤ (306792679 / 500000000) := by
  have h := checkLog_sound (w := (587 / 1973)) (n := 12)
    (lo := (613585357 / 1000000000)) (hi := (306792679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 693) = 1/(693 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306792679 / 500000000) (-613585357 / 1000000000) (Real.log (693 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35402391 / 125000000) ≤ -Real.log (250000 / 331849) ∧
    -Real.log (250000 / 331849) ≤ (283219129 / 1000000000) := by
  have h := checkLog_sound (w := (81849 / 581849)) (n := 12)
    (lo := (35402391 / 125000000)) (hi := (283219129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331849 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331849 / 250000) = 1/(250000 / 331849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35402391 / 125000000) (283219129 / 1000000000) (Real.log (331849 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (331849 / 250000) = -Real.log (250000 / 331849) := by
    rw [show ((331849 / 250000) : ℝ) = ((250000 / 331849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99149633 / 250000000) ≤ -Real.log (168151 / 250000) ∧
    -Real.log (168151 / 250000) ≤ (396598533 / 1000000000) := by
  have h := checkLog_sound (w := (81849 / 418151)) (n := 12)
    (lo := (99149633 / 250000000)) (hi := (396598533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 168151) = 1/(168151 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-396598533 / 1000000000) (-99149633 / 250000000) (Real.log (168151 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35442689 / 125000000) ≤ -Real.log (62500 / 82989) ∧
    -Real.log (62500 / 82989) ≤ (283541513 / 1000000000) := by
  have h := checkLog_sound (w := (20489 / 145489)) (n := 12)
    (lo := (35442689 / 125000000)) (hi := (283541513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82989 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82989 / 62500) = 1/(62500 / 82989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35442689 / 125000000) (283541513 / 1000000000) (Real.log (82989 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (82989 / 62500) = -Real.log (62500 / 82989) := by
    rw [show ((82989 / 62500) : ℝ) = ((62500 / 82989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (397235067 / 1000000000) ≤ -Real.log (42011 / 62500) ∧
    -Real.log (42011 / 62500) ≤ (99308767 / 250000000) := by
  have h := checkLog_sound (w := (20489 / 104511)) (n := 12)
    (lo := (397235067 / 1000000000)) (hi := (99308767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42011) = 1/(42011 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-99308767 / 250000000) (-397235067 / 1000000000) (Real.log (42011 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26745897 / 125000000) ≤ -Real.log (500000 / 619291) ∧
    -Real.log (500000 / 619291) ≤ (213967177 / 1000000000) := by
  have h := checkLog_sound (w := (119291 / 1119291)) (n := 12)
    (lo := (26745897 / 125000000)) (hi := (213967177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619291 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619291 / 500000) = 1/(500000 / 619291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26745897 / 125000000) (213967177 / 1000000000) (Real.log (619291 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (619291 / 500000) = -Real.log (500000 / 619291) := by
    rw [show ((619291 / 500000) : ℝ) = ((500000 / 619291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136286397 / 500000000) ≤ -Real.log (380709 / 500000) ∧
    -Real.log (380709 / 500000) ≤ (54514559 / 200000000) := by
  have h := checkLog_sound (w := (119291 / 880709)) (n := 12)
    (lo := (136286397 / 500000000)) (hi := (54514559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380709) = 1/(380709 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54514559 / 200000000) (-136286397 / 500000000) (Real.log (380709 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (107117191 / 500000000) ≤ -Real.log (1000000 / 1238913) ∧
    -Real.log (1000000 / 1238913) ≤ (214234383 / 1000000000) := by
  have h := checkLog_sound (w := (238913 / 2238913)) (n := 12)
    (lo := (107117191 / 500000000)) (hi := (214234383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238913 / 1000000) = 1/(1000000 / 1238913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (107117191 / 500000000) (214234383 / 1000000000) (Real.log (1238913 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238913 / 1000000) = -Real.log (1000000 / 1238913) := by
    rw [show ((1238913 / 1000000) : ℝ) = ((1000000 / 1238913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (68251901 / 250000000) ≤ -Real.log (761087 / 1000000) ∧
    -Real.log (761087 / 1000000) ≤ (54601521 / 200000000) := by
  have h := checkLog_sound (w := (238913 / 1761087)) (n := 12)
    (lo := (68251901 / 250000000)) (hi := (54601521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761087) = 1/(761087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-54601521 / 200000000) (-68251901 / 250000000) (Real.log (761087 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (33990883 / 50000000) ≤ -Real.log (500000000000 / 986758925013) ∧
    -Real.log (500000000000 / 986758925013) ≤ (679817661 / 1000000000) := by
  have h := checkLog_sound (w := (486758925013 / 1486758925013)) (n := 12)
    (lo := (33990883 / 50000000)) (hi := (679817661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986758925013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986758925013 / 500000000000) = 1/(500000000000 / 986758925013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33990883 / 50000000) (679817661 / 1000000000) (Real.log (986758925013 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (986758925013 / 500000000000) = -Real.log (500000000000 / 986758925013) := by
    rw [show ((986758925013 / 500000000000) : ℝ) = ((500000000000 / 986758925013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34038829 / 50000000) ≤ -Real.log (100000000000 / 197541120183) ∧
    -Real.log (100000000000 / 197541120183) ≤ (680776581 / 1000000000) := by
  have h := checkLog_sound (w := (97541120183 / 297541120183)) (n := 12)
    (lo := (34038829 / 50000000)) (hi := (680776581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197541120183 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197541120183 / 100000000000) = 1/(100000000000 / 197541120183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34038829 / 50000000) (680776581 / 1000000000) (Real.log (197541120183 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (197541120183 / 100000000000) = -Real.log (100000000000 / 197541120183) := by
    rw [show ((197541120183 / 100000000000) : ℝ) = ((100000000000 / 197541120183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (486539971 / 1000000000) ≤ -Real.log (500000000000 / 813339059491) ∧
    -Real.log (500000000000 / 813339059491) ≤ (121634993 / 250000000) := by
  have h := checkLog_sound (w := (313339059491 / 1313339059491)) (n := 12)
    (lo := (486539971 / 1000000000)) (hi := (121634993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813339059491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813339059491 / 500000000000) = 1/(500000000000 / 813339059491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (486539971 / 1000000000) (121634993 / 250000000) (Real.log (813339059491 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (813339059491 / 500000000000) = -Real.log (500000000000 / 813339059491) := by
    rw [show ((813339059491 / 500000000000) : ℝ) = ((500000000000 / 813339059491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (243620993 / 500000000) ≤ -Real.log (500000000000 / 813910236281) ∧
    -Real.log (500000000000 / 813910236281) ≤ (487241987 / 1000000000) := by
  have h := checkLog_sound (w := (313910236281 / 1313910236281)) (n := 12)
    (lo := (243620993 / 500000000)) (hi := (487241987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813910236281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813910236281 / 500000000000) = 1/(500000000000 / 813910236281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (243620993 / 500000000) (487241987 / 1000000000) (Real.log (813910236281 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (813910236281 / 500000000000) = -Real.log (500000000000 / 813910236281) := by
    rw [show ((813910236281 / 500000000000) : ℝ) = ((500000000000 / 813910236281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0373
