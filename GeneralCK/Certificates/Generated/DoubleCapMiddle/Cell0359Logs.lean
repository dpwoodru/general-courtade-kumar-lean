import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0359
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

theorem reflection_log_1_neg : (105005409 / 500000000) ≤ -Real.log (10240 / 12633) ∧
    -Real.log (10240 / 12633) ≤ (210010819 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 22873)) (n := 12)
    (lo := (105005409 / 500000000)) (hi := (210010819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12633 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12633 / 10240) = 1/(10240 / 12633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (105005409 / 500000000) (210010819 / 1000000000) (Real.log (12633 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12633 / 10240) = -Real.log (10240 / 12633) := by
    rw [show ((12633 / 10240) : ℝ) = ((10240 / 12633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133085163 / 500000000) ≤ -Real.log (7847 / 10240) ∧
    -Real.log (7847 / 10240) ≤ (266170327 / 1000000000) := by
  have h := checkLog_sound (w := (2393 / 18087)) (n := 12)
    (lo := (133085163 / 500000000)) (hi := (266170327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7847) = 1/(7847 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266170327 / 1000000000) (-133085163 / 500000000) (Real.log (7847 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52443329 / 250000000) ≤ -Real.log (1024 / 1263) ∧
    -Real.log (1024 / 1263) ≤ (209773317 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2287)) (n := 12)
    (lo := (52443329 / 250000000)) (hi := (209773317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263 / 1024) = 1/(1024 / 1263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52443329 / 250000000) (209773317 / 1000000000) (Real.log (1263 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1263 / 1024) = -Real.log (1024 / 1263) := by
    rw [show ((1263 / 1024) : ℝ) = ((1024 / 1263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (265788087 / 1000000000) ≤ -Real.log (785 / 1024) ∧
    -Real.log (785 / 1024) ≤ (33223511 / 125000000) := by
  have h := checkLog_sound (w := (239 / 1809)) (n := 12)
    (lo := (265788087 / 1000000000)) (hi := (33223511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 785) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 785) = 1/(785 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33223511 / 125000000) (-265788087 / 1000000000) (Real.log (785 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191740207 / 500000000) ≤ -Real.log (5120 / 7513) ∧
    -Real.log (5120 / 7513) ≤ (76696083 / 200000000) := by
  have h := checkLog_sound (w := (2393 / 12633)) (n := 12)
    (lo := (191740207 / 500000000)) (hi := (76696083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7513 / 5120) = 1/(5120 / 7513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191740207 / 500000000) (76696083 / 200000000) (Real.log (7513 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7513 / 5120) = -Real.log (5120 / 7513) := by
    rw [show ((7513 / 5120) : ℝ) = ((5120 / 7513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (125990467 / 200000000) ≤ -Real.log (2727 / 5120) ∧
    -Real.log (2727 / 5120) ≤ (39372021 / 62500000) := by
  have h := checkLog_sound (w := (2393 / 7847)) (n := 12)
    (lo := (125990467 / 200000000)) (hi := (39372021 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2727) = 1/(2727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39372021 / 62500000) (-125990467 / 200000000) (Real.log (2727 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191540513 / 500000000) ≤ -Real.log (512 / 751) ∧
    -Real.log (512 / 751) ≤ (383081027 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1263)) (n := 12)
    (lo := (191540513 / 500000000)) (hi := (383081027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751 / 512) = 1/(512 / 751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191540513 / 500000000) (383081027 / 1000000000) (Real.log (751 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (751 / 512) = -Real.log (512 / 751) := by
    rw [show ((751 / 512) : ℝ) = ((512 / 751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (628852829 / 1000000000) ≤ -Real.log (273 / 512) ∧
    -Real.log (273 / 512) ≤ (62885283 / 100000000) := by
  have h := checkLog_sound (w := (239 / 785)) (n := 12)
    (lo := (628852829 / 1000000000)) (hi := (62885283 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 273) = 1/(273 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62885283 / 100000000) (-628852829 / 1000000000) (Real.log (273 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (287716321 / 1000000000) ≤ -Real.log (1000000 / 1333379) ∧
    -Real.log (1000000 / 1333379) ≤ (143858161 / 500000000) := by
  have h := checkLog_sound (w := (333379 / 2333379)) (n := 12)
    (lo := (287716321 / 1000000000)) (hi := (143858161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333379 / 1000000) = 1/(1000000 / 1333379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (287716321 / 1000000000) (143858161 / 500000000) (Real.log (1333379 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1333379 / 1000000) = -Real.log (1000000 / 1333379) := by
    rw [show ((1333379 / 1000000) : ℝ) = ((1000000 / 1333379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40553361 / 100000000) ≤ -Real.log (666621 / 1000000) ∧
    -Real.log (666621 / 1000000) ≤ (405533611 / 1000000000) := by
  have h := checkLog_sound (w := (333379 / 1666621)) (n := 12)
    (lo := (40553361 / 100000000)) (hi := (405533611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666621) = 1/(666621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-405533611 / 1000000000) (-40553361 / 100000000) (Real.log (666621 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (288037259 / 1000000000) ≤ -Real.log (1000000 / 1333807) ∧
    -Real.log (1000000 / 1333807) ≤ (14401863 / 50000000) := by
  have h := checkLog_sound (w := (333807 / 2333807)) (n := 12)
    (lo := (288037259 / 1000000000)) (hi := (14401863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333807 / 1000000) = 1/(1000000 / 1333807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (288037259 / 1000000000) (14401863 / 50000000) (Real.log (1333807 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1333807 / 1000000) = -Real.log (1000000 / 1333807) := by
    rw [show ((1333807 / 1000000) : ℝ) = ((1000000 / 1333807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20308793 / 50000000) ≤ -Real.log (666193 / 1000000) ∧
    -Real.log (666193 / 1000000) ≤ (406175861 / 1000000000) := by
  have h := checkLog_sound (w := (333807 / 1666193)) (n := 12)
    (lo := (20308793 / 50000000)) (hi := (406175861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666193) = 1/(666193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-406175861 / 1000000000) (-20308793 / 50000000) (Real.log (666193 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108850383 / 500000000) ≤ -Real.log (200000 / 248643) ∧
    -Real.log (200000 / 248643) ≤ (217700767 / 1000000000) := by
  have h := checkLog_sound (w := (48643 / 448643)) (n := 12)
    (lo := (108850383 / 500000000)) (hi := (217700767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248643 / 200000) = 1/(200000 / 248643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108850383 / 500000000) (217700767 / 1000000000) (Real.log (248643 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (248643 / 200000) = -Real.log (200000 / 248643) := by
    rw [show ((248643 / 200000) : ℝ) = ((200000 / 248643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (278676081 / 1000000000) ≤ -Real.log (151357 / 200000) ∧
    -Real.log (151357 / 200000) ≤ (139338041 / 500000000) := by
  have h := checkLog_sound (w := (48643 / 351357)) (n := 12)
    (lo := (278676081 / 1000000000)) (hi := (139338041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151357) = 1/(151357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-139338041 / 500000000) (-278676081 / 1000000000) (Real.log (151357 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27246073 / 125000000) ≤ -Real.log (250000 / 310887) ∧
    -Real.log (250000 / 310887) ≤ (43593717 / 200000000) := by
  have h := checkLog_sound (w := (60887 / 560887)) (n := 12)
    (lo := (27246073 / 125000000)) (hi := (43593717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310887 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310887 / 250000) = 1/(250000 / 310887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27246073 / 125000000) (43593717 / 200000000) (Real.log (310887 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (310887 / 250000) = -Real.log (250000 / 310887) := by
    rw [show ((310887 / 250000) : ℝ) = ((250000 / 310887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279116197 / 1000000000) ≤ -Real.log (189113 / 250000) ∧
    -Real.log (189113 / 250000) ≤ (139558099 / 500000000) := by
  have h := checkLog_sound (w := (60887 / 439113)) (n := 12)
    (lo := (279116197 / 1000000000)) (hi := (139558099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189113) = 1/(189113 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139558099 / 500000000) (-279116197 / 1000000000) (Real.log (189113 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (693249931 / 1000000000) ≤ -Real.log (250000000000 / 500051378519) ∧
    -Real.log (250000000000 / 500051378519) ≤ (693249933 / 1000000000) := by
  have h := checkLog_sound (w := (51378519 / 1000051378519)) (n := 12)
    (lo := (102751 / 1000000000)) (hi := (3211 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500051378519 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500051378519 / 500000000000) = 1/(250000000000 / 500051378519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (693249931 / 1000000000) (693249933 / 1000000000) (Real.log (500051378519 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (500051378519 / 250000000000) = -Real.log (250000000000 / 500051378519) := by
    rw [show ((500051378519 / 250000000000) : ℝ) = ((250000000000 / 500051378519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (694213119 / 1000000000) ≤ -Real.log (250000000000 / 500533253877) ∧
    -Real.log (250000000000 / 500533253877) ≤ (694213121 / 1000000000) := by
  have h := checkLog_sound (w := (533253877 / 1000533253877)) (n := 12)
    (lo := (1065939 / 1000000000)) (hi := (53297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500533253877 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500533253877 / 500000000000) = 1/(250000000000 / 500533253877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (694213119 / 1000000000) (694213121 / 1000000000) (Real.log (500533253877 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (500533253877 / 250000000000) = -Real.log (250000000000 / 500533253877) := by
    rw [show ((500533253877 / 250000000000) : ℝ) = ((250000000000 / 500533253877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (496376847 / 1000000000) ≤ -Real.log (500000000000 / 821379255667) ∧
    -Real.log (500000000000 / 821379255667) ≤ (31023553 / 62500000) := by
  have h := checkLog_sound (w := (321379255667 / 1321379255667)) (n := 12)
    (lo := (496376847 / 1000000000)) (hi := (31023553 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821379255667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821379255667 / 500000000000) = 1/(500000000000 / 821379255667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (496376847 / 1000000000) (31023553 / 62500000) (Real.log (821379255667 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (821379255667 / 500000000000) = -Real.log (500000000000 / 821379255667) := by
    rw [show ((821379255667 / 500000000000) : ℝ) = ((500000000000 / 821379255667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (248542391 / 500000000) ≤ -Real.log (250000000000 / 410980471993) ∧
    -Real.log (250000000000 / 410980471993) ≤ (497084783 / 1000000000) := by
  have h := checkLog_sound (w := (160980471993 / 660980471993)) (n := 12)
    (lo := (248542391 / 500000000)) (hi := (497084783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410980471993 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410980471993 / 250000000000) = 1/(250000000000 / 410980471993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (248542391 / 500000000) (497084783 / 1000000000) (Real.log (410980471993 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (410980471993 / 250000000000) = -Real.log (250000000000 / 410980471993) := by
    rw [show ((410980471993 / 250000000000) : ℝ) = ((250000000000 / 410980471993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0359
