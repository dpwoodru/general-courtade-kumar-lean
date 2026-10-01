import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell224
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

theorem reflection_log_1_neg : (80853251 / 250000000) ≤ -Real.log (1024 / 1415) ∧
    -Real.log (1024 / 1415) ≤ (64682601 / 200000000) := by
  have h := checkLog_sound (w := (391 / 2439)) (n := 12)
    (lo := (80853251 / 250000000)) (hi := (64682601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415 / 1024) = 1/(1024 / 1415) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80853251 / 250000000) (64682601 / 200000000) (Real.log (1415 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1415 / 1024) = -Real.log (1024 / 1415) := by
    rw [show ((1415 / 1024) : ℝ) = ((1024 / 1415) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (481001383 / 1000000000) ≤ -Real.log (633 / 1024) ∧
    -Real.log (633 / 1024) ≤ (60125173 / 125000000) := by
  have h := checkLog_sound (w := (391 / 1657)) (n := 12)
    (lo := (481001383 / 1000000000)) (hi := (60125173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 633) = 1/(633 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60125173 / 125000000) (-481001383 / 1000000000) (Real.log (633 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (161494443 / 500000000) ≤ -Real.log (160 / 221) ∧
    -Real.log (160 / 221) ≤ (322988887 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 381)) (n := 12)
    (lo := (161494443 / 500000000)) (hi := (322988887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221 / 160) = 1/(160 / 221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (161494443 / 500000000) (322988887 / 1000000000) (Real.log (221 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (221 / 160) = -Real.log (160 / 221) := by
    rw [show ((221 / 160) : ℝ) = ((160 / 221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (96010793 / 200000000) ≤ -Real.log (99 / 160) ∧
    -Real.log (99 / 160) ≤ (240026983 / 500000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 99) = 1/(99 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240026983 / 500000000) (-96010793 / 200000000) (Real.log (99 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24005809 / 100000000) ≤ -Real.log (1000000 / 1271323) ∧
    -Real.log (1000000 / 1271323) ≤ (240058091 / 1000000000) := by
  have h := checkLog_sound (w := (271323 / 2271323)) (n := 12)
    (lo := (24005809 / 100000000)) (hi := (240058091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271323 / 1000000) = 1/(1000000 / 1271323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24005809 / 100000000) (240058091 / 1000000000) (Real.log (1271323 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1271323 / 1000000) = -Real.log (1000000 / 1271323) := by
    rw [show ((1271323 / 1000000) : ℝ) = ((1000000 / 1271323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316524717 / 1000000000) ≤ -Real.log (728677 / 1000000) ∧
    -Real.log (728677 / 1000000) ≤ (158262359 / 500000000) := by
  have h := checkLog_sound (w := (271323 / 1728677)) (n := 12)
    (lo := (316524717 / 1000000000)) (hi := (158262359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728677) = 1/(728677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158262359 / 500000000) (-316524717 / 1000000000) (Real.log (728677 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48078309 / 200000000) ≤ -Real.log (1000000 / 1271747) ∧
    -Real.log (1000000 / 1271747) ≤ (120195773 / 500000000) := by
  have h := checkLog_sound (w := (271747 / 2271747)) (n := 12)
    (lo := (48078309 / 200000000)) (hi := (120195773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271747 / 1000000) = 1/(1000000 / 1271747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48078309 / 200000000) (120195773 / 500000000) (Real.log (1271747 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1271747 / 1000000) = -Real.log (1000000 / 1271747) := by
    rw [show ((1271747 / 1000000) : ℝ) = ((1000000 / 1271747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (317106763 / 1000000000) ≤ -Real.log (728253 / 1000000) ∧
    -Real.log (728253 / 1000000) ≤ (79276691 / 250000000) := by
  have h := checkLog_sound (w := (271747 / 1728253)) (n := 12)
    (lo := (317106763 / 1000000000)) (hi := (79276691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728253) = 1/(728253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-79276691 / 250000000) (-317106763 / 1000000000) (Real.log (728253 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178855557 / 1000000000) ≤ -Real.log (125000 / 149481) ∧
    -Real.log (125000 / 149481) ≤ (89427779 / 500000000) := by
  have h := checkLog_sound (w := (24481 / 274481)) (n := 12)
    (lo := (178855557 / 1000000000)) (hi := (89427779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149481 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149481 / 125000) = 1/(125000 / 149481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178855557 / 1000000000) (89427779 / 500000000) (Real.log (149481 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (149481 / 125000) = -Real.log (125000 / 149481) := by
    rw [show ((149481 / 125000) : ℝ) = ((125000 / 149481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54491743 / 250000000) ≤ -Real.log (100519 / 125000) ∧
    -Real.log (100519 / 125000) ≤ (217966973 / 1000000000) := by
  have h := checkLog_sound (w := (24481 / 225519)) (n := 12)
    (lo := (54491743 / 250000000)) (hi := (217966973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100519) = 1/(100519 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-217966973 / 1000000000) (-54491743 / 250000000) (Real.log (100519 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (179121441 / 1000000000) ≤ -Real.log (500000 / 598083) ∧
    -Real.log (500000 / 598083) ≤ (89560721 / 500000000) := by
  have h := checkLog_sound (w := (98083 / 1098083)) (n := 12)
    (lo := (179121441 / 1000000000)) (hi := (89560721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598083 / 500000) = 1/(500000 / 598083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (179121441 / 1000000000) (89560721 / 500000000) (Real.log (598083 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (598083 / 500000) = -Real.log (500000 / 598083) := by
    rw [show ((598083 / 500000) : ℝ) = ((500000 / 598083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (109181249 / 500000000) ≤ -Real.log (401917 / 500000) ∧
    -Real.log (401917 / 500000) ≤ (218362499 / 1000000000) := by
  have h := checkLog_sound (w := (98083 / 901917)) (n := 12)
    (lo := (109181249 / 500000000)) (hi := (218362499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401917) = 1/(401917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-218362499 / 1000000000) (-109181249 / 500000000) (Real.log (401917 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16060857 / 20000000) ≤ -Real.log (500000000000 / 1116161616161) ∧
    -Real.log (500000000000 / 1116161616161) ≤ (200760713 / 250000000) := by
  have h := checkLog_sound (w := (116161616161 / 2116161616161)) (n := 12)
    (lo := (10989567 / 100000000)) (hi := (109895671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116161616161 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1116161616161 / 1000000000000) = 1/(500000000000 / 1116161616161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16060857 / 20000000) (200760713 / 250000000) (Real.log (1116161616161 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1116161616161 / 500000000000) = -Real.log (500000000000 / 1116161616161) := by
    rw [show ((1116161616161 / 500000000000) : ℝ) = ((500000000000 / 1116161616161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (804414387 / 1000000000) ≤ -Real.log (500000000000 / 1117693522907) ∧
    -Real.log (500000000000 / 1117693522907) ≤ (804414389 / 1000000000) := by
  have h := checkLog_sound (w := (117693522907 / 2117693522907)) (n := 12)
    (lo := (111267207 / 1000000000)) (hi := (13908401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117693522907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1117693522907 / 1000000000000) = 1/(500000000000 / 1117693522907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (804414387 / 1000000000) (804414389 / 1000000000) (Real.log (1117693522907 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1117693522907 / 500000000000) = -Real.log (500000000000 / 1117693522907) := by
    rw [show ((1117693522907 / 500000000000) : ℝ) = ((500000000000 / 1117693522907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (69572851 / 125000000) ≤ -Real.log (250000000000 / 436175081689) ∧
    -Real.log (250000000000 / 436175081689) ≤ (556582809 / 1000000000) := by
  have h := checkLog_sound (w := (186175081689 / 686175081689)) (n := 12)
    (lo := (69572851 / 125000000)) (hi := (556582809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436175081689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436175081689 / 250000000000) = 1/(250000000000 / 436175081689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69572851 / 125000000) (556582809 / 1000000000) (Real.log (436175081689 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (436175081689 / 250000000000) = -Real.log (250000000000 / 436175081689) := by
    rw [show ((436175081689 / 250000000000) : ℝ) = ((250000000000 / 436175081689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (557498309 / 1000000000) ≤ -Real.log (62500000000 / 109143645821) ∧
    -Real.log (62500000000 / 109143645821) ≤ (55749831 / 100000000) := by
  have h := checkLog_sound (w := (46643645821 / 171643645821)) (n := 12)
    (lo := (557498309 / 1000000000)) (hi := (55749831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109143645821 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109143645821 / 62500000000) = 1/(62500000000 / 109143645821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (557498309 / 1000000000) (55749831 / 100000000) (Real.log (109143645821 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (109143645821 / 62500000000) = -Real.log (62500000000 / 109143645821) := by
    rw [show ((109143645821 / 62500000000) : ℝ) = ((62500000000 / 109143645821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (39682253 / 100000000) ≤ -Real.log (500000000000 / 743545996279) ∧
    -Real.log (500000000000 / 743545996279) ≤ (396822531 / 1000000000) := by
  have h := checkLog_sound (w := (243545996279 / 1243545996279)) (n := 12)
    (lo := (39682253 / 100000000)) (hi := (396822531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743545996279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743545996279 / 500000000000) = 1/(500000000000 / 743545996279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (39682253 / 100000000) (396822531 / 1000000000) (Real.log (743545996279 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (743545996279 / 500000000000) = -Real.log (500000000000 / 743545996279) := by
    rw [show ((743545996279 / 500000000000) : ℝ) = ((500000000000 / 743545996279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (19874197 / 50000000) ≤ -Real.log (250000000000 / 372018974067) ∧
    -Real.log (250000000000 / 372018974067) ≤ (397483941 / 1000000000) := by
  have h := checkLog_sound (w := (122018974067 / 622018974067)) (n := 12)
    (lo := (19874197 / 50000000)) (hi := (397483941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372018974067 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372018974067 / 250000000000) = 1/(250000000000 / 372018974067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (19874197 / 50000000) (397483941 / 1000000000) (Real.log (372018974067 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (372018974067 / 250000000000) = -Real.log (250000000000 / 372018974067) := by
    rw [show ((372018974067 / 250000000000) : ℝ) = ((250000000000 / 372018974067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1226283 / 31250000) ≤ -Real.log (240379725111 / 250000000000) ∧
    -Real.log (240379725111 / 250000000000) ≤ (39241057 / 1000000000) := by
  have h := checkLog_sound (w := (9620274889 / 490379725111)) (n := 12)
    (lo := (1226283 / 31250000)) (hi := (39241057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240379725111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240379725111) = 1/(240379725111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-39241057 / 1000000000) (-1226283 / 31250000) (Real.log (240379725111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7822283 / 200000000) ≤ -Real.log (15025680639 / 15625000000) ∧
    -Real.log (15025680639 / 15625000000) ≤ (4888927 / 125000000) := by
  have h := checkLog_sound (w := (599319361 / 30650680639)) (n := 12)
    (lo := (7822283 / 200000000)) (hi := (4888927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15025680639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15025680639) = 1/(15025680639 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4888927 / 125000000) (-7822283 / 200000000) (Real.log (15025680639 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell224
