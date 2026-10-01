import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell163
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

theorem reflection_log_1_neg : (297206879 / 1000000000) ≤ -Real.log (1280 / 1723) ∧
    -Real.log (1280 / 1723) ≤ (1857543 / 6250000) := by
  have h := checkLog_sound (w := (443 / 3003)) (n := 12)
    (lo := (297206879 / 1000000000)) (hi := (1857543 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723 / 1280) = 1/(1280 / 1723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (297206879 / 1000000000) (1857543 / 6250000) (Real.log (1723 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1723 / 1280) = -Real.log (1280 / 1723) := by
    rw [show ((1723 / 1280) : ℝ) = ((1280 / 1723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (212395643 / 500000000) ≤ -Real.log (837 / 1280) ∧
    -Real.log (837 / 1280) ≤ (424791287 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2117)) (n := 12)
    (lo := (212395643 / 500000000)) (hi := (424791287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 837) = 1/(837 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-424791287 / 1000000000) (-212395643 / 500000000) (Real.log (837 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (296771497 / 1000000000) ≤ -Real.log (5120 / 6889) ∧
    -Real.log (5120 / 6889) ≤ (148385749 / 500000000) := by
  have h := checkLog_sound (w := (1769 / 12009)) (n := 12)
    (lo := (296771497 / 1000000000)) (hi := (148385749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6889 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6889 / 5120) = 1/(5120 / 6889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (296771497 / 1000000000) (148385749 / 500000000) (Real.log (6889 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6889 / 5120) = -Real.log (5120 / 6889) := by
    rw [show ((6889 / 5120) : ℝ) = ((5120 / 6889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (42389563 / 100000000) ≤ -Real.log (3351 / 5120) ∧
    -Real.log (3351 / 5120) ≤ (423895631 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 8471)) (n := 12)
    (lo := (42389563 / 100000000)) (hi := (423895631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3351) = 1/(3351 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-423895631 / 1000000000) (-42389563 / 100000000) (Real.log (3351 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (219609313 / 1000000000) ≤ -Real.log (100000 / 124559) ∧
    -Real.log (100000 / 124559) ≤ (109804657 / 500000000) := by
  have h := checkLog_sound (w := (24559 / 224559)) (n := 12)
    (lo := (219609313 / 1000000000)) (hi := (109804657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124559 / 100000) = 1/(100000 / 124559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (219609313 / 1000000000) (109804657 / 500000000) (Real.log (124559 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (124559 / 100000) = -Real.log (100000 / 124559) := by
    rw [show ((124559 / 100000) : ℝ) = ((100000 / 124559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70454823 / 250000000) ≤ -Real.log (75441 / 100000) ∧
    -Real.log (75441 / 100000) ≤ (281819293 / 1000000000) := by
  have h := checkLog_sound (w := (24559 / 175441)) (n := 12)
    (lo := (70454823 / 250000000)) (hi := (281819293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75441) = 1/(75441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-281819293 / 1000000000) (-70454823 / 250000000) (Real.log (75441 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (219948051 / 1000000000) ≤ -Real.log (250000 / 311503) ∧
    -Real.log (250000 / 311503) ≤ (54987013 / 250000000) := by
  have h := checkLog_sound (w := (61503 / 561503)) (n := 12)
    (lo := (219948051 / 1000000000)) (hi := (54987013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311503 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311503 / 250000) = 1/(250000 / 311503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (219948051 / 1000000000) (54987013 / 250000000) (Real.log (311503 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (311503 / 250000) = -Real.log (250000 / 311503) := by
    rw [show ((311503 / 250000) : ℝ) = ((250000 / 311503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141189413 / 500000000) ≤ -Real.log (188497 / 250000) ∧
    -Real.log (188497 / 250000) ≤ (282378827 / 1000000000) := by
  have h := checkLog_sound (w := (61503 / 438497)) (n := 12)
    (lo := (141189413 / 500000000)) (hi := (282378827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188497) = 1/(188497 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282378827 / 1000000000) (-141189413 / 500000000) (Real.log (188497 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40659143 / 250000000) ≤ -Real.log (1000000 / 1176609) ∧
    -Real.log (1000000 / 1176609) ≤ (162636573 / 1000000000) := by
  have h := checkLog_sound (w := (176609 / 2176609)) (n := 12)
    (lo := (40659143 / 250000000)) (hi := (162636573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176609 / 1000000) = 1/(1000000 / 1176609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40659143 / 250000000) (162636573 / 1000000000) (Real.log (1176609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1176609 / 1000000) = -Real.log (1000000 / 1176609) := by
    rw [show ((1176609 / 1000000) : ℝ) = ((1000000 / 1176609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194324099 / 1000000000) ≤ -Real.log (823391 / 1000000) ∧
    -Real.log (823391 / 1000000) ≤ (1943241 / 10000000) := by
  have h := checkLog_sound (w := (176609 / 1823391)) (n := 12)
    (lo := (194324099 / 1000000000)) (hi := (1943241 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823391) = 1/(823391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1943241 / 10000000) (-194324099 / 1000000000) (Real.log (823391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32580681 / 200000000) ≤ -Real.log (1000000 / 1176923) ∧
    -Real.log (1000000 / 1176923) ≤ (81451703 / 500000000) := by
  have h := checkLog_sound (w := (176923 / 2176923)) (n := 12)
    (lo := (32580681 / 200000000)) (hi := (81451703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176923 / 1000000) = 1/(1000000 / 1176923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32580681 / 200000000) (81451703 / 500000000) (Real.log (1176923 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1176923 / 1000000) = -Real.log (1000000 / 1176923) := by
    rw [show ((1176923 / 1000000) : ℝ) = ((1000000 / 1176923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (97352761 / 500000000) ≤ -Real.log (823077 / 1000000) ∧
    -Real.log (823077 / 1000000) ≤ (194705523 / 1000000000) := by
  have h := checkLog_sound (w := (176923 / 1823077)) (n := 12)
    (lo := (97352761 / 500000000)) (hi := (194705523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823077) = 1/(823077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-194705523 / 1000000000) (-97352761 / 500000000) (Real.log (823077 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (720667127 / 1000000000) ≤ -Real.log (50000000000 / 102790211877) ∧
    -Real.log (50000000000 / 102790211877) ≤ (720667129 / 1000000000) := by
  have h := checkLog_sound (w := (2790211877 / 202790211877)) (n := 12)
    (lo := (27519947 / 1000000000)) (hi := (6879987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102790211877 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102790211877 / 100000000000) = 1/(50000000000 / 102790211877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (720667127 / 1000000000) (720667129 / 1000000000) (Real.log (102790211877 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102790211877 / 50000000000) = -Real.log (50000000000 / 102790211877) := by
    rw [show ((102790211877 / 50000000000) : ℝ) = ((50000000000 / 102790211877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144399633 / 200000000) ≤ -Real.log (500000000000 / 1029271206691) ∧
    -Real.log (500000000000 / 1029271206691) ≤ (721998167 / 1000000000) := by
  have h := checkLog_sound (w := (29271206691 / 2029271206691)) (n := 12)
    (lo := (5770197 / 200000000)) (hi := (14425493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029271206691 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1029271206691 / 1000000000000) = 1/(500000000000 / 1029271206691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (144399633 / 200000000) (721998167 / 1000000000) (Real.log (1029271206691 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1029271206691 / 500000000000) = -Real.log (500000000000 / 1029271206691) := by
    rw [show ((1029271206691 / 500000000000) : ℝ) = ((500000000000 / 1029271206691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (100285721 / 200000000) ≤ -Real.log (250000000000 / 412769581527) ∧
    -Real.log (250000000000 / 412769581527) ≤ (250714303 / 500000000) := by
  have h := checkLog_sound (w := (162769581527 / 662769581527)) (n := 12)
    (lo := (100285721 / 200000000)) (hi := (250714303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412769581527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412769581527 / 250000000000) = 1/(250000000000 / 412769581527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100285721 / 200000000) (250714303 / 500000000) (Real.log (412769581527 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (412769581527 / 250000000000) = -Real.log (250000000000 / 412769581527) := by
    rw [show ((412769581527 / 250000000000) : ℝ) = ((250000000000 / 412769581527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (502326877 / 1000000000) ≤ -Real.log (500000000000 / 826281054871) ∧
    -Real.log (500000000000 / 826281054871) ≤ (251163439 / 500000000) := by
  have h := checkLog_sound (w := (326281054871 / 1326281054871)) (n := 12)
    (lo := (502326877 / 1000000000)) (hi := (251163439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826281054871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826281054871 / 500000000000) = 1/(500000000000 / 826281054871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (502326877 / 1000000000) (251163439 / 500000000) (Real.log (826281054871 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (826281054871 / 500000000000) = -Real.log (500000000000 / 826281054871) := by
    rw [show ((826281054871 / 500000000000) : ℝ) = ((500000000000 / 826281054871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (11155021 / 31250000) ≤ -Real.log (500000000000 / 714489835327) ∧
    -Real.log (500000000000 / 714489835327) ≤ (356960673 / 1000000000) := by
  have h := checkLog_sound (w := (214489835327 / 1214489835327)) (n := 12)
    (lo := (11155021 / 31250000)) (hi := (356960673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714489835327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714489835327 / 500000000000) = 1/(500000000000 / 714489835327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (11155021 / 31250000) (356960673 / 1000000000) (Real.log (714489835327 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714489835327 / 500000000000) = -Real.log (500000000000 / 714489835327) := by
    rw [show ((714489835327 / 500000000000) : ℝ) = ((500000000000 / 714489835327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11175279 / 31250000) ≤ -Real.log (250000000000 / 357476578741) ∧
    -Real.log (250000000000 / 357476578741) ≤ (357608929 / 1000000000) := by
  have h := checkLog_sound (w := (107476578741 / 607476578741)) (n := 12)
    (lo := (11175279 / 31250000)) (hi := (357608929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357476578741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357476578741 / 250000000000) = 1/(250000000000 / 357476578741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11175279 / 31250000) (357608929 / 1000000000) (Real.log (357476578741 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (357476578741 / 250000000000) = -Real.log (250000000000 / 357476578741) := by
    rw [show ((357476578741 / 250000000000) : ℝ) = ((250000000000 / 357476578741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7950529 / 250000000) ≤ -Real.log (968698252071 / 1000000000000) ∧
    -Real.log (968698252071 / 1000000000000) ≤ (31802117 / 1000000000) := by
  have h := checkLog_sound (w := (31301747929 / 1968698252071)) (n := 12)
    (lo := (7950529 / 250000000)) (hi := (31802117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968698252071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968698252071) = 1/(968698252071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31802117 / 1000000000) (-7950529 / 250000000) (Real.log (968698252071 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31687527 / 1000000000) ≤ -Real.log (968809261119 / 1000000000000) ∧
    -Real.log (968809261119 / 1000000000000) ≤ (3960941 / 125000000) := by
  have h := checkLog_sound (w := (31190738881 / 1968809261119)) (n := 12)
    (lo := (31687527 / 1000000000)) (hi := (3960941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968809261119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968809261119) = 1/(968809261119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3960941 / 125000000) (-31687527 / 1000000000) (Real.log (968809261119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell163
