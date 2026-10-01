import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0028
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

theorem reflection_log_1_neg : (392094873 / 1000000000) ≤ -Real.log (2560 / 3789) ∧
    -Real.log (2560 / 3789) ≤ (196047437 / 500000000) := by
  have h := checkLog_sound (w := (1229 / 6349)) (n := 12)
    (lo := (392094873 / 1000000000)) (hi := (196047437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3789 / 2560) = 1/(2560 / 3789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (392094873 / 1000000000) (196047437 / 500000000) (Real.log (3789 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3789 / 2560) = -Real.log (2560 / 3789) := by
    rw [show ((3789 / 2560) : ℝ) = ((2560 / 3789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (654076719 / 1000000000) ≤ -Real.log (1331 / 2560) ∧
    -Real.log (1331 / 2560) ≤ (8175959 / 12500000) := by
  have h := checkLog_sound (w := (1229 / 3891)) (n := 12)
    (lo := (654076719 / 1000000000)) (hi := (8175959 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1331) = 1/(1331 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8175959 / 12500000) (-654076719 / 1000000000) (Real.log (1331 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (195651397 / 500000000) ≤ -Real.log (1280 / 1893) ∧
    -Real.log (1280 / 1893) ≤ (78260559 / 200000000) := by
  have h := checkLog_sound (w := (613 / 3173)) (n := 12)
    (lo := (195651397 / 500000000)) (hi := (78260559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1280) = 1/(1280 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (195651397 / 500000000) (78260559 / 200000000) (Real.log (1893 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1893 / 1280) = -Real.log (1280 / 1893) := by
    rw [show ((1893 / 1280) : ℝ) = ((1280 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65182531 / 100000000) ≤ -Real.log (667 / 1280) ∧
    -Real.log (667 / 1280) ≤ (651825311 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1947)) (n := 12)
    (lo := (65182531 / 100000000)) (hi := (651825311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 667) = 1/(667 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-651825311 / 1000000000) (-65182531 / 100000000) (Real.log (667 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (673024189 / 1000000000) ≤ -Real.log (1280 / 2509) ∧
    -Real.log (1280 / 2509) ≤ (67302419 / 100000000) := by
  have h := checkLog_sound (w := (1229 / 3789)) (n := 12)
    (lo := (673024189 / 1000000000)) (hi := (67302419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1280) = 1/(1280 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (673024189 / 1000000000) (67302419 / 100000000) (Real.log (2509 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2509 / 1280) = -Real.log (1280 / 2509) := by
    rw [show ((2509 / 1280) : ℝ) = ((1280 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3222789721 / 1000000000) ≤ -Real.log (51 / 1280) ∧
    -Real.log (51 / 1280) ≤ (1611394863 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 51) = 1/(51 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1611394863 / 500000000) (-3222789721 / 1000000000) (Real.log (51 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (335913889 / 500000000) ≤ -Real.log (640 / 1253) ∧
    -Real.log (640 / 1253) ≤ (671827779 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 1893)) (n := 12)
    (lo := (335913889 / 500000000)) (hi := (671827779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253 / 640) = 1/(640 / 1253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (335913889 / 500000000) (671827779 / 1000000000) (Real.log (1253 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1253 / 640) = -Real.log (640 / 1253) := by
    rw [show ((1253 / 640) : ℝ) = ((640 / 1253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (791407827 / 250000000) ≤ -Real.log (27 / 640) ∧
    -Real.log (27 / 640) ≤ (3165631313 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 27) = 1/(27 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3165631313 / 1000000000) (-791407827 / 250000000) (Real.log (27 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (546920109 / 1000000000) ≤ -Real.log (1000000 / 1727923) ∧
    -Real.log (1000000 / 1727923) ≤ (54692011 / 100000000) := by
  have h := checkLog_sound (w := (727923 / 2727923)) (n := 12)
    (lo := (546920109 / 1000000000)) (hi := (54692011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1727923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1727923 / 1000000) = 1/(1000000 / 1727923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (546920109 / 1000000000) (54692011 / 100000000) (Real.log (1727923 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1727923 / 1000000) = -Real.log (1000000 / 1727923) := by
    rw [show ((1727923 / 1000000) : ℝ) = ((1000000 / 1727923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1301670163 / 1000000000) ≤ -Real.log (272077 / 1000000) ∧
    -Real.log (272077 / 1000000) ≤ (260334033 / 200000000) := by
  have h := checkLog_sound (w := (227923 / 772077)) (n := 12)
    (lo := (608522983 / 1000000000)) (hi := (76065373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 272077) = 1/(272077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-260334033 / 200000000) (-1301670163 / 1000000000) (Real.log (272077 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (274167051 / 500000000) ≤ -Real.log (15625 / 27037) ∧
    -Real.log (15625 / 27037) ≤ (548334103 / 1000000000) := by
  have h := checkLog_sound (w := (5706 / 21331)) (n := 12)
    (lo := (274167051 / 500000000)) (hi := (548334103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27037 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27037 / 15625) = 1/(15625 / 27037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (274167051 / 500000000) (548334103 / 1000000000) (Real.log (27037 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (27037 / 15625) = -Real.log (15625 / 27037) := by
    rw [show ((27037 / 15625) : ℝ) = ((15625 / 27037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (327674303 / 250000000) ≤ -Real.log (4213 / 15625) ∧
    -Real.log (4213 / 15625) ≤ (655348607 / 500000000) := by
  have h := checkLog_sound (w := (7199 / 24051)) (n := 12)
    (lo := (38596877 / 62500000)) (hi := (617550033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8426) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 8426) = 1/(4213 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-655348607 / 500000000) (-327674303 / 250000000) (Real.log (4213 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (235438811 / 500000000) ≤ -Real.log (1000000 / 1601399) ∧
    -Real.log (1000000 / 1601399) ≤ (470877623 / 1000000000) := by
  have h := checkLog_sound (w := (601399 / 2601399)) (n := 12)
    (lo := (235438811 / 500000000)) (hi := (470877623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1601399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1601399 / 1000000) = 1/(1000000 / 1601399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (235438811 / 500000000) (470877623 / 1000000000) (Real.log (1601399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1601399 / 1000000) = -Real.log (1000000 / 1601399) := by
    rw [show ((1601399 / 1000000) : ℝ) = ((1000000 / 1601399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (919794361 / 1000000000) ≤ -Real.log (398601 / 1000000) ∧
    -Real.log (398601 / 1000000) ≤ (919794363 / 1000000000) := by
  have h := checkLog_sound (w := (101399 / 898601)) (n := 12)
    (lo := (226647181 / 1000000000)) (hi := (113323591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 398601) = 1/(398601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-919794363 / 1000000000) (-919794361 / 1000000000) (Real.log (398601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (472542279 / 1000000000) ≤ -Real.log (1000000 / 1604067) ∧
    -Real.log (1000000 / 1604067) ≤ (11813557 / 25000000) := by
  have h := checkLog_sound (w := (604067 / 2604067)) (n := 12)
    (lo := (472542279 / 1000000000)) (hi := (11813557 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1604067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1604067 / 1000000) = 1/(1000000 / 1604067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (472542279 / 1000000000) (11813557 / 25000000) (Real.log (1604067 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1604067 / 1000000) = -Real.log (1000000 / 1604067) := by
    rw [show ((1604067 / 1000000) : ℝ) = ((1000000 / 1604067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (926510273 / 1000000000) ≤ -Real.log (395933 / 1000000) ∧
    -Real.log (395933 / 1000000) ≤ (37060411 / 40000000) := by
  have h := checkLog_sound (w := (104067 / 895933)) (n := 12)
    (lo := (233363093 / 1000000000)) (hi := (116681547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 395933) = 1/(395933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-37060411 / 40000000) (-926510273 / 1000000000) (Real.log (395933 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (28884223 / 15625000) ≤ -Real.log (500000000000 / 3175430117209) ∧
    -Real.log (500000000000 / 3175430117209) ≤ (73943611 / 40000000) := by
  have h := checkLog_sound (w := (1175430117209 / 5175430117209)) (n := 12)
    (lo := (57786989 / 125000000)) (hi := (462295913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3175430117209 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3175430117209 / 2000000000000) = 1/(500000000000 / 3175430117209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28884223 / 15625000) (73943611 / 40000000) (Real.log (3175430117209 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3175430117209 / 500000000000) = -Real.log (500000000000 / 3175430117209) := by
    rw [show ((3175430117209 / 500000000000) : ℝ) = ((500000000000 / 3175430117209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (929515657 / 500000000) ≤ -Real.log (3125000000 / 20054741277) ∧
    -Real.log (3125000000 / 20054741277) ≤ (1859031317 / 1000000000) := by
  have h := checkLog_sound (w := (7554741277 / 32554741277)) (n := 12)
    (lo := (236368477 / 500000000)) (hi := (94547391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20054741277 / 12500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20054741277 / 12500000000) = 1/(3125000000 / 20054741277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (929515657 / 500000000) (1859031317 / 1000000000) (Real.log (20054741277 / 3125000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20054741277 / 3125000000) = -Real.log (3125000000 / 20054741277) := by
    rw [show ((20054741277 / 3125000000) : ℝ) = ((3125000000 / 20054741277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1390671983 / 1000000000) ≤ -Real.log (500000000000 / 2008774438599) ∧
    -Real.log (500000000000 / 2008774438599) ≤ (695335993 / 500000000) := by
  have h := checkLog_sound (w := (8774438599 / 4008774438599)) (n := 12)
    (lo := (4377623 / 1000000000)) (hi := (547203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2008774438599 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2008774438599 / 2000000000000) = 1/(500000000000 / 2008774438599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1390671983 / 1000000000) (695335993 / 500000000) (Real.log (2008774438599 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2008774438599 / 500000000000) = -Real.log (500000000000 / 2008774438599) := by
    rw [show ((2008774438599 / 500000000000) : ℝ) = ((500000000000 / 2008774438599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1399052551 / 1000000000) ≤ -Real.log (250000000000 / 1012839924937) ∧
    -Real.log (250000000000 / 1012839924937) ≤ (699526277 / 500000000) := by
  have h := checkLog_sound (w := (12839924937 / 2012839924937)) (n := 12)
    (lo := (12758191 / 1000000000)) (hi := (797387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1012839924937 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1012839924937 / 1000000000000) = 1/(250000000000 / 1012839924937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1399052551 / 1000000000) (699526277 / 500000000) (Real.log (1012839924937 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1012839924937 / 250000000000) = -Real.log (250000000000 / 1012839924937) := by
    rw [show ((1012839924937 / 250000000000) : ℝ) = ((250000000000 / 1012839924937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0028
