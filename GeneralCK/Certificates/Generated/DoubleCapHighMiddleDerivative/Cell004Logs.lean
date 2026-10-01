import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell004
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

theorem reflection_log_1_neg : (225484559 / 1000000000) ≤ -Real.log (1024 / 1283) ∧
    -Real.log (1024 / 1283) ≤ (2818557 / 12500000) := by
  have h := checkLog_sound (w := (259 / 2307)) (n := 12)
    (lo := (225484559 / 1000000000)) (hi := (2818557 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 1024) = 1/(1024 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (225484559 / 1000000000) (2818557 / 12500000) (Real.log (1283 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1283 / 1024) = -Real.log (1024 / 1283) := by
    rw [show ((1283 / 1024) : ℝ) = ((1024 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291595971 / 1000000000) ≤ -Real.log (765 / 1024) ∧
    -Real.log (765 / 1024) ≤ (72898993 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1789)) (n := 12)
    (lo := (291595971 / 1000000000)) (hi := (72898993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 765) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 765) = 1/(765 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72898993 / 250000000) (-291595971 / 1000000000) (Real.log (765 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45003359 / 200000000) ≤ -Real.log (1280 / 1603) ∧
    -Real.log (1280 / 1603) ≤ (56254199 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2883)) (n := 12)
    (lo := (45003359 / 200000000)) (hi := (56254199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603 / 1280) = 1/(1280 / 1603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45003359 / 200000000) (56254199 / 250000000) (Real.log (1603 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1603 / 1280) = -Real.log (1280 / 1603) := by
    rw [show ((1603 / 1280) : ℝ) = ((1280 / 1603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58162393 / 200000000) ≤ -Real.log (957 / 1280) ∧
    -Real.log (957 / 1280) ≤ (145405983 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 957) = 1/(957 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-145405983 / 500000000) (-58162393 / 200000000) (Real.log (957 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32919753 / 200000000) ≤ -Real.log (25000 / 29473) ∧
    -Real.log (25000 / 29473) ≤ (82299383 / 500000000) := by
  have h := checkLog_sound (w := (4473 / 54473)) (n := 12)
    (lo := (32919753 / 200000000)) (hi := (82299383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29473 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29473 / 25000) = 1/(25000 / 29473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32919753 / 200000000) (82299383 / 500000000) (Real.log (29473 / 25000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (29473 / 25000) = -Real.log (25000 / 29473) := by
    rw [show ((29473 / 25000) : ℝ) = ((25000 / 29473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (49283683 / 250000000) ≤ -Real.log (20527 / 25000) ∧
    -Real.log (20527 / 25000) ≤ (197134733 / 1000000000) := by
  have h := checkLog_sound (w := (4473 / 45527)) (n := 12)
    (lo := (49283683 / 250000000)) (hi := (197134733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20527) = 1/(20527 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-197134733 / 1000000000) (-49283683 / 250000000) (Real.log (20527 / 25000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322176 / 1953125) ≤ -Real.log (1000000 / 1179339) ∧
    -Real.log (1000000 / 1179339) ≤ (164954113 / 1000000000) := by
  have h := checkLog_sound (w := (179339 / 2179339)) (n := 12)
    (lo := (322176 / 1953125)) (hi := (164954113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179339 / 1000000) = 1/(1000000 / 1179339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322176 / 1953125) (164954113 / 1000000000) (Real.log (1179339 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1179339 / 1000000) = -Real.log (1000000 / 1179339) := by
    rw [show ((1179339 / 1000000) : ℝ) = ((1000000 / 1179339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39529033 / 200000000) ≤ -Real.log (820661 / 1000000) ∧
    -Real.log (820661 / 1000000) ≤ (98822583 / 500000000) := by
  have h := checkLog_sound (w := (179339 / 1820661)) (n := 12)
    (lo := (39529033 / 200000000)) (hi := (98822583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820661) = 1/(820661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-98822583 / 500000000) (-39529033 / 200000000) (Real.log (820661 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120134047 / 1000000000) ≤ -Real.log (31250 / 35239) ∧
    -Real.log (31250 / 35239) ≤ (3754189 / 31250000) := by
  have h := checkLog_sound (w := (3989 / 66489)) (n := 12)
    (lo := (120134047 / 1000000000)) (hi := (3754189 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35239 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35239 / 31250) = 1/(31250 / 35239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120134047 / 1000000000) (3754189 / 31250000) (Real.log (35239 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (35239 / 31250) = -Real.log (31250 / 35239) := by
    rw [show ((35239 / 31250) : ℝ) = ((31250 / 35239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (68281133 / 500000000) ≤ -Real.log (27261 / 31250) ∧
    -Real.log (27261 / 31250) ≤ (136562267 / 1000000000) := by
  have h := checkLog_sound (w := (3989 / 58511)) (n := 12)
    (lo := (68281133 / 500000000)) (hi := (136562267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27261) = 1/(27261 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-136562267 / 1000000000) (-68281133 / 500000000) (Real.log (27261 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60201799 / 500000000) ≤ -Real.log (62500 / 70497) ∧
    -Real.log (62500 / 70497) ≤ (120403599 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 132997)) (n := 12)
    (lo := (60201799 / 500000000)) (hi := (120403599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70497 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70497 / 62500) = 1/(62500 / 70497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60201799 / 500000000) (120403599 / 1000000000) (Real.log (70497 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (70497 / 62500) = -Real.log (62500 / 70497) := by
    rw [show ((70497 / 62500) : ℝ) = ((62500 / 70497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13691081 / 100000000) ≤ -Real.log (54503 / 62500) ∧
    -Real.log (54503 / 62500) ≤ (136910811 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 117003)) (n := 12)
    (lo := (13691081 / 100000000)) (hi := (136910811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54503) = 1/(54503 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-136910811 / 1000000000) (-13691081 / 100000000) (Real.log (54503 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (515828761 / 1000000000) ≤ -Real.log (10000000000 / 16750261233) ∧
    -Real.log (10000000000 / 16750261233) ≤ (257914381 / 500000000) := by
  have h := checkLog_sound (w := (6750261233 / 26750261233)) (n := 12)
    (lo := (515828761 / 1000000000)) (hi := (257914381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16750261233 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16750261233 / 10000000000) = 1/(10000000000 / 16750261233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (515828761 / 1000000000) (257914381 / 500000000) (Real.log (16750261233 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (16750261233 / 10000000000) = -Real.log (10000000000 / 16750261233) := by
    rw [show ((16750261233 / 10000000000) : ℝ) = ((10000000000 / 16750261233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51708053 / 100000000) ≤ -Real.log (31250000000 / 52410130719) ∧
    -Real.log (31250000000 / 52410130719) ≤ (517080531 / 1000000000) := by
  have h := checkLog_sound (w := (21160130719 / 83660130719)) (n := 12)
    (lo := (51708053 / 100000000)) (hi := (517080531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52410130719 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52410130719 / 31250000000) = 1/(31250000000 / 52410130719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (51708053 / 100000000) (517080531 / 1000000000) (Real.log (52410130719 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (52410130719 / 31250000000) = -Real.log (31250000000 / 52410130719) := by
    rw [show ((52410130719 / 31250000000) : ℝ) = ((31250000000 / 52410130719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (361733497 / 1000000000) ≤ -Real.log (500000000000 / 717908121011) ∧
    -Real.log (500000000000 / 717908121011) ≤ (180866749 / 500000000) := by
  have h := checkLog_sound (w := (217908121011 / 1217908121011)) (n := 12)
    (lo := (361733497 / 1000000000)) (hi := (180866749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717908121011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717908121011 / 500000000000) = 1/(500000000000 / 717908121011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (361733497 / 1000000000) (180866749 / 500000000) (Real.log (717908121011 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (717908121011 / 500000000000) = -Real.log (500000000000 / 717908121011) := by
    rw [show ((717908121011 / 500000000000) : ℝ) = ((500000000000 / 717908121011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (362599277 / 1000000000) ≤ -Real.log (500000000000 / 718529941109) ∧
    -Real.log (500000000000 / 718529941109) ≤ (181299639 / 500000000) := by
  have h := checkLog_sound (w := (218529941109 / 1218529941109)) (n := 12)
    (lo := (362599277 / 1000000000)) (hi := (181299639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718529941109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718529941109 / 500000000000) = 1/(500000000000 / 718529941109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (362599277 / 1000000000) (181299639 / 500000000) (Real.log (718529941109 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (718529941109 / 500000000000) = -Real.log (500000000000 / 718529941109) := by
    rw [show ((718529941109 / 500000000000) : ℝ) = ((500000000000 / 718529941109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (128348157 / 500000000) ≤ -Real.log (250000000000 / 323163126811) ∧
    -Real.log (250000000000 / 323163126811) ≤ (51339263 / 200000000) := by
  have h := checkLog_sound (w := (73163126811 / 573163126811)) (n := 12)
    (lo := (128348157 / 500000000)) (hi := (51339263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323163126811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323163126811 / 250000000000) = 1/(250000000000 / 323163126811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (128348157 / 500000000) (51339263 / 200000000) (Real.log (323163126811 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (323163126811 / 250000000000) = -Real.log (250000000000 / 323163126811) := by
    rw [show ((323163126811 / 250000000000) : ℝ) = ((250000000000 / 323163126811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257314409 / 1000000000) ≤ -Real.log (500000000000 / 646725868301) ∧
    -Real.log (500000000000 / 646725868301) ≤ (25731441 / 100000000) := by
  have h := checkLog_sound (w := (146725868301 / 1146725868301)) (n := 12)
    (lo := (257314409 / 1000000000)) (hi := (25731441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646725868301 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646725868301 / 500000000000) = 1/(500000000000 / 646725868301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257314409 / 1000000000) (25731441 / 100000000) (Real.log (646725868301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (646725868301 / 500000000000) = -Real.log (500000000000 / 646725868301) := by
    rw [show ((646725868301 / 500000000000) : ℝ) = ((500000000000 / 646725868301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16507211 / 1000000000) ≤ -Real.log (3842297991 / 3906250000) ∧
    -Real.log (3842297991 / 3906250000) ≤ (4126803 / 250000000) := by
  have h := checkLog_sound (w := (63952009 / 7748547991)) (n := 12)
    (lo := (16507211 / 1000000000)) (hi := (4126803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3842297991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3842297991) = 1/(3842297991 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4126803 / 250000000) (-16507211 / 1000000000) (Real.log (3842297991 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16428219 / 1000000000) ≤ -Real.log (960650379 / 976562500) ∧
    -Real.log (960650379 / 976562500) ≤ (821411 / 50000000) := by
  have h := checkLog_sound (w := (15912121 / 1937212879)) (n := 12)
    (lo := (16428219 / 1000000000)) (hi := (821411 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 960650379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 960650379) = 1/(960650379 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-821411 / 50000000) (-16428219 / 1000000000) (Real.log (960650379 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell004
