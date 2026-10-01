import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0473
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

theorem reflection_log_1_neg : (45793921 / 250000000) ≤ -Real.log (20480 / 24597) ∧
    -Real.log (20480 / 24597) ≤ (36635137 / 200000000) := by
  have h := checkLog_sound (w := (4117 / 45077)) (n := 12)
    (lo := (45793921 / 250000000)) (hi := (36635137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24597 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24597 / 20480) = 1/(20480 / 24597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (45793921 / 250000000) (36635137 / 200000000) (Real.log (24597 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24597 / 20480) = -Real.log (20480 / 24597) := by
    rw [show ((24597 / 20480) : ℝ) = ((20480 / 24597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224426111 / 1000000000) ≤ -Real.log (16363 / 20480) ∧
    -Real.log (16363 / 20480) ≤ (1753329 / 7812500) := by
  have h := checkLog_sound (w := (4117 / 36843)) (n := 12)
    (lo := (224426111 / 1000000000)) (hi := (1753329 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16363) = 1/(16363 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1753329 / 7812500) (-224426111 / 1000000000) (Real.log (16363 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18305371 / 100000000) ≤ -Real.log (10240 / 12297) ∧
    -Real.log (10240 / 12297) ≤ (183053711 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 22537)) (n := 12)
    (lo := (18305371 / 100000000)) (hi := (183053711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 10240) = 1/(10240 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18305371 / 100000000) (183053711 / 1000000000) (Real.log (12297 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12297 / 10240) = -Real.log (10240 / 12297) := by
    rw [show ((12297 / 10240) : ℝ) = ((10240 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56060697 / 250000000) ≤ -Real.log (8183 / 10240) ∧
    -Real.log (8183 / 10240) ≤ (224242789 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 18423)) (n := 12)
    (lo := (56060697 / 250000000)) (hi := (224242789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8183) = 1/(8183 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224242789 / 1000000000) (-56060697 / 250000000) (Real.log (8183 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42242001 / 125000000) ≤ -Real.log (10240 / 14357) ∧
    -Real.log (10240 / 14357) ≤ (337936009 / 1000000000) := by
  have h := checkLog_sound (w := (4117 / 24597)) (n := 12)
    (lo := (42242001 / 125000000)) (hi := (337936009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14357 / 10240) = 1/(10240 / 14357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42242001 / 125000000) (337936009 / 1000000000) (Real.log (14357 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14357 / 10240) = -Real.log (10240 / 14357) := by
    rw [show ((14357 / 10240) : ℝ) = ((10240 / 14357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (514249447 / 1000000000) ≤ -Real.log (6123 / 10240) ∧
    -Real.log (6123 / 10240) ≤ (64281181 / 125000000) := by
  have h := checkLog_sound (w := (4117 / 16363)) (n := 12)
    (lo := (514249447 / 1000000000)) (hi := (64281181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6123) = 1/(6123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-64281181 / 125000000) (-514249447 / 1000000000) (Real.log (6123 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (337727029 / 1000000000) ≤ -Real.log (5120 / 7177) ∧
    -Real.log (5120 / 7177) ≤ (33772703 / 100000000) := by
  have h := checkLog_sound (w := (2057 / 12297)) (n := 12)
    (lo := (337727029 / 1000000000)) (hi := (33772703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7177 / 5120) = 1/(5120 / 7177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (337727029 / 1000000000) (33772703 / 100000000) (Real.log (7177 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7177 / 5120) = -Real.log (5120 / 7177) := by
    rw [show ((7177 / 5120) : ℝ) = ((5120 / 7177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (513759611 / 1000000000) ≤ -Real.log (3063 / 5120) ∧
    -Real.log (3063 / 5120) ≤ (128439903 / 250000000) := by
  have h := checkLog_sound (w := (2057 / 8183)) (n := 12)
    (lo := (513759611 / 1000000000)) (hi := (128439903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3063) = 1/(3063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128439903 / 250000000) (-513759611 / 1000000000) (Real.log (3063 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125821187 / 500000000) ≤ -Real.log (125000 / 160767) ∧
    -Real.log (125000 / 160767) ≤ (2013139 / 8000000) := by
  have h := checkLog_sound (w := (35767 / 285767)) (n := 12)
    (lo := (125821187 / 500000000)) (hi := (2013139 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160767 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160767 / 125000) = 1/(125000 / 160767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125821187 / 500000000) (2013139 / 8000000) (Real.log (160767 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160767 / 125000) = -Real.log (125000 / 160767) := by
    rw [show ((160767 / 125000) : ℝ) = ((125000 / 160767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (33706281 / 100000000) ≤ -Real.log (89233 / 125000) ∧
    -Real.log (89233 / 125000) ≤ (337062811 / 1000000000) := by
  have h := checkLog_sound (w := (35767 / 214233)) (n := 12)
    (lo := (33706281 / 100000000)) (hi := (337062811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89233) = 1/(89233 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337062811 / 1000000000) (-33706281 / 100000000) (Real.log (89233 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251807973 / 1000000000) ≤ -Real.log (1000000 / 1286349) ∧
    -Real.log (1000000 / 1286349) ≤ (125903987 / 500000000) := by
  have h := checkLog_sound (w := (286349 / 2286349)) (n := 12)
    (lo := (251807973 / 1000000000)) (hi := (125903987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286349 / 1000000) = 1/(1000000 / 1286349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251807973 / 1000000000) (125903987 / 500000000) (Real.log (1286349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286349 / 1000000) = -Real.log (1000000 / 1286349) := by
    rw [show ((1286349 / 1000000) : ℝ) = ((1000000 / 1286349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337361231 / 1000000000) ≤ -Real.log (713651 / 1000000) ∧
    -Real.log (713651 / 1000000) ≤ (21085077 / 62500000) := by
  have h := checkLog_sound (w := (286349 / 1713651)) (n := 12)
    (lo := (337361231 / 1000000000)) (hi := (21085077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713651) = 1/(713651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21085077 / 62500000) (-337361231 / 1000000000) (Real.log (713651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23519521 / 125000000) ≤ -Real.log (500000 / 603511) ∧
    -Real.log (500000 / 603511) ≤ (188156169 / 1000000000) := by
  have h := checkLog_sound (w := (103511 / 1103511)) (n := 12)
    (lo := (23519521 / 125000000)) (hi := (188156169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603511 / 500000) = 1/(500000 / 603511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23519521 / 125000000) (188156169 / 1000000000) (Real.log (603511 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (603511 / 500000) = -Real.log (500000 / 603511) := by
    rw [show ((603511 / 500000) : ℝ) = ((500000 / 603511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1159799 / 5000000) ≤ -Real.log (396489 / 500000) ∧
    -Real.log (396489 / 500000) ≤ (231959801 / 1000000000) := by
  have h := checkLog_sound (w := (103511 / 896489)) (n := 12)
    (lo := (1159799 / 5000000)) (hi := (231959801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396489) = 1/(396489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231959801 / 1000000000) (-1159799 / 5000000) (Real.log (396489 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94145187 / 500000000) ≤ -Real.log (62500 / 75449) ∧
    -Real.log (62500 / 75449) ≤ (1506323 / 8000000) := by
  have h := checkLog_sound (w := (12949 / 137949)) (n := 12)
    (lo := (94145187 / 500000000)) (hi := (1506323 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75449 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75449 / 62500) = 1/(62500 / 75449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94145187 / 500000000) (1506323 / 8000000) (Real.log (75449 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75449 / 62500) = -Real.log (62500 / 75449) := by
    rw [show ((75449 / 62500) : ℝ) = ((62500 / 75449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (116082057 / 500000000) ≤ -Real.log (49551 / 62500) ∧
    -Real.log (49551 / 62500) ≤ (46432823 / 200000000) := by
  have h := checkLog_sound (w := (12949 / 112051)) (n := 12)
    (lo := (116082057 / 500000000)) (hi := (46432823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49551) = 1/(49551 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46432823 / 200000000) (-116082057 / 500000000) (Real.log (49551 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117741037 / 200000000) ≤ -Real.log (500000000000 / 900827048289) ∧
    -Real.log (500000000000 / 900827048289) ≤ (294352593 / 500000000) := by
  have h := checkLog_sound (w := (400827048289 / 1400827048289)) (n := 12)
    (lo := (117741037 / 200000000)) (hi := (294352593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900827048289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900827048289 / 500000000000) = 1/(500000000000 / 900827048289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117741037 / 200000000) (294352593 / 500000000) (Real.log (900827048289 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (900827048289 / 500000000000) = -Real.log (500000000000 / 900827048289) := by
    rw [show ((900827048289 / 500000000000) : ℝ) = ((500000000000 / 900827048289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (147292301 / 250000000) ≤ -Real.log (250000000000 / 450622573219) ∧
    -Real.log (250000000000 / 450622573219) ≤ (117833841 / 200000000) := by
  have h := checkLog_sound (w := (200622573219 / 700622573219)) (n := 12)
    (lo := (147292301 / 250000000)) (hi := (117833841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450622573219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450622573219 / 250000000000) = 1/(250000000000 / 450622573219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (147292301 / 250000000) (117833841 / 200000000) (Real.log (450622573219 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450622573219 / 250000000000) = -Real.log (250000000000 / 450622573219) := by
    rw [show ((450622573219 / 250000000000) : ℝ) = ((250000000000 / 450622573219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (420115969 / 1000000000) ≤ -Real.log (500000000000 / 761069033441) ∧
    -Real.log (500000000000 / 761069033441) ≤ (42011597 / 100000000) := by
  have h := checkLog_sound (w := (261069033441 / 1261069033441)) (n := 12)
    (lo := (420115969 / 1000000000)) (hi := (42011597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761069033441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761069033441 / 500000000000) = 1/(500000000000 / 761069033441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (420115969 / 1000000000) (42011597 / 100000000) (Real.log (761069033441 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761069033441 / 500000000000) = -Real.log (500000000000 / 761069033441) := by
    rw [show ((761069033441 / 500000000000) : ℝ) = ((500000000000 / 761069033441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (420454489 / 1000000000) ≤ -Real.log (500000000000 / 761326713891) ∧
    -Real.log (500000000000 / 761326713891) ≤ (42045449 / 100000000) := by
  have h := checkLog_sound (w := (261326713891 / 1261326713891)) (n := 12)
    (lo := (420454489 / 1000000000)) (hi := (42045449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761326713891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761326713891 / 500000000000) = 1/(500000000000 / 761326713891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (420454489 / 1000000000) (42045449 / 100000000) (Real.log (761326713891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (761326713891 / 500000000000) = -Real.log (500000000000 / 761326713891) := by
    rw [show ((761326713891 / 500000000000) : ℝ) = ((500000000000 / 761326713891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0473
