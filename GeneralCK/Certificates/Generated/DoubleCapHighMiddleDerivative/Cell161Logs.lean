import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell161
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

theorem reflection_log_1_neg : (11853437 / 40000000) ≤ -Real.log (2560 / 3443) ∧
    -Real.log (2560 / 3443) ≤ (148167963 / 500000000) := by
  have h := checkLog_sound (w := (883 / 6003)) (n := 12)
    (lo := (11853437 / 40000000)) (hi := (148167963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3443 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3443 / 2560) = 1/(2560 / 3443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11853437 / 40000000) (148167963 / 500000000) (Real.log (3443 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3443 / 2560) = -Real.log (2560 / 3443) := by
    rw [show ((3443 / 2560) : ℝ) = ((2560 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16920031 / 40000000) ≤ -Real.log (1677 / 2560) ∧
    -Real.log (1677 / 2560) ≤ (52875097 / 125000000) := by
  have h := checkLog_sound (w := (883 / 4237)) (n := 12)
    (lo := (16920031 / 40000000)) (hi := (52875097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1677) = 1/(1677 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-52875097 / 125000000) (-16920031 / 40000000) (Real.log (1677 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73975041 / 250000000) ≤ -Real.log (5120 / 6883) ∧
    -Real.log (5120 / 6883) ≤ (59180033 / 200000000) := by
  have h := checkLog_sound (w := (1763 / 12003)) (n := 12)
    (lo := (73975041 / 250000000)) (hi := (59180033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6883 / 5120) = 1/(5120 / 6883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73975041 / 250000000) (59180033 / 200000000) (Real.log (6883 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6883 / 5120) = -Real.log (5120 / 6883) := by
    rw [show ((6883 / 5120) : ℝ) = ((5120 / 6883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (422106721 / 1000000000) ≤ -Real.log (3357 / 5120) ∧
    -Real.log (3357 / 5120) ≤ (211053361 / 500000000) := by
  have h := checkLog_sound (w := (1763 / 8477)) (n := 12)
    (lo := (422106721 / 1000000000)) (hi := (211053361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3357) = 1/(3357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-211053361 / 500000000) (-422106721 / 1000000000) (Real.log (3357 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (218933099 / 1000000000) ≤ -Real.log (250000 / 311187) ∧
    -Real.log (250000 / 311187) ≤ (2189331 / 10000000) := by
  have h := checkLog_sound (w := (61187 / 561187)) (n := 12)
    (lo := (218933099 / 1000000000)) (hi := (2189331 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311187 / 250000) = 1/(250000 / 311187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (218933099 / 1000000000) (2189331 / 10000000) (Real.log (311187 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (311187 / 250000) = -Real.log (250000 / 311187) := by
    rw [show ((311187 / 250000) : ℝ) = ((250000 / 311187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28070381 / 100000000) ≤ -Real.log (188813 / 250000) ∧
    -Real.log (188813 / 250000) ≤ (280703811 / 1000000000) := by
  have h := checkLog_sound (w := (61187 / 438813)) (n := 12)
    (lo := (28070381 / 100000000)) (hi := (280703811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188813) = 1/(188813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280703811 / 1000000000) (-28070381 / 100000000) (Real.log (188813 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109636033 / 500000000) ≤ -Real.log (100000 / 124517) ∧
    -Real.log (100000 / 124517) ≤ (219272067 / 1000000000) := by
  have h := checkLog_sound (w := (24517 / 224517)) (n := 12)
    (lo := (109636033 / 500000000)) (hi := (219272067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124517 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124517 / 100000) = 1/(100000 / 124517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109636033 / 500000000) (219272067 / 1000000000) (Real.log (124517 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (124517 / 100000) = -Real.log (100000 / 124517) := by
    rw [show ((124517 / 100000) : ℝ) = ((100000 / 124517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (439473 / 1562500) ≤ -Real.log (75483 / 100000) ∧
    -Real.log (75483 / 100000) ≤ (281262721 / 1000000000) := by
  have h := checkLog_sound (w := (24517 / 175483)) (n := 12)
    (lo := (439473 / 1562500)) (hi := (281262721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75483) = 1/(75483 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-281262721 / 1000000000) (-439473 / 1562500) (Real.log (75483 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (162104393 / 1000000000) ≤ -Real.log (1000000 / 1175983) ∧
    -Real.log (1000000 / 1175983) ≤ (81052197 / 500000000) := by
  have h := checkLog_sound (w := (175983 / 2175983)) (n := 12)
    (lo := (162104393 / 1000000000)) (hi := (81052197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175983 / 1000000) = 1/(1000000 / 1175983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (162104393 / 1000000000) (81052197 / 500000000) (Real.log (1175983 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1175983 / 1000000) = -Real.log (1000000 / 1175983) := by
    rw [show ((1175983 / 1000000) : ℝ) = ((1000000 / 1175983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96782059 / 500000000) ≤ -Real.log (824017 / 1000000) ∧
    -Real.log (824017 / 1000000) ≤ (193564119 / 1000000000) := by
  have h := checkLog_sound (w := (175983 / 1824017)) (n := 12)
    (lo := (96782059 / 500000000)) (hi := (193564119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824017) = 1/(824017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-193564119 / 1000000000) (-96782059 / 500000000) (Real.log (824017 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20296421 / 125000000) ≤ -Real.log (1000000 / 1176297) ∧
    -Real.log (1000000 / 1176297) ≤ (162371369 / 1000000000) := by
  have h := checkLog_sound (w := (176297 / 2176297)) (n := 12)
    (lo := (20296421 / 125000000)) (hi := (162371369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176297 / 1000000) = 1/(1000000 / 1176297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20296421 / 125000000) (162371369 / 1000000000) (Real.log (1176297 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1176297 / 1000000) = -Real.log (1000000 / 1176297) := by
    rw [show ((1176297 / 1000000) : ℝ) = ((1000000 / 1176297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (775781 / 4000000) ≤ -Real.log (823703 / 1000000) ∧
    -Real.log (823703 / 1000000) ≤ (193945251 / 1000000000) := by
  have h := checkLog_sound (w := (176297 / 1823703)) (n := 12)
    (lo := (775781 / 4000000)) (hi := (193945251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823703) = 1/(823703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193945251 / 1000000000) (-775781 / 4000000) (Real.log (823703 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (179501721 / 250000000) ≤ -Real.log (125000000000 / 256292820971) ∧
    -Real.log (125000000000 / 256292820971) ≤ (359003443 / 500000000) := by
  have h := checkLog_sound (w := (6292820971 / 506292820971)) (n := 12)
    (lo := (3107463 / 125000000)) (hi := (4971941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256292820971 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256292820971 / 250000000000) = 1/(125000000000 / 256292820971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (179501721 / 250000000) (359003443 / 500000000) (Real.log (256292820971 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (256292820971 / 125000000000) = -Real.log (125000000000 / 256292820971) := by
    rw [show ((256292820971 / 125000000000) : ℝ) = ((125000000000 / 256292820971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7193367 / 10000000) ≤ -Real.log (62500000000 / 128316935003) ∧
    -Real.log (62500000000 / 128316935003) ≤ (359668351 / 500000000) := by
  have h := checkLog_sound (w := (3316935003 / 253316935003)) (n := 12)
    (lo := (327369 / 12500000)) (hi := (26189521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128316935003 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128316935003 / 125000000000) = 1/(62500000000 / 128316935003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (7193367 / 10000000) (359668351 / 500000000) (Real.log (128316935003 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (128316935003 / 62500000000) = -Real.log (62500000000 / 128316935003) := by
    rw [show ((128316935003 / 62500000000) : ℝ) = ((62500000000 / 128316935003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (49963691 / 100000000) ≤ -Real.log (125000000000 / 206015343223) ∧
    -Real.log (125000000000 / 206015343223) ≤ (499636911 / 1000000000) := by
  have h := checkLog_sound (w := (81015343223 / 331015343223)) (n := 12)
    (lo := (49963691 / 100000000)) (hi := (499636911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206015343223 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206015343223 / 125000000000) = 1/(125000000000 / 206015343223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49963691 / 100000000) (499636911 / 1000000000) (Real.log (206015343223 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (206015343223 / 125000000000) = -Real.log (125000000000 / 206015343223) := by
    rw [show ((206015343223 / 125000000000) : ℝ) = ((125000000000 / 206015343223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (500534787 / 1000000000) ≤ -Real.log (500000000000 / 824801610959) ∧
    -Real.log (500000000000 / 824801610959) ≤ (125133697 / 250000000) := by
  have h := checkLog_sound (w := (324801610959 / 1324801610959)) (n := 12)
    (lo := (500534787 / 1000000000)) (hi := (125133697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824801610959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824801610959 / 500000000000) = 1/(500000000000 / 824801610959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (500534787 / 1000000000) (125133697 / 250000000) (Real.log (824801610959 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (824801610959 / 500000000000) = -Real.log (500000000000 / 824801610959) := by
    rw [show ((824801610959 / 500000000000) : ℝ) = ((500000000000 / 824801610959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (355668511 / 1000000000) ≤ -Real.log (250000000000 / 356783597911) ∧
    -Real.log (250000000000 / 356783597911) ≤ (11114641 / 31250000) := by
  have h := checkLog_sound (w := (106783597911 / 606783597911)) (n := 12)
    (lo := (355668511 / 1000000000)) (hi := (11114641 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356783597911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356783597911 / 250000000000) = 1/(250000000000 / 356783597911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355668511 / 1000000000) (11114641 / 31250000) (Real.log (356783597911 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356783597911 / 250000000000) = -Real.log (250000000000 / 356783597911) := by
    rw [show ((356783597911 / 250000000000) : ℝ) = ((250000000000 / 356783597911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356316619 / 1000000000) ≤ -Real.log (100000000000 / 142805962829) ∧
    -Real.log (100000000000 / 142805962829) ≤ (17815831 / 50000000) := by
  have h := checkLog_sound (w := (42805962829 / 242805962829)) (n := 12)
    (lo := (356316619 / 1000000000)) (hi := (17815831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142805962829 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142805962829 / 100000000000) = 1/(100000000000 / 142805962829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356316619 / 1000000000) (17815831 / 50000000) (Real.log (142805962829 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142805962829 / 100000000000) = -Real.log (100000000000 / 142805962829) := by
    rw [show ((142805962829 / 100000000000) : ℝ) = ((100000000000 / 142805962829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15786941 / 500000000) ≤ -Real.log (968919367791 / 1000000000000) ∧
    -Real.log (968919367791 / 1000000000000) ≤ (31573883 / 1000000000) := by
  have h := checkLog_sound (w := (31080632209 / 1968919367791)) (n := 12)
    (lo := (15786941 / 500000000)) (hi := (31573883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968919367791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968919367791) = 1/(968919367791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31573883 / 1000000000) (-15786941 / 500000000) (Real.log (968919367791 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7864931 / 250000000) ≤ -Real.log (969029983711 / 1000000000000) ∧
    -Real.log (969029983711 / 1000000000000) ≤ (1258389 / 40000000) := by
  have h := checkLog_sound (w := (30970016289 / 1969029983711)) (n := 12)
    (lo := (7864931 / 250000000)) (hi := (1258389 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969029983711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969029983711) = 1/(969029983711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1258389 / 40000000) (-7864931 / 250000000) (Real.log (969029983711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell161
