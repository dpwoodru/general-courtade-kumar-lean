import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021
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

theorem reflection_log_1_neg : (5835081 / 25000000) ≤ -Real.log (2560 / 3233) ∧
    -Real.log (2560 / 3233) ≤ (233403241 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 5793)) (n := 12)
    (lo := (5835081 / 25000000)) (hi := (233403241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3233 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3233 / 2560) = 1/(2560 / 3233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5835081 / 25000000) (233403241 / 1000000000) (Real.log (3233 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3233 / 2560) = -Real.log (2560 / 3233) := by
    rw [show ((3233 / 2560) : ℝ) = ((2560 / 3233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19063687 / 62500000) ≤ -Real.log (1887 / 2560) ∧
    -Real.log (1887 / 2560) ≤ (305018993 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 4447)) (n := 12)
    (lo := (19063687 / 62500000)) (hi := (305018993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1887) = 1/(1887 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-305018993 / 1000000000) (-19063687 / 62500000) (Real.log (1887 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (232939167 / 1000000000) ≤ -Real.log (5120 / 6463) ∧
    -Real.log (5120 / 6463) ≤ (7279349 / 31250000) := by
  have h := checkLog_sound (w := (1343 / 11583)) (n := 12)
    (lo := (232939167 / 1000000000)) (hi := (7279349 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6463 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6463 / 5120) = 1/(5120 / 6463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (232939167 / 1000000000) (7279349 / 31250000) (Real.log (6463 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6463 / 5120) = -Real.log (5120 / 6463) := by
    rw [show ((6463 / 5120) : ℝ) = ((5120 / 6463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (60844879 / 200000000) ≤ -Real.log (3777 / 5120) ∧
    -Real.log (3777 / 5120) ≤ (76056099 / 250000000) := by
  have h := checkLog_sound (w := (1343 / 8897)) (n := 12)
    (lo := (60844879 / 200000000)) (hi := (76056099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3777) = 1/(3777 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-76056099 / 250000000) (-60844879 / 200000000) (Real.log (3777 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21325817 / 125000000) ≤ -Real.log (125000 / 148253) ∧
    -Real.log (125000 / 148253) ≤ (170606537 / 1000000000) := by
  have h := checkLog_sound (w := (23253 / 273253)) (n := 12)
    (lo := (21325817 / 125000000)) (hi := (170606537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148253 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148253 / 125000) = 1/(125000 / 148253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21325817 / 125000000) (170606537 / 1000000000) (Real.log (148253 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (148253 / 125000) = -Real.log (125000 / 148253) := by
    rw [show ((148253 / 125000) : ℝ) = ((125000 / 148253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (205824397 / 1000000000) ≤ -Real.log (101747 / 125000) ∧
    -Real.log (101747 / 125000) ≤ (102912199 / 500000000) := by
  have h := checkLog_sound (w := (23253 / 226747)) (n := 12)
    (lo := (205824397 / 1000000000)) (hi := (102912199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101747) = 1/(101747 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-102912199 / 500000000) (-205824397 / 1000000000) (Real.log (101747 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (34191951 / 200000000) ≤ -Real.log (1000000 / 1186443) ∧
    -Real.log (1000000 / 1186443) ≤ (42739939 / 250000000) := by
  have h := checkLog_sound (w := (186443 / 2186443)) (n := 12)
    (lo := (34191951 / 200000000)) (hi := (42739939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186443 / 1000000) = 1/(1000000 / 1186443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (34191951 / 200000000) (42739939 / 250000000) (Real.log (1186443 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1186443 / 1000000) = -Real.log (1000000 / 1186443) := by
    rw [show ((1186443 / 1000000) : ℝ) = ((1000000 / 1186443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (206339287 / 1000000000) ≤ -Real.log (813557 / 1000000) ∧
    -Real.log (813557 / 1000000) ≤ (25792411 / 125000000) := by
  have h := checkLog_sound (w := (186443 / 1813557)) (n := 12)
    (lo := (206339287 / 1000000000)) (hi := (25792411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813557) = 1/(813557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-25792411 / 125000000) (-206339287 / 1000000000) (Real.log (813557 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (124703919 / 1000000000) ≤ -Real.log (1000000 / 1132813) ∧
    -Real.log (1000000 / 1132813) ≤ (1558799 / 12500000) := by
  have h := checkLog_sound (w := (132813 / 2132813)) (n := 12)
    (lo := (124703919 / 1000000000)) (hi := (1558799 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132813 / 1000000) = 1/(1000000 / 1132813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (124703919 / 1000000000) (1558799 / 12500000) (Real.log (1132813 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1132813 / 1000000) = -Real.log (1000000 / 1132813) := by
    rw [show ((1132813 / 1000000) : ℝ) = ((1000000 / 1132813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142500639 / 1000000000) ≤ -Real.log (867187 / 1000000) ∧
    -Real.log (867187 / 1000000) ≤ (890629 / 6250000) := by
  have h := checkLog_sound (w := (132813 / 1867187)) (n := 12)
    (lo := (142500639 / 1000000000)) (hi := (890629 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867187) = 1/(867187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-890629 / 6250000) (-142500639 / 1000000000) (Real.log (867187 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31243281 / 250000000) ≤ -Real.log (500000 / 566559) ∧
    -Real.log (500000 / 566559) ≤ (199957 / 1600000) := by
  have h := checkLog_sound (w := (66559 / 1066559)) (n := 12)
    (lo := (31243281 / 250000000)) (hi := (199957 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566559 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566559 / 500000) = 1/(500000 / 566559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31243281 / 250000000) (199957 / 1600000) (Real.log (566559 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566559 / 500000) = -Real.log (500000 / 566559) := by
    rw [show ((566559 / 500000) : ℝ) = ((500000 / 566559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (35713103 / 250000000) ≤ -Real.log (433441 / 500000) ∧
    -Real.log (433441 / 500000) ≤ (142852413 / 1000000000) := by
  have h := checkLog_sound (w := (66559 / 933441)) (n := 12)
    (lo := (35713103 / 250000000)) (hi := (142852413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433441) = 1/(433441 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-142852413 / 1000000000) (-35713103 / 250000000) (Real.log (433441 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (268581781 / 500000000) ≤ -Real.log (62500000000 / 106946650781) ∧
    -Real.log (62500000000 / 106946650781) ≤ (537163563 / 1000000000) := by
  have h := checkLog_sound (w := (44446650781 / 169446650781)) (n := 12)
    (lo := (268581781 / 500000000)) (hi := (537163563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106946650781 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106946650781 / 62500000000) = 1/(62500000000 / 106946650781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (268581781 / 500000000) (537163563 / 1000000000) (Real.log (106946650781 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (106946650781 / 62500000000) = -Real.log (62500000000 / 106946650781) := by
    rw [show ((106946650781 / 62500000000) : ℝ) = ((62500000000 / 106946650781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67302779 / 125000000) ≤ -Real.log (15625000000 / 26770336513) ∧
    -Real.log (15625000000 / 26770336513) ≤ (538422233 / 1000000000) := by
  have h := checkLog_sound (w := (11145336513 / 42395336513)) (n := 12)
    (lo := (67302779 / 125000000)) (hi := (538422233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26770336513 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26770336513 / 15625000000) = 1/(15625000000 / 26770336513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (67302779 / 125000000) (538422233 / 1000000000) (Real.log (26770336513 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (26770336513 / 15625000000) = -Real.log (15625000000 / 26770336513) := by
    rw [show ((26770336513 / 15625000000) : ℝ) = ((15625000000 / 26770336513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (376430933 / 1000000000) ≤ -Real.log (100000000000 / 145707490147) ∧
    -Real.log (100000000000 / 145707490147) ≤ (188215467 / 500000000) := by
  have h := checkLog_sound (w := (45707490147 / 245707490147)) (n := 12)
    (lo := (376430933 / 1000000000)) (hi := (188215467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145707490147 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145707490147 / 100000000000) = 1/(100000000000 / 145707490147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (376430933 / 1000000000) (188215467 / 500000000) (Real.log (145707490147 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145707490147 / 100000000000) = -Real.log (100000000000 / 145707490147) := by
    rw [show ((145707490147 / 100000000000) : ℝ) = ((100000000000 / 145707490147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (188649521 / 500000000) ≤ -Real.log (125000000000 / 182292543731) ∧
    -Real.log (125000000000 / 182292543731) ≤ (377299043 / 1000000000) := by
  have h := checkLog_sound (w := (57292543731 / 307292543731)) (n := 12)
    (lo := (188649521 / 500000000)) (hi := (377299043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182292543731 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182292543731 / 125000000000) = 1/(125000000000 / 182292543731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (188649521 / 500000000) (377299043 / 1000000000) (Real.log (182292543731 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (182292543731 / 125000000000) = -Real.log (125000000000 / 182292543731) := by
    rw [show ((182292543731 / 125000000000) : ℝ) = ((125000000000 / 182292543731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (267204559 / 1000000000) ≤ -Real.log (250000000000 / 326576909017) ∧
    -Real.log (250000000000 / 326576909017) ≤ (3340057 / 12500000) := by
  have h := checkLog_sound (w := (76576909017 / 576576909017)) (n := 12)
    (lo := (267204559 / 1000000000)) (hi := (3340057 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326576909017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326576909017 / 250000000000) = 1/(250000000000 / 326576909017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (267204559 / 1000000000) (3340057 / 12500000) (Real.log (326576909017 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (326576909017 / 250000000000) = -Real.log (250000000000 / 326576909017) := by
    rw [show ((326576909017 / 250000000000) : ℝ) = ((250000000000 / 326576909017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (267825537 / 1000000000) ≤ -Real.log (500000000000 / 653559538669) ∧
    -Real.log (500000000000 / 653559538669) ≤ (133912769 / 500000000) := by
  have h := checkLog_sound (w := (153559538669 / 1153559538669)) (n := 12)
    (lo := (267825537 / 1000000000)) (hi := (133912769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653559538669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653559538669 / 500000000000) = 1/(500000000000 / 653559538669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (267825537 / 1000000000) (133912769 / 500000000) (Real.log (653559538669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (653559538669 / 500000000000) = -Real.log (500000000000 / 653559538669) := by
    rw [show ((653559538669 / 500000000000) : ℝ) = ((500000000000 / 653559538669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2234911 / 125000000) ≤ -Real.log (245569899519 / 250000000000) ∧
    -Real.log (245569899519 / 250000000000) ≤ (17879289 / 1000000000) := by
  have h := checkLog_sound (w := (4430100481 / 495569899519)) (n := 12)
    (lo := (2234911 / 125000000)) (hi := (17879289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245569899519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245569899519) = 1/(245569899519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17879289 / 1000000000) (-2234911 / 125000000) (Real.log (245569899519 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17796719 / 1000000000) ≤ -Real.log (982360707031 / 1000000000000) ∧
    -Real.log (982360707031 / 1000000000000) ≤ (222459 / 12500000) := by
  have h := checkLog_sound (w := (17639292969 / 1982360707031)) (n := 12)
    (lo := (17796719 / 1000000000)) (hi := (222459 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982360707031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982360707031) = 1/(982360707031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-222459 / 12500000) (-17796719 / 1000000000) (Real.log (982360707031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021
