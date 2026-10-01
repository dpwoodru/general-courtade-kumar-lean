import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0344
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

theorem reflection_log_1_neg : (53391647 / 250000000) ≤ -Real.log (5120 / 6339) ∧
    -Real.log (5120 / 6339) ≤ (213566589 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 11459)) (n := 12)
    (lo := (53391647 / 250000000)) (hi := (213566589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6339 / 5120) = 1/(5120 / 6339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53391647 / 250000000) (213566589 / 1000000000) (Real.log (6339 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6339 / 5120) = -Real.log (5120 / 6339) := by
    rw [show ((6339 / 5120) : ℝ) = ((5120 / 6339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (67980377 / 250000000) ≤ -Real.log (3901 / 5120) ∧
    -Real.log (3901 / 5120) ≤ (271921509 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 9021)) (n := 12)
    (lo := (67980377 / 250000000)) (hi := (271921509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3901) = 1/(3901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-271921509 / 1000000000) (-67980377 / 250000000) (Real.log (3901 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (213329929 / 1000000000) ≤ -Real.log (2048 / 2535) ∧
    -Real.log (2048 / 2535) ≤ (21332993 / 100000000) := by
  have h := checkLog_sound (w := (487 / 4583)) (n := 12)
    (lo := (213329929 / 1000000000)) (hi := (21332993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2535 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2535 / 2048) = 1/(2048 / 2535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (213329929 / 1000000000) (21332993 / 100000000) (Real.log (2535 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2535 / 2048) = -Real.log (2048 / 2535) := by
    rw [show ((2535 / 2048) : ℝ) = ((2048 / 2535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (54307413 / 200000000) ≤ -Real.log (1561 / 2048) ∧
    -Real.log (1561 / 2048) ≤ (135768533 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3609)) (n := 12)
    (lo := (54307413 / 200000000)) (hi := (135768533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1561) = 1/(1561 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-135768533 / 500000000) (-54307413 / 200000000) (Real.log (1561 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77890433 / 200000000) ≤ -Real.log (2560 / 3779) ∧
    -Real.log (2560 / 3779) ≤ (194726083 / 500000000) := by
  have h := checkLog_sound (w := (1219 / 6339)) (n := 12)
    (lo := (77890433 / 200000000)) (hi := (194726083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3779 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3779 / 2560) = 1/(2560 / 3779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77890433 / 200000000) (194726083 / 500000000) (Real.log (3779 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3779 / 2560) = -Real.log (2560 / 3779) := by
    rw [show ((3779 / 2560) : ℝ) = ((2560 / 3779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (323295827 / 500000000) ≤ -Real.log (1341 / 2560) ∧
    -Real.log (1341 / 2560) ≤ (129318331 / 200000000) := by
  have h := checkLog_sound (w := (1219 / 3901)) (n := 12)
    (lo := (323295827 / 500000000)) (hi := (129318331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1341) = 1/(1341 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-129318331 / 200000000) (-323295827 / 500000000) (Real.log (1341 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97263789 / 250000000) ≤ -Real.log (1024 / 1511) ∧
    -Real.log (1024 / 1511) ≤ (389055157 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 2535)) (n := 12)
    (lo := (97263789 / 250000000)) (hi := (389055157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 1024) = 1/(1024 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97263789 / 250000000) (389055157 / 1000000000) (Real.log (1511 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1511 / 1024) = -Real.log (1024 / 1511) := by
    rw [show ((1511 / 1024) : ℝ) = ((1024 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (645473711 / 1000000000) ≤ -Real.log (537 / 1024) ∧
    -Real.log (537 / 1024) ≤ (40342107 / 62500000) := by
  have h := checkLog_sound (w := (487 / 1561)) (n := 12)
    (lo := (645473711 / 1000000000)) (hi := (40342107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 537) = 1/(537 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40342107 / 62500000) (-645473711 / 1000000000) (Real.log (537 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36564857 / 125000000) ≤ -Real.log (500000 / 669899) ∧
    -Real.log (500000 / 669899) ≤ (292518857 / 1000000000) := by
  have h := checkLog_sound (w := (169899 / 1169899)) (n := 12)
    (lo := (36564857 / 125000000)) (hi := (292518857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669899 / 500000) = 1/(500000 / 669899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36564857 / 125000000) (292518857 / 1000000000) (Real.log (669899 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (669899 / 500000) = -Real.log (500000 / 669899) := by
    rw [show ((669899 / 500000) : ℝ) = ((500000 / 669899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41520943 / 100000000) ≤ -Real.log (330101 / 500000) ∧
    -Real.log (330101 / 500000) ≤ (415209431 / 1000000000) := by
  have h := checkLog_sound (w := (169899 / 830101)) (n := 12)
    (lo := (41520943 / 100000000)) (hi := (415209431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330101) = 1/(330101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-415209431 / 1000000000) (-41520943 / 100000000) (Real.log (330101 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146419501 / 500000000) ≤ -Real.log (1000000 / 1340227) ∧
    -Real.log (1000000 / 1340227) ≤ (292839003 / 1000000000) := by
  have h := checkLog_sound (w := (340227 / 2340227)) (n := 12)
    (lo := (146419501 / 500000000)) (hi := (292839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1340227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1340227 / 1000000) = 1/(1000000 / 1340227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146419501 / 500000000) (292839003 / 1000000000) (Real.log (1340227 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1340227 / 1000000) = -Real.log (1000000 / 1340227) := by
    rw [show ((1340227 / 1000000) : ℝ) = ((1000000 / 1340227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207929721 / 500000000) ≤ -Real.log (659773 / 1000000) ∧
    -Real.log (659773 / 1000000) ≤ (415859443 / 1000000000) := by
  have h := checkLog_sound (w := (340227 / 1659773)) (n := 12)
    (lo := (207929721 / 500000000)) (hi := (415859443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 659773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 659773) = 1/(659773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-415859443 / 1000000000) (-207929721 / 500000000) (Real.log (659773 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (110852859 / 500000000) ≤ -Real.log (250000 / 312051) ∧
    -Real.log (250000 / 312051) ≤ (221705719 / 1000000000) := by
  have h := checkLog_sound (w := (62051 / 562051)) (n := 12)
    (lo := (110852859 / 500000000)) (hi := (221705719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312051 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312051 / 250000) = 1/(250000 / 312051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (110852859 / 500000000) (221705719 / 1000000000) (Real.log (312051 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (312051 / 250000) = -Real.log (250000 / 312051) := by
    rw [show ((312051 / 250000) : ℝ) = ((250000 / 312051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71322567 / 250000000) ≤ -Real.log (187949 / 250000) ∧
    -Real.log (187949 / 250000) ≤ (285290269 / 1000000000) := by
  have h := checkLog_sound (w := (62051 / 437949)) (n := 12)
    (lo := (71322567 / 250000000)) (hi := (285290269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187949) = 1/(187949 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285290269 / 1000000000) (-71322567 / 250000000) (Real.log (187949 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221974067 / 1000000000) ≤ -Real.log (1000000 / 1248539) ∧
    -Real.log (1000000 / 1248539) ≤ (55493517 / 250000000) := by
  have h := checkLog_sound (w := (248539 / 2248539)) (n := 12)
    (lo := (221974067 / 1000000000)) (hi := (55493517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248539 / 1000000) = 1/(1000000 / 1248539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221974067 / 1000000000) (55493517 / 250000000) (Real.log (1248539 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1248539 / 1000000) = -Real.log (1000000 / 1248539) := by
    rw [show ((1248539 / 1000000) : ℝ) = ((1000000 / 1248539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (285735967 / 1000000000) ≤ -Real.log (751461 / 1000000) ∧
    -Real.log (751461 / 1000000) ≤ (8929249 / 31250000) := by
  have h := checkLog_sound (w := (248539 / 1751461)) (n := 12)
    (lo := (285735967 / 1000000000)) (hi := (8929249 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751461) = 1/(751461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-8929249 / 31250000) (-285735967 / 1000000000) (Real.log (751461 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (141545657 / 200000000) ≤ -Real.log (250000000000 / 507343964423) ∧
    -Real.log (250000000000 / 507343964423) ≤ (707728287 / 1000000000) := by
  have h := checkLog_sound (w := (7343964423 / 1007343964423)) (n := 12)
    (lo := (2916221 / 200000000)) (hi := (7290553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507343964423 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507343964423 / 500000000000) = 1/(250000000000 / 507343964423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (141545657 / 200000000) (707728287 / 1000000000) (Real.log (507343964423 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (507343964423 / 250000000000) = -Real.log (250000000000 / 507343964423) := by
    rw [show ((507343964423 / 250000000000) : ℝ) = ((250000000000 / 507343964423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (177174611 / 250000000) ≤ -Real.log (500000000000 / 1015672814741) ∧
    -Real.log (500000000000 / 1015672814741) ≤ (354349223 / 500000000) := by
  have h := checkLog_sound (w := (15672814741 / 2015672814741)) (n := 12)
    (lo := (485977 / 31250000)) (hi := (3110253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1015672814741 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1015672814741 / 1000000000000) = 1/(500000000000 / 1015672814741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (177174611 / 250000000) (354349223 / 500000000) (Real.log (1015672814741 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1015672814741 / 500000000000) = -Real.log (500000000000 / 1015672814741) := by
    rw [show ((1015672814741 / 500000000000) : ℝ) = ((500000000000 / 1015672814741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253497993 / 500000000) ≤ -Real.log (500000000000 / 830148072083) ∧
    -Real.log (500000000000 / 830148072083) ≤ (506995987 / 1000000000) := by
  have h := checkLog_sound (w := (330148072083 / 1330148072083)) (n := 12)
    (lo := (253497993 / 500000000)) (hi := (506995987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830148072083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830148072083 / 500000000000) = 1/(500000000000 / 830148072083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253497993 / 500000000) (506995987 / 1000000000) (Real.log (830148072083 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (830148072083 / 500000000000) = -Real.log (500000000000 / 830148072083) := by
    rw [show ((830148072083 / 500000000000) : ℝ) = ((500000000000 / 830148072083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (101542007 / 200000000) ≤ -Real.log (500000000000 / 830741049769) ∧
    -Real.log (500000000000 / 830741049769) ≤ (126927509 / 250000000) := by
  have h := checkLog_sound (w := (330741049769 / 1330741049769)) (n := 12)
    (lo := (101542007 / 200000000)) (hi := (126927509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830741049769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830741049769 / 500000000000) = 1/(500000000000 / 830741049769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (101542007 / 200000000) (126927509 / 250000000) (Real.log (830741049769 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (830741049769 / 500000000000) = -Real.log (500000000000 / 830741049769) := by
    rw [show ((830741049769 / 500000000000) : ℝ) = ((500000000000 / 830741049769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0344
