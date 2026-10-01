import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell041
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

theorem reflection_log_1_neg : (242639759 / 1000000000) ≤ -Real.log (2560 / 3263) ∧
    -Real.log (2560 / 3263) ≤ (3032997 / 12500000) := by
  have h := checkLog_sound (w := (703 / 5823)) (n := 12)
    (lo := (242639759 / 1000000000)) (hi := (3032997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3263 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3263 / 2560) = 1/(2560 / 3263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (242639759 / 1000000000) (3032997 / 12500000) (Real.log (3263 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3263 / 2560) = -Real.log (2560 / 3263) := by
    rw [show ((3263 / 2560) : ℝ) = ((2560 / 3263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20065311 / 62500000) ≤ -Real.log (1857 / 2560) ∧
    -Real.log (1857 / 2560) ≤ (321044977 / 1000000000) := by
  have h := checkLog_sound (w := (703 / 4417)) (n := 12)
    (lo := (20065311 / 62500000)) (hi := (321044977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1857) = 1/(1857 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-321044977 / 1000000000) (-20065311 / 62500000) (Real.log (1857 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (242179953 / 1000000000) ≤ -Real.log (5120 / 6523) ∧
    -Real.log (5120 / 6523) ≤ (121089977 / 500000000) := by
  have h := checkLog_sound (w := (1403 / 11643)) (n := 12)
    (lo := (242179953 / 1000000000)) (hi := (121089977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6523 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6523 / 5120) = 1/(5120 / 6523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (242179953 / 1000000000) (121089977 / 500000000) (Real.log (6523 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6523 / 5120) = -Real.log (5120 / 6523) := by
    rw [show ((6523 / 5120) : ℝ) = ((5120 / 6523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (320237547 / 1000000000) ≤ -Real.log (3717 / 5120) ∧
    -Real.log (3717 / 5120) ≤ (80059387 / 250000000) := by
  have h := checkLog_sound (w := (1403 / 8837)) (n := 12)
    (lo := (320237547 / 1000000000)) (hi := (80059387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3717) = 1/(3717 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80059387 / 250000000) (-320237547 / 1000000000) (Real.log (3717 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177634757 / 1000000000) ≤ -Real.log (1000000 / 1194389) ∧
    -Real.log (1000000 / 1194389) ≤ (88817379 / 500000000) := by
  have h := checkLog_sound (w := (194389 / 2194389)) (n := 12)
    (lo := (177634757 / 1000000000)) (hi := (88817379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194389 / 1000000) = 1/(1000000 / 1194389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177634757 / 1000000000) (88817379 / 500000000) (Real.log (1194389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1194389 / 1000000) = -Real.log (1000000 / 1194389) := by
    rw [show ((1194389 / 1000000) : ℝ) = ((1000000 / 1194389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (216154283 / 1000000000) ≤ -Real.log (805611 / 1000000) ∧
    -Real.log (805611 / 1000000) ≤ (54038571 / 250000000) := by
  have h := checkLog_sound (w := (194389 / 1805611)) (n := 12)
    (lo := (216154283 / 1000000000)) (hi := (54038571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805611) = 1/(805611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54038571 / 250000000) (-216154283 / 1000000000) (Real.log (805611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177986339 / 1000000000) ≤ -Real.log (1000000 / 1194809) ∧
    -Real.log (1000000 / 1194809) ≤ (8899317 / 50000000) := by
  have h := checkLog_sound (w := (194809 / 2194809)) (n := 12)
    (lo := (177986339 / 1000000000)) (hi := (8899317 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194809 / 1000000) = 1/(1000000 / 1194809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177986339 / 1000000000) (8899317 / 50000000) (Real.log (1194809 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1194809 / 1000000) = -Real.log (1000000 / 1194809) := by
    rw [show ((1194809 / 1000000) : ℝ) = ((1000000 / 1194809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (108337881 / 500000000) ≤ -Real.log (805191 / 1000000) ∧
    -Real.log (805191 / 1000000) ≤ (216675763 / 1000000000) := by
  have h := checkLog_sound (w := (194809 / 1805191)) (n := 12)
    (lo := (108337881 / 500000000)) (hi := (216675763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805191) = 1/(805191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-216675763 / 1000000000) (-108337881 / 500000000) (Real.log (805191 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65035393 / 500000000) ≤ -Real.log (1000000 / 1138909) ∧
    -Real.log (1000000 / 1138909) ≤ (130070787 / 1000000000) := by
  have h := checkLog_sound (w := (138909 / 2138909)) (n := 12)
    (lo := (65035393 / 500000000)) (hi := (130070787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138909 / 1000000) = 1/(1000000 / 1138909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65035393 / 500000000) (130070787 / 1000000000) (Real.log (1138909 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1138909 / 1000000) = -Real.log (1000000 / 1138909) := by
    rw [show ((1138909 / 1000000) : ℝ) = ((1000000 / 1138909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149555089 / 1000000000) ≤ -Real.log (861091 / 1000000) ∧
    -Real.log (861091 / 1000000) ≤ (14955509 / 100000000) := by
  have h := checkLog_sound (w := (138909 / 1861091)) (n := 12)
    (lo := (149555089 / 1000000000)) (hi := (14955509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861091) = 1/(861091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14955509 / 100000000) (-149555089 / 1000000000) (Real.log (861091 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32584857 / 250000000) ≤ -Real.log (200000 / 227843) ∧
    -Real.log (200000 / 227843) ≤ (130339429 / 1000000000) := by
  have h := checkLog_sound (w := (27843 / 427843)) (n := 12)
    (lo := (32584857 / 250000000)) (hi := (130339429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227843 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227843 / 200000) = 1/(200000 / 227843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32584857 / 250000000) (130339429 / 1000000000) (Real.log (227843 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (227843 / 200000) = -Real.log (200000 / 227843) := by
    rw [show ((227843 / 200000) : ℝ) = ((200000 / 227843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (29982103 / 200000000) ≤ -Real.log (172157 / 200000) ∧
    -Real.log (172157 / 200000) ≤ (37477629 / 250000000) := by
  have h := checkLog_sound (w := (27843 / 372157)) (n := 12)
    (lo := (29982103 / 200000000)) (hi := (37477629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 172157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 172157) = 1/(172157 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-37477629 / 250000000) (-29982103 / 200000000) (Real.log (172157 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (562417501 / 1000000000) ≤ -Real.log (62500000000 / 109681867097) ∧
    -Real.log (62500000000 / 109681867097) ≤ (281208751 / 500000000) := by
  have h := checkLog_sound (w := (47181867097 / 172181867097)) (n := 12)
    (lo := (562417501 / 1000000000)) (hi := (281208751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109681867097 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109681867097 / 62500000000) = 1/(62500000000 / 109681867097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (562417501 / 1000000000) (281208751 / 500000000) (Real.log (109681867097 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (109681867097 / 62500000000) = -Real.log (62500000000 / 109681867097) := by
    rw [show ((109681867097 / 62500000000) : ℝ) = ((62500000000 / 109681867097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (112736947 / 200000000) ≤ -Real.log (250000000000 / 439283791061) ∧
    -Real.log (250000000000 / 439283791061) ≤ (4403787 / 7812500) := by
  have h := checkLog_sound (w := (189283791061 / 689283791061)) (n := 12)
    (lo := (112736947 / 200000000)) (hi := (4403787 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439283791061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439283791061 / 250000000000) = 1/(250000000000 / 439283791061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (112736947 / 200000000) (4403787 / 7812500) (Real.log (439283791061 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (439283791061 / 250000000000) = -Real.log (250000000000 / 439283791061) := by
    rw [show ((439283791061 / 250000000000) : ℝ) = ((250000000000 / 439283791061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (4922363 / 12500000) ≤ -Real.log (500000000000 / 741293875083) ∧
    -Real.log (500000000000 / 741293875083) ≤ (393789041 / 1000000000) := by
  have h := checkLog_sound (w := (241293875083 / 1241293875083)) (n := 12)
    (lo := (4922363 / 12500000)) (hi := (393789041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741293875083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741293875083 / 500000000000) = 1/(500000000000 / 741293875083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4922363 / 12500000) (393789041 / 1000000000) (Real.log (741293875083 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (741293875083 / 500000000000) = -Real.log (500000000000 / 741293875083) := by
    rw [show ((741293875083 / 500000000000) : ℝ) = ((500000000000 / 741293875083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (197331051 / 500000000) ≤ -Real.log (250000000000 / 370970676523) ∧
    -Real.log (250000000000 / 370970676523) ≤ (394662103 / 1000000000) := by
  have h := checkLog_sound (w := (120970676523 / 620970676523)) (n := 12)
    (lo := (197331051 / 500000000)) (hi := (394662103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370970676523 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370970676523 / 250000000000) = 1/(250000000000 / 370970676523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (197331051 / 500000000) (394662103 / 1000000000) (Real.log (370970676523 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (370970676523 / 250000000000) = -Real.log (250000000000 / 370970676523) := by
    rw [show ((370970676523 / 250000000000) : ℝ) = ((250000000000 / 370970676523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2237007 / 8000000) ≤ -Real.log (250000000000 / 330658722481) ∧
    -Real.log (250000000000 / 330658722481) ≤ (69906469 / 250000000) := by
  have h := checkLog_sound (w := (80658722481 / 580658722481)) (n := 12)
    (lo := (2237007 / 8000000)) (hi := (69906469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330658722481 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330658722481 / 250000000000) = 1/(250000000000 / 330658722481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2237007 / 8000000) (69906469 / 250000000) (Real.log (330658722481 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (330658722481 / 250000000000) = -Real.log (250000000000 / 330658722481) := by
    rw [show ((330658722481 / 250000000000) : ℝ) = ((250000000000 / 330658722481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35031243 / 125000000) ≤ -Real.log (500000000000 / 661730281081) ∧
    -Real.log (500000000000 / 661730281081) ≤ (56049989 / 200000000) := by
  have h := checkLog_sound (w := (161730281081 / 1161730281081)) (n := 12)
    (lo := (35031243 / 125000000)) (hi := (56049989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661730281081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661730281081 / 500000000000) = 1/(500000000000 / 661730281081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35031243 / 125000000) (56049989 / 200000000) (Real.log (661730281081 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (661730281081 / 500000000000) = -Real.log (500000000000 / 661730281081) := by
    rw [show ((661730281081 / 500000000000) : ℝ) = ((500000000000 / 661730281081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9785543 / 500000000) ≤ -Real.log (39224767351 / 40000000000) ∧
    -Real.log (39224767351 / 40000000000) ≤ (19571087 / 1000000000) := by
  have h := checkLog_sound (w := (775232649 / 79224767351)) (n := 12)
    (lo := (9785543 / 500000000)) (hi := (19571087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39224767351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39224767351) = 1/(39224767351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19571087 / 1000000000) (-9785543 / 500000000) (Real.log (39224767351 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (9742151 / 500000000) ≤ -Real.log (980704289719 / 1000000000000) ∧
    -Real.log (980704289719 / 1000000000000) ≤ (19484303 / 1000000000) := by
  have h := checkLog_sound (w := (19295710281 / 1980704289719)) (n := 12)
    (lo := (9742151 / 500000000)) (hi := (19484303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980704289719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980704289719) = 1/(980704289719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19484303 / 1000000000) (-9742151 / 500000000) (Real.log (980704289719 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell041
