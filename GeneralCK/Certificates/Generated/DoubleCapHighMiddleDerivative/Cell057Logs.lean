import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell057
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

theorem reflection_log_1_neg : (62492009 / 250000000) ≤ -Real.log (2560 / 3287) ∧
    -Real.log (2560 / 3287) ≤ (249968037 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 5847)) (n := 12)
    (lo := (62492009 / 250000000)) (hi := (249968037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3287 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3287 / 2560) = 1/(2560 / 3287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62492009 / 250000000) (249968037 / 1000000000) (Real.log (3287 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3287 / 2560) = -Real.log (2560 / 3287) := by
    rw [show ((3287 / 2560) : ℝ) = ((2560 / 3287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (334053289 / 1000000000) ≤ -Real.log (1833 / 2560) ∧
    -Real.log (1833 / 2560) ≤ (33405329 / 100000000) := by
  have h := checkLog_sound (w := (727 / 4393)) (n := 12)
    (lo := (334053289 / 1000000000)) (hi := (33405329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1833) = 1/(1833 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33405329 / 100000000) (-334053289 / 1000000000) (Real.log (1833 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62377897 / 250000000) ≤ -Real.log (5120 / 6571) ∧
    -Real.log (5120 / 6571) ≤ (249511589 / 1000000000) := by
  have h := checkLog_sound (w := (1451 / 11691)) (n := 12)
    (lo := (62377897 / 250000000)) (hi := (249511589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6571 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6571 / 5120) = 1/(5120 / 6571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62377897 / 250000000) (249511589 / 1000000000) (Real.log (6571 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6571 / 5120) = -Real.log (5120 / 6571) := by
    rw [show ((6571 / 5120) : ℝ) = ((5120 / 6571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333235293 / 1000000000) ≤ -Real.log (3669 / 5120) ∧
    -Real.log (3669 / 5120) ≤ (166617647 / 500000000) := by
  have h := checkLog_sound (w := (1451 / 8789)) (n := 12)
    (lo := (333235293 / 1000000000)) (hi := (166617647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3669) = 1/(3669 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-166617647 / 500000000) (-333235293 / 1000000000) (Real.log (3669 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183226147 / 1000000000) ≤ -Real.log (500000 / 600543) ∧
    -Real.log (500000 / 600543) ≤ (45806537 / 250000000) := by
  have h := checkLog_sound (w := (100543 / 1100543)) (n := 12)
    (lo := (183226147 / 1000000000)) (hi := (45806537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600543 / 500000) = 1/(500000 / 600543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183226147 / 1000000000) (45806537 / 250000000) (Real.log (600543 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (600543 / 500000) = -Real.log (500000 / 600543) := by
    rw [show ((600543 / 500000) : ℝ) = ((500000 / 600543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (224501973 / 1000000000) ≤ -Real.log (399457 / 500000) ∧
    -Real.log (399457 / 500000) ≤ (112250987 / 500000000) := by
  have h := checkLog_sound (w := (100543 / 899457)) (n := 12)
    (lo := (224501973 / 1000000000)) (hi := (112250987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399457) = 1/(399457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112250987 / 500000000) (-224501973 / 1000000000) (Real.log (399457 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (183575769 / 1000000000) ≤ -Real.log (500000 / 600753) ∧
    -Real.log (500000 / 600753) ≤ (18357577 / 100000000) := by
  have h := checkLog_sound (w := (100753 / 1100753)) (n := 12)
    (lo := (183575769 / 1000000000)) (hi := (18357577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600753 / 500000) = 1/(500000 / 600753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (183575769 / 1000000000) (18357577 / 100000000) (Real.log (600753 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (600753 / 500000) = -Real.log (500000 / 600753) := by
    rw [show ((600753 / 500000) : ℝ) = ((500000 / 600753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9001113 / 40000000) ≤ -Real.log (399247 / 500000) ∧
    -Real.log (399247 / 500000) ≤ (112513913 / 500000000) := by
  have h := checkLog_sound (w := (100753 / 899247)) (n := 12)
    (lo := (9001113 / 40000000)) (hi := (112513913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399247) = 1/(399247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112513913 / 500000000) (-9001113 / 40000000) (Real.log (399247 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67178463 / 500000000) ≤ -Real.log (1000000 / 1143801) ∧
    -Real.log (1000000 / 1143801) ≤ (134356927 / 1000000000) := by
  have h := checkLog_sound (w := (143801 / 2143801)) (n := 12)
    (lo := (67178463 / 500000000)) (hi := (134356927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1143801 / 1000000) = 1/(1000000 / 1143801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67178463 / 500000000) (134356927 / 1000000000) (Real.log (1143801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1143801 / 1000000) = -Real.log (1000000 / 1143801) := by
    rw [show ((1143801 / 1000000) : ℝ) = ((1000000 / 1143801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155252453 / 1000000000) ≤ -Real.log (856199 / 1000000) ∧
    -Real.log (856199 / 1000000) ≤ (77626227 / 500000000) := by
  have h := checkLog_sound (w := (143801 / 1856199)) (n := 12)
    (lo := (155252453 / 1000000000)) (hi := (77626227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 856199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 856199) = 1/(856199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77626227 / 500000000) (-155252453 / 1000000000) (Real.log (856199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67312647 / 500000000) ≤ -Real.log (250000 / 286027) ∧
    -Real.log (250000 / 286027) ≤ (26925059 / 200000000) := by
  have h := checkLog_sound (w := (36027 / 536027)) (n := 12)
    (lo := (67312647 / 500000000)) (hi := (26925059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286027 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286027 / 250000) = 1/(250000 / 286027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67312647 / 500000000) (26925059 / 200000000) (Real.log (286027 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286027 / 250000) = -Real.log (250000 / 286027) := by
    rw [show ((286027 / 250000) : ℝ) = ((250000 / 286027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155611079 / 1000000000) ≤ -Real.log (213973 / 250000) ∧
    -Real.log (213973 / 250000) ≤ (3890277 / 25000000) := by
  have h := checkLog_sound (w := (36027 / 463973)) (n := 12)
    (lo := (155611079 / 1000000000)) (hi := (3890277 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213973) = 1/(213973 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3890277 / 25000000) (-155611079 / 1000000000) (Real.log (213973 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (291373441 / 500000000) ≤ -Real.log (15625000000 / 27983612701) ∧
    -Real.log (15625000000 / 27983612701) ≤ (582746883 / 1000000000) := by
  have h := checkLog_sound (w := (12358612701 / 43608612701)) (n := 12)
    (lo := (291373441 / 500000000)) (hi := (582746883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27983612701 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27983612701 / 15625000000) = 1/(15625000000 / 27983612701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (291373441 / 500000000) (582746883 / 1000000000) (Real.log (27983612701 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (27983612701 / 15625000000) = -Real.log (15625000000 / 27983612701) := by
    rw [show ((27983612701 / 15625000000) : ℝ) = ((15625000000 / 27983612701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23360853 / 40000000) ≤ -Real.log (500000000000 / 896617566831) ∧
    -Real.log (500000000000 / 896617566831) ≤ (292010663 / 500000000) := by
  have h := checkLog_sound (w := (396617566831 / 1396617566831)) (n := 12)
    (lo := (23360853 / 40000000)) (hi := (292010663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((896617566831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(896617566831 / 500000000000) = 1/(500000000000 / 896617566831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (23360853 / 40000000) (292010663 / 500000000) (Real.log (896617566831 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (896617566831 / 500000000000) = -Real.log (500000000000 / 896617566831) := by
    rw [show ((896617566831 / 500000000000) : ℝ) = ((500000000000 / 896617566831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (407728121 / 1000000000) ≤ -Real.log (500000000000 / 751699181639) ∧
    -Real.log (500000000000 / 751699181639) ≤ (203864061 / 500000000) := by
  have h := checkLog_sound (w := (251699181639 / 1251699181639)) (n := 12)
    (lo := (407728121 / 1000000000)) (hi := (203864061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751699181639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751699181639 / 500000000000) = 1/(500000000000 / 751699181639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (407728121 / 1000000000) (203864061 / 500000000) (Real.log (751699181639 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (751699181639 / 500000000000) = -Real.log (500000000000 / 751699181639) := by
    rw [show ((751699181639 / 500000000000) : ℝ) = ((500000000000 / 751699181639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81720719 / 200000000) ≤ -Real.log (500000000000 / 752357563113) ∧
    -Real.log (500000000000 / 752357563113) ≤ (102150899 / 250000000) := by
  have h := checkLog_sound (w := (252357563113 / 1252357563113)) (n := 12)
    (lo := (81720719 / 200000000)) (hi := (102150899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752357563113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752357563113 / 500000000000) = 1/(500000000000 / 752357563113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (81720719 / 200000000) (102150899 / 250000000) (Real.log (752357563113 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (752357563113 / 500000000000) = -Real.log (500000000000 / 752357563113) := by
    rw [show ((752357563113 / 500000000000) : ℝ) = ((500000000000 / 752357563113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14480469 / 50000000) ≤ -Real.log (500000000000 / 667952777333) ∧
    -Real.log (500000000000 / 667952777333) ≤ (289609381 / 1000000000) := by
  have h := checkLog_sound (w := (167952777333 / 1167952777333)) (n := 12)
    (lo := (14480469 / 50000000)) (hi := (289609381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667952777333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667952777333 / 500000000000) = 1/(500000000000 / 667952777333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14480469 / 50000000) (289609381 / 1000000000) (Real.log (667952777333 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667952777333 / 500000000000) = -Real.log (500000000000 / 667952777333) := by
    rw [show ((667952777333 / 500000000000) : ℝ) = ((500000000000 / 667952777333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (290236373 / 1000000000) ≤ -Real.log (10000000000 / 13367434209) ∧
    -Real.log (10000000000 / 13367434209) ≤ (145118187 / 500000000) := by
  have h := checkLog_sound (w := (3367434209 / 23367434209)) (n := 12)
    (lo := (290236373 / 1000000000)) (hi := (145118187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13367434209 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13367434209 / 10000000000) = 1/(10000000000 / 13367434209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (290236373 / 1000000000) (145118187 / 500000000) (Real.log (13367434209 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13367434209 / 10000000000) = -Real.log (10000000000 / 13367434209) := by
    rw [show ((13367434209 / 10000000000) : ℝ) = ((10000000000 / 13367434209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2623223 / 125000000) ≤ -Real.log (61202055271 / 62500000000) ∧
    -Real.log (61202055271 / 62500000000) ≤ (4197157 / 200000000) := by
  have h := checkLog_sound (w := (1297944729 / 123702055271)) (n := 12)
    (lo := (2623223 / 125000000)) (hi := (4197157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61202055271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61202055271) = 1/(61202055271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4197157 / 200000000) (-2623223 / 125000000) (Real.log (61202055271 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10447763 / 500000000) ≤ -Real.log (979321272399 / 1000000000000) ∧
    -Real.log (979321272399 / 1000000000000) ≤ (20895527 / 1000000000) := by
  have h := checkLog_sound (w := (20678727601 / 1979321272399)) (n := 12)
    (lo := (10447763 / 500000000)) (hi := (20895527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979321272399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979321272399) = 1/(979321272399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20895527 / 1000000000) (-10447763 / 500000000) (Real.log (979321272399 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell057
