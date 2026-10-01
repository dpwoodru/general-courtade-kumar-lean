import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0368
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

theorem reflection_log_1_neg : (207871271 / 1000000000) ≤ -Real.log (5120 / 6303) ∧
    -Real.log (5120 / 6303) ≤ (25983909 / 125000000) := by
  have h := checkLog_sound (w := (1183 / 11423)) (n := 12)
    (lo := (207871271 / 1000000000)) (hi := (25983909 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6303 / 5120) = 1/(5120 / 6303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (207871271 / 1000000000) (25983909 / 125000000) (Real.log (6303 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6303 / 5120) = -Real.log (5120 / 6303) := by
    rw [show ((6303 / 5120) : ℝ) = ((5120 / 6303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (262735427 / 1000000000) ≤ -Real.log (3937 / 5120) ∧
    -Real.log (3937 / 5120) ≤ (65683857 / 250000000) := by
  have h := checkLog_sound (w := (1183 / 9057)) (n := 12)
    (lo := (262735427 / 1000000000)) (hi := (65683857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3937) = 1/(3937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65683857 / 250000000) (-262735427 / 1000000000) (Real.log (3937 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (207633261 / 1000000000) ≤ -Real.log (10240 / 12603) ∧
    -Real.log (10240 / 12603) ≤ (103816631 / 500000000) := by
  have h := checkLog_sound (w := (2363 / 22843)) (n := 12)
    (lo := (207633261 / 1000000000)) (hi := (103816631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12603 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12603 / 10240) = 1/(10240 / 12603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (207633261 / 1000000000) (103816631 / 500000000) (Real.log (12603 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12603 / 10240) = -Real.log (10240 / 12603) := by
    rw [show ((12603 / 10240) : ℝ) = ((10240 / 12603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (131177249 / 500000000) ≤ -Real.log (7877 / 10240) ∧
    -Real.log (7877 / 10240) ≤ (262354499 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 18117)) (n := 12)
    (lo := (131177249 / 500000000)) (hi := (262354499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7877) = 1/(7877 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-262354499 / 1000000000) (-131177249 / 500000000) (Real.log (7877 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (37988017 / 100000000) ≤ -Real.log (2560 / 3743) ∧
    -Real.log (2560 / 3743) ≤ (379880171 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 6303)) (n := 12)
    (lo := (37988017 / 100000000)) (hi := (379880171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3743 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3743 / 2560) = 1/(2560 / 3743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (37988017 / 100000000) (379880171 / 1000000000) (Real.log (3743 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3743 / 2560) = -Real.log (2560 / 3743) := by
    rw [show ((3743 / 2560) : ℝ) = ((2560 / 3743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (310050019 / 500000000) ≤ -Real.log (1377 / 2560) ∧
    -Real.log (1377 / 2560) ≤ (620100039 / 1000000000) := by
  have h := checkLog_sound (w := (1183 / 3937)) (n := 12)
    (lo := (310050019 / 500000000)) (hi := (620100039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1377) = 1/(1377 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-620100039 / 1000000000) (-310050019 / 500000000) (Real.log (1377 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189739671 / 500000000) ≤ -Real.log (5120 / 7483) ∧
    -Real.log (5120 / 7483) ≤ (379479343 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 12603)) (n := 12)
    (lo := (189739671 / 500000000)) (hi := (379479343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7483 / 5120) = 1/(5120 / 7483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189739671 / 500000000) (379479343 / 1000000000) (Real.log (7483 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7483 / 5120) = -Real.log (5120 / 7483) := by
    rw [show ((7483 / 5120) : ℝ) = ((5120 / 7483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (619011307 / 1000000000) ≤ -Real.log (2757 / 5120) ∧
    -Real.log (2757 / 5120) ≤ (154752827 / 250000000) := by
  have h := checkLog_sound (w := (2363 / 7877)) (n := 12)
    (lo := (619011307 / 1000000000)) (hi := (154752827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2757) = 1/(2757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154752827 / 250000000) (-619011307 / 1000000000) (Real.log (2757 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (284827 / 1000000) ≤ -Real.log (250000 / 332383) ∧
    -Real.log (250000 / 332383) ≤ (284827001 / 1000000000) := by
  have h := checkLog_sound (w := (82383 / 582383)) (n := 12)
    (lo := (284827 / 1000000)) (hi := (284827001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332383 / 250000) = 1/(250000 / 332383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (284827 / 1000000) (284827001 / 1000000000) (Real.log (332383 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (332383 / 250000) = -Real.log (250000 / 332383) := by
    rw [show ((332383 / 250000) : ℝ) = ((250000 / 332383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199889651 / 500000000) ≤ -Real.log (167617 / 250000) ∧
    -Real.log (167617 / 250000) ≤ (399779303 / 1000000000) := by
  have h := checkLog_sound (w := (82383 / 417617)) (n := 12)
    (lo := (199889651 / 500000000)) (hi := (399779303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 167617) = 1/(167617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-399779303 / 1000000000) (-199889651 / 500000000) (Real.log (167617 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142574433 / 500000000) ≤ -Real.log (25000 / 33249) ∧
    -Real.log (25000 / 33249) ≤ (285148867 / 1000000000) := by
  have h := checkLog_sound (w := (8249 / 58249)) (n := 12)
    (lo := (142574433 / 500000000)) (hi := (285148867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33249 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33249 / 25000) = 1/(25000 / 33249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142574433 / 500000000) (285148867 / 1000000000) (Real.log (33249 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (33249 / 25000) = -Real.log (25000 / 33249) := by
    rw [show ((33249 / 25000) : ℝ) = ((25000 / 33249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200208933 / 500000000) ≤ -Real.log (16751 / 25000) ∧
    -Real.log (16751 / 25000) ≤ (400417867 / 1000000000) := by
  have h := checkLog_sound (w := (8249 / 41751)) (n := 12)
    (lo := (200208933 / 500000000)) (hi := (400417867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16751) = 1/(16751 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-400417867 / 1000000000) (-200208933 / 500000000) (Real.log (16751 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215300071 / 1000000000) ≤ -Real.log (500000 / 620117) ∧
    -Real.log (500000 / 620117) ≤ (26912509 / 125000000) := by
  have h := checkLog_sound (w := (120117 / 1120117)) (n := 12)
    (lo := (215300071 / 1000000000)) (hi := (26912509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620117 / 500000) = 1/(500000 / 620117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215300071 / 1000000000) (26912509 / 125000000) (Real.log (620117 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (620117 / 500000) = -Real.log (500000 / 620117) := by
    rw [show ((620117 / 500000) : ℝ) = ((500000 / 620117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (274744787 / 1000000000) ≤ -Real.log (379883 / 500000) ∧
    -Real.log (379883 / 500000) ≤ (68686197 / 250000000) := by
  have h := checkLog_sound (w := (120117 / 879883)) (n := 12)
    (lo := (274744787 / 1000000000)) (hi := (68686197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379883) = 1/(379883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68686197 / 250000000) (-274744787 / 1000000000) (Real.log (379883 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215567727 / 1000000000) ≤ -Real.log (500000 / 620283) ∧
    -Real.log (500000 / 620283) ≤ (13472983 / 62500000) := by
  have h := checkLog_sound (w := (120283 / 1120283)) (n := 12)
    (lo := (215567727 / 1000000000)) (hi := (13472983 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620283 / 500000) = 1/(500000 / 620283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215567727 / 1000000000) (13472983 / 62500000) (Real.log (620283 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (620283 / 500000) = -Real.log (500000 / 620283) := by
    rw [show ((620283 / 500000) : ℝ) = ((500000 / 620283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (275181859 / 1000000000) ≤ -Real.log (379717 / 500000) ∧
    -Real.log (379717 / 500000) ≤ (13759093 / 50000000) := by
  have h := checkLog_sound (w := (120283 / 879717)) (n := 12)
    (lo := (275181859 / 1000000000)) (hi := (13759093 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379717) = 1/(379717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-13759093 / 50000000) (-275181859 / 1000000000) (Real.log (379717 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (684606303 / 1000000000) ≤ -Real.log (5000000000 / 9914954927) ∧
    -Real.log (5000000000 / 9914954927) ≤ (21393947 / 31250000) := by
  have h := checkLog_sound (w := (4914954927 / 14914954927)) (n := 12)
    (lo := (684606303 / 1000000000)) (hi := (21393947 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9914954927 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9914954927 / 5000000000) = 1/(5000000000 / 9914954927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (684606303 / 1000000000) (21393947 / 31250000) (Real.log (9914954927 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9914954927 / 5000000000) = -Real.log (5000000000 / 9914954927) := by
    rw [show ((9914954927 / 5000000000) : ℝ) = ((5000000000 / 9914954927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (685566733 / 1000000000) ≤ -Real.log (31250000000 / 62028013253) ∧
    -Real.log (31250000000 / 62028013253) ≤ (342783367 / 500000000) := by
  have h := checkLog_sound (w := (30778013253 / 93278013253)) (n := 12)
    (lo := (685566733 / 1000000000)) (hi := (342783367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62028013253 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62028013253 / 31250000000) = 1/(31250000000 / 62028013253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (685566733 / 1000000000) (342783367 / 500000000) (Real.log (62028013253 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (62028013253 / 31250000000) = -Real.log (31250000000 / 62028013253) := by
    rw [show ((62028013253 / 31250000000) : ℝ) = ((31250000000 / 62028013253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (490044859 / 1000000000) ≤ -Real.log (62500000000 / 102024340389) ∧
    -Real.log (62500000000 / 102024340389) ≤ (24502243 / 50000000) := by
  have h := checkLog_sound (w := (39524340389 / 164524340389)) (n := 12)
    (lo := (490044859 / 1000000000)) (hi := (24502243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102024340389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102024340389 / 62500000000) = 1/(62500000000 / 102024340389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (490044859 / 1000000000) (24502243 / 50000000) (Real.log (102024340389 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (102024340389 / 62500000000) = -Real.log (62500000000 / 102024340389) := by
    rw [show ((102024340389 / 62500000000) : ℝ) = ((62500000000 / 102024340389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (490749587 / 1000000000) ≤ -Real.log (250000000000 / 408385060453) ∧
    -Real.log (250000000000 / 408385060453) ≤ (122687397 / 250000000) := by
  have h := checkLog_sound (w := (158385060453 / 658385060453)) (n := 12)
    (lo := (490749587 / 1000000000)) (hi := (122687397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408385060453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408385060453 / 250000000000) = 1/(250000000000 / 408385060453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (490749587 / 1000000000) (122687397 / 250000000) (Real.log (408385060453 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (408385060453 / 250000000000) = -Real.log (250000000000 / 408385060453) := by
    rw [show ((408385060453 / 250000000000) : ℝ) = ((250000000000 / 408385060453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0368
