import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell227
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

theorem reflection_log_1_neg : (8117107 / 25000000) ≤ -Real.log (1280 / 1771) ∧
    -Real.log (1280 / 1771) ≤ (324684281 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 3051)) (n := 12)
    (lo := (8117107 / 25000000)) (hi := (324684281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771 / 1280) = 1/(1280 / 1771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8117107 / 25000000) (324684281 / 1000000000) (Real.log (1771 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1771 / 1280) = -Real.log (1280 / 1771) := by
    rw [show ((1771 / 1280) : ℝ) = ((1280 / 1771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120962259 / 250000000) ≤ -Real.log (789 / 1280) ∧
    -Real.log (789 / 1280) ≤ (483849037 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 2069)) (n := 12)
    (lo := (120962259 / 250000000)) (hi := (483849037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 789) = 1/(789 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-483849037 / 1000000000) (-120962259 / 250000000) (Real.log (789 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324260701 / 1000000000) ≤ -Real.log (5120 / 7081) ∧
    -Real.log (5120 / 7081) ≤ (162130351 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 12201)) (n := 12)
    (lo := (324260701 / 1000000000)) (hi := (162130351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7081 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7081 / 5120) = 1/(5120 / 7081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324260701 / 1000000000) (162130351 / 500000000) (Real.log (7081 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7081 / 5120) = -Real.log (5120 / 7081) := by
    rw [show ((7081 / 5120) : ℝ) = ((5120 / 7081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (482898917 / 1000000000) ≤ -Real.log (3159 / 5120) ∧
    -Real.log (3159 / 5120) ≤ (241449459 / 500000000) := by
  have h := checkLog_sound (w := (1961 / 8279)) (n := 12)
    (lo := (482898917 / 1000000000)) (hi := (241449459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3159) = 1/(3159 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-241449459 / 500000000) (-482898917 / 1000000000) (Real.log (3159 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (241054979 / 1000000000) ≤ -Real.log (1000000 / 1272591) ∧
    -Real.log (1000000 / 1272591) ≤ (12052749 / 50000000) := by
  have h := checkLog_sound (w := (272591 / 2272591)) (n := 12)
    (lo := (241054979 / 1000000000)) (hi := (12052749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272591 / 1000000) = 1/(1000000 / 1272591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (241054979 / 1000000000) (12052749 / 50000000) (Real.log (1272591 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1272591 / 1000000) = -Real.log (1000000 / 1272591) := by
    rw [show ((1272591 / 1000000) : ℝ) = ((1000000 / 1272591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (318266373 / 1000000000) ≤ -Real.log (727409 / 1000000) ∧
    -Real.log (727409 / 1000000) ≤ (159133187 / 500000000) := by
  have h := checkLog_sound (w := (272591 / 1727409)) (n := 12)
    (lo := (318266373 / 1000000000)) (hi := (159133187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727409) = 1/(727409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159133187 / 500000000) (-318266373 / 1000000000) (Real.log (727409 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120694051 / 500000000) ≤ -Real.log (200000 / 254603) ∧
    -Real.log (200000 / 254603) ≤ (241388103 / 1000000000) := by
  have h := checkLog_sound (w := (54603 / 454603)) (n := 12)
    (lo := (120694051 / 500000000)) (hi := (241388103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254603 / 200000) = 1/(200000 / 254603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120694051 / 500000000) (241388103 / 1000000000) (Real.log (254603 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (254603 / 200000) = -Real.log (200000 / 254603) := by
    rw [show ((254603 / 200000) : ℝ) = ((200000 / 254603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159424717 / 500000000) ≤ -Real.log (145397 / 200000) ∧
    -Real.log (145397 / 200000) ≤ (63769887 / 200000000) := by
  have h := checkLog_sound (w := (54603 / 345397)) (n := 12)
    (lo := (159424717 / 500000000)) (hi := (63769887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145397) = 1/(145397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63769887 / 200000000) (-159424717 / 500000000) (Real.log (145397 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (179652163 / 1000000000) ≤ -Real.log (1000000 / 1196801) ∧
    -Real.log (1000000 / 1196801) ≤ (44913041 / 250000000) := by
  have h := checkLog_sound (w := (196801 / 2196801)) (n := 12)
    (lo := (179652163 / 1000000000)) (hi := (44913041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196801 / 1000000) = 1/(1000000 / 1196801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (179652163 / 1000000000) (44913041 / 250000000) (Real.log (1196801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1196801 / 1000000) = -Real.log (1000000 / 1196801) := by
    rw [show ((1196801 / 1000000) : ℝ) = ((1000000 / 1196801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8766111 / 40000000) ≤ -Real.log (803199 / 1000000) ∧
    -Real.log (803199 / 1000000) ≤ (27394097 / 125000000) := by
  have h := checkLog_sound (w := (196801 / 1803199)) (n := 12)
    (lo := (8766111 / 40000000)) (hi := (27394097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803199) = 1/(803199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-27394097 / 125000000) (-8766111 / 40000000) (Real.log (803199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11244917 / 62500000) ≤ -Real.log (3125 / 3741) ∧
    -Real.log (3125 / 3741) ≤ (179918673 / 1000000000) := by
  have h := checkLog_sound (w := (308 / 3433)) (n := 12)
    (lo := (11244917 / 62500000)) (hi := (179918673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 3125) = 1/(3125 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11244917 / 62500000) (179918673 / 1000000000) (Real.log (3741 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3741 / 3125) = -Real.log (3125 / 3741) := by
    rw [show ((3741 / 3125) : ℝ) = ((3125 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43910003 / 200000000) ≤ -Real.log (2509 / 3125) ∧
    -Real.log (2509 / 3125) ≤ (3430469 / 15625000) := by
  have h := checkLog_sound (w := (308 / 2817)) (n := 12)
    (lo := (43910003 / 200000000)) (hi := (3430469 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2509) = 1/(2509 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3430469 / 15625000) (-43910003 / 200000000) (Real.log (2509 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (403579809 / 500000000) ≤ -Real.log (50000000000 / 112076606521) ∧
    -Real.log (50000000000 / 112076606521) ≤ (40357981 / 50000000) := by
  have h := checkLog_sound (w := (12076606521 / 212076606521)) (n := 12)
    (lo := (57006219 / 500000000)) (hi := (114012439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112076606521 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112076606521 / 100000000000) = 1/(50000000000 / 112076606521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (403579809 / 500000000) (40357981 / 50000000) (Real.log (112076606521 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (112076606521 / 50000000000) = -Real.log (50000000000 / 112076606521) := by
    rw [show ((112076606521 / 50000000000) : ℝ) = ((50000000000 / 112076606521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (202133329 / 250000000) ≤ -Real.log (125000000000 / 280576679341) ∧
    -Real.log (125000000000 / 280576679341) ≤ (404266659 / 500000000) := by
  have h := checkLog_sound (w := (30576679341 / 530576679341)) (n := 12)
    (lo := (14423267 / 125000000)) (hi := (115386137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280576679341 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(280576679341 / 250000000000) = 1/(125000000000 / 280576679341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (202133329 / 250000000) (404266659 / 500000000) (Real.log (280576679341 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (280576679341 / 125000000000) = -Real.log (125000000000 / 280576679341) := by
    rw [show ((280576679341 / 125000000000) : ℝ) = ((125000000000 / 280576679341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (559321353 / 1000000000) ≤ -Real.log (500000000000 / 874742407641) ∧
    -Real.log (500000000000 / 874742407641) ≤ (279660677 / 500000000) := by
  have h := checkLog_sound (w := (374742407641 / 1374742407641)) (n := 12)
    (lo := (559321353 / 1000000000)) (hi := (279660677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874742407641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874742407641 / 500000000000) = 1/(500000000000 / 874742407641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (559321353 / 1000000000) (279660677 / 500000000) (Real.log (874742407641 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (874742407641 / 500000000000) = -Real.log (500000000000 / 874742407641) := by
    rw [show ((874742407641 / 500000000000) : ℝ) = ((500000000000 / 874742407641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (560237537 / 1000000000) ≤ -Real.log (250000000000 / 437772099837) ∧
    -Real.log (250000000000 / 437772099837) ≤ (280118769 / 500000000) := by
  have h := checkLog_sound (w := (187772099837 / 687772099837)) (n := 12)
    (lo := (560237537 / 1000000000)) (hi := (280118769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437772099837 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437772099837 / 250000000000) = 1/(250000000000 / 437772099837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (560237537 / 1000000000) (280118769 / 500000000) (Real.log (437772099837 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (437772099837 / 250000000000) = -Real.log (250000000000 / 437772099837) := by
    rw [show ((437772099837 / 250000000000) : ℝ) = ((250000000000 / 437772099837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (199402469 / 500000000) ≤ -Real.log (100000000000 / 149004294079) ∧
    -Real.log (100000000000 / 149004294079) ≤ (398804939 / 1000000000) := by
  have h := checkLog_sound (w := (49004294079 / 249004294079)) (n := 12)
    (lo := (199402469 / 500000000)) (hi := (398804939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149004294079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149004294079 / 100000000000) = 1/(100000000000 / 149004294079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (199402469 / 500000000) (398804939 / 1000000000) (Real.log (149004294079 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (149004294079 / 100000000000) = -Real.log (100000000000 / 149004294079) := by
    rw [show ((149004294079 / 100000000000) : ℝ) = ((100000000000 / 149004294079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (399468687 / 1000000000) ≤ -Real.log (50000000000 / 74551614189) ∧
    -Real.log (50000000000 / 74551614189) ≤ (24966793 / 62500000) := by
  have h := checkLog_sound (w := (24551614189 / 124551614189)) (n := 12)
    (lo := (399468687 / 1000000000)) (hi := (24966793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74551614189 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74551614189 / 50000000000) = 1/(50000000000 / 74551614189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (399468687 / 1000000000) (24966793 / 62500000) (Real.log (74551614189 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (74551614189 / 50000000000) = -Real.log (50000000000 / 74551614189) := by
    rw [show ((74551614189 / 50000000000) : ℝ) = ((50000000000 / 74551614189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39631343 / 1000000000) ≤ -Real.log (9386169 / 9765625) ∧
    -Real.log (9386169 / 9765625) ≤ (2476959 / 62500000) := by
  have h := checkLog_sound (w := (189728 / 9575897)) (n := 12)
    (lo := (39631343 / 1000000000)) (hi := (2476959 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9386169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9386169) = 1/(9386169 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2476959 / 62500000) (-39631343 / 1000000000) (Real.log (9386169 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39500611 / 1000000000) ≤ -Real.log (961269366399 / 1000000000000) ∧
    -Real.log (961269366399 / 1000000000000) ≤ (9875153 / 250000000) := by
  have h := checkLog_sound (w := (38730633601 / 1961269366399)) (n := 12)
    (lo := (39500611 / 1000000000)) (hi := (9875153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961269366399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961269366399) = 1/(961269366399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9875153 / 250000000) (-39500611 / 1000000000) (Real.log (961269366399 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell227
