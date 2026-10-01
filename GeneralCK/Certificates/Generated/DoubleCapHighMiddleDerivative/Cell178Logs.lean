import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell178
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

theorem reflection_log_1_neg : (60742993 / 200000000) ≤ -Real.log (5120 / 6937) ∧
    -Real.log (5120 / 6937) ≤ (151857483 / 500000000) := by
  have h := checkLog_sound (w := (1817 / 12057)) (n := 12)
    (lo := (60742993 / 200000000)) (hi := (151857483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6937 / 5120) = 1/(5120 / 6937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60742993 / 200000000) (151857483 / 500000000) (Real.log (6937 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6937 / 5120) = -Real.log (5120 / 6937) := by
    rw [show ((6937 / 5120) : ℝ) = ((5120 / 6937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (109580823 / 250000000) ≤ -Real.log (3303 / 5120) ∧
    -Real.log (3303 / 5120) ≤ (438323293 / 1000000000) := by
  have h := checkLog_sound (w := (1817 / 8423)) (n := 12)
    (lo := (109580823 / 250000000)) (hi := (438323293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3303) = 1/(3303 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-438323293 / 1000000000) (-109580823 / 250000000) (Real.log (3303 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37910301 / 125000000) ≤ -Real.log (2560 / 3467) ∧
    -Real.log (2560 / 3467) ≤ (303282409 / 1000000000) := by
  have h := checkLog_sound (w := (907 / 6027)) (n := 12)
    (lo := (37910301 / 125000000)) (hi := (303282409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3467 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3467 / 2560) = 1/(2560 / 3467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37910301 / 125000000) (303282409 / 1000000000) (Real.log (3467 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3467 / 2560) = -Real.log (2560 / 3467) := by
    rw [show ((3467 / 2560) : ℝ) = ((2560 / 3467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (437415439 / 1000000000) ≤ -Real.log (1653 / 2560) ∧
    -Real.log (1653 / 2560) ≤ (5467693 / 12500000) := by
  have h := checkLog_sound (w := (907 / 4213)) (n := 12)
    (lo := (437415439 / 1000000000)) (hi := (5467693 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1653) = 1/(1653 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-5467693 / 12500000) (-437415439 / 1000000000) (Real.log (1653 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224668787 / 1000000000) ≤ -Real.log (250000 / 312977) ∧
    -Real.log (250000 / 312977) ≤ (56167197 / 250000000) := by
  have h := checkLog_sound (w := (62977 / 562977)) (n := 12)
    (lo := (224668787 / 1000000000)) (hi := (56167197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312977 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312977 / 250000) = 1/(250000 / 312977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224668787 / 1000000000) (56167197 / 250000000) (Real.log (312977 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (312977 / 250000) = -Real.log (250000 / 312977) := by
    rw [show ((312977 / 250000) : ℝ) = ((250000 / 312977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (290229313 / 1000000000) ≤ -Real.log (187023 / 250000) ∧
    -Real.log (187023 / 250000) ≤ (145114657 / 500000000) := by
  have h := checkLog_sound (w := (62977 / 437023)) (n := 12)
    (lo := (290229313 / 1000000000)) (hi := (145114657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187023) = 1/(187023 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145114657 / 500000000) (-290229313 / 1000000000) (Real.log (187023 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (112503307 / 500000000) ≤ -Real.log (1000000 / 1252331) ∧
    -Real.log (1000000 / 1252331) ≤ (45001323 / 200000000) := by
  have h := checkLog_sound (w := (252331 / 2252331)) (n := 12)
    (lo := (112503307 / 500000000)) (hi := (45001323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252331 / 1000000) = 1/(1000000 / 1252331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (112503307 / 500000000) (45001323 / 200000000) (Real.log (1252331 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1252331 / 1000000) = -Real.log (1000000 / 1252331) := by
    rw [show ((1252331 / 1000000) : ℝ) = ((1000000 / 1252331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9087341 / 31250000) ≤ -Real.log (747669 / 1000000) ∧
    -Real.log (747669 / 1000000) ≤ (290794913 / 1000000000) := by
  have h := checkLog_sound (w := (252331 / 1747669)) (n := 12)
    (lo := (9087341 / 31250000)) (hi := (290794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747669) = 1/(747669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-290794913 / 1000000000) (-9087341 / 31250000) (Real.log (747669 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166626531 / 1000000000) ≤ -Real.log (1000000 / 1181313) ∧
    -Real.log (1000000 / 1181313) ≤ (41656633 / 250000000) := by
  have h := checkLog_sound (w := (181313 / 2181313)) (n := 12)
    (lo := (166626531 / 1000000000)) (hi := (41656633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181313 / 1000000) = 1/(1000000 / 1181313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166626531 / 1000000000) (41656633 / 250000000) (Real.log (1181313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1181313 / 1000000) = -Real.log (1000000 / 1181313) := by
    rw [show ((1181313 / 1000000) : ℝ) = ((1000000 / 1181313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (200053441 / 1000000000) ≤ -Real.log (818687 / 1000000) ∧
    -Real.log (818687 / 1000000) ≤ (100026721 / 500000000) := by
  have h := checkLog_sound (w := (181313 / 1818687)) (n := 12)
    (lo := (200053441 / 1000000000)) (hi := (100026721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818687) = 1/(818687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-100026721 / 500000000) (-200053441 / 1000000000) (Real.log (818687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83446997 / 500000000) ≤ -Real.log (1000000 / 1181629) ∧
    -Real.log (1000000 / 1181629) ≤ (33378799 / 200000000) := by
  have h := checkLog_sound (w := (181629 / 2181629)) (n := 12)
    (lo := (83446997 / 500000000)) (hi := (33378799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181629 / 1000000) = 1/(1000000 / 1181629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83446997 / 500000000) (33378799 / 200000000) (Real.log (1181629 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181629 / 1000000) = -Real.log (1000000 / 1181629) := by
    rw [show ((1181629 / 1000000) : ℝ) = ((1000000 / 1181629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (200439499 / 1000000000) ≤ -Real.log (818371 / 1000000) ∧
    -Real.log (818371 / 1000000) ≤ (400879 / 2000000) := by
  have h := checkLog_sound (w := (181629 / 1818371)) (n := 12)
    (lo := (200439499 / 1000000000)) (hi := (400879 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818371) = 1/(818371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-400879 / 2000000) (-200439499 / 1000000000) (Real.log (818371 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (740697847 / 1000000000) ≤ -Real.log (500000000000 / 1048699334543) ∧
    -Real.log (500000000000 / 1048699334543) ≤ (740697849 / 1000000000) := by
  have h := checkLog_sound (w := (48699334543 / 2048699334543)) (n := 12)
    (lo := (47550667 / 1000000000)) (hi := (11887667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1048699334543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1048699334543 / 1000000000000) = 1/(500000000000 / 1048699334543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (740697847 / 1000000000) (740697849 / 1000000000) (Real.log (1048699334543 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1048699334543 / 500000000000) = -Real.log (500000000000 / 1048699334543) := by
    rw [show ((1048699334543 / 500000000000) : ℝ) = ((500000000000 / 1048699334543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (742038257 / 1000000000) ≤ -Real.log (20000000000 / 42004238571) ∧
    -Real.log (20000000000 / 42004238571) ≤ (742038259 / 1000000000) := by
  have h := checkLog_sound (w := (2004238571 / 82004238571)) (n := 12)
    (lo := (48891077 / 1000000000)) (hi := (24445539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42004238571 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42004238571 / 40000000000) = 1/(20000000000 / 42004238571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (742038257 / 1000000000) (742038259 / 1000000000) (Real.log (42004238571 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42004238571 / 20000000000) = -Real.log (20000000000 / 42004238571) := by
    rw [show ((42004238571 / 20000000000) : ℝ) = ((20000000000 / 42004238571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (514898101 / 1000000000) ≤ -Real.log (50000000000 / 83673398459) ∧
    -Real.log (50000000000 / 83673398459) ≤ (257449051 / 500000000) := by
  have h := checkLog_sound (w := (33673398459 / 133673398459)) (n := 12)
    (lo := (514898101 / 1000000000)) (hi := (257449051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83673398459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83673398459 / 50000000000) = 1/(50000000000 / 83673398459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (514898101 / 1000000000) (257449051 / 500000000) (Real.log (83673398459 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (83673398459 / 50000000000) = -Real.log (50000000000 / 83673398459) := by
    rw [show ((83673398459 / 50000000000) : ℝ) = ((50000000000 / 83673398459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (515801527 / 1000000000) ≤ -Real.log (6250000000 / 10468628163) ∧
    -Real.log (6250000000 / 10468628163) ≤ (64475191 / 125000000) := by
  have h := checkLog_sound (w := (4218628163 / 16718628163)) (n := 12)
    (lo := (515801527 / 1000000000)) (hi := (64475191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10468628163 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10468628163 / 6250000000) = 1/(6250000000 / 10468628163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (515801527 / 1000000000) (64475191 / 125000000) (Real.log (10468628163 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (10468628163 / 6250000000) = -Real.log (6250000000 / 10468628163) := by
    rw [show ((10468628163 / 6250000000) : ℝ) = ((6250000000 / 10468628163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (366679973 / 1000000000) ≤ -Real.log (50000000000 / 72146803357) ∧
    -Real.log (50000000000 / 72146803357) ≤ (183339987 / 500000000) := by
  have h := checkLog_sound (w := (22146803357 / 122146803357)) (n := 12)
    (lo := (366679973 / 1000000000)) (hi := (183339987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72146803357 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72146803357 / 50000000000) = 1/(50000000000 / 72146803357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (366679973 / 1000000000) (183339987 / 500000000) (Real.log (72146803357 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (72146803357 / 50000000000) = -Real.log (50000000000 / 72146803357) := by
    rw [show ((72146803357 / 50000000000) : ℝ) = ((50000000000 / 72146803357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (183666747 / 500000000) ≤ -Real.log (250000000000 / 360969841307) ∧
    -Real.log (250000000000 / 360969841307) ≤ (73466699 / 200000000) := by
  have h := checkLog_sound (w := (110969841307 / 610969841307)) (n := 12)
    (lo := (183666747 / 500000000)) (hi := (73466699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360969841307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360969841307 / 250000000000) = 1/(250000000000 / 360969841307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (183666747 / 500000000) (73466699 / 200000000) (Real.log (360969841307 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (360969841307 / 250000000000) = -Real.log (250000000000 / 360969841307) := by
    rw [show ((360969841307 / 250000000000) : ℝ) = ((250000000000 / 360969841307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6709101 / 200000000) ≤ -Real.log (967010906359 / 1000000000000) ∧
    -Real.log (967010906359 / 1000000000000) ≤ (16772753 / 500000000) := by
  have h := checkLog_sound (w := (32989093641 / 1967010906359)) (n := 12)
    (lo := (6709101 / 200000000)) (hi := (16772753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967010906359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967010906359) = 1/(967010906359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16772753 / 500000000) (-6709101 / 200000000) (Real.log (967010906359 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33426909 / 1000000000) ≤ -Real.log (967125596031 / 1000000000000) ∧
    -Real.log (967125596031 / 1000000000000) ≤ (3342691 / 100000000) := by
  have h := checkLog_sound (w := (32874403969 / 1967125596031)) (n := 12)
    (lo := (33426909 / 1000000000)) (hi := (3342691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967125596031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967125596031) = 1/(967125596031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3342691 / 100000000) (-33426909 / 1000000000) (Real.log (967125596031 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell178
