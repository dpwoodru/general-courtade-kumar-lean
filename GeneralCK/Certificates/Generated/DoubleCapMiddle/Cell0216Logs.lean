import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0216
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

theorem reflection_log_1_neg : (51690073 / 200000000) ≤ -Real.log (512 / 663) ∧
    -Real.log (512 / 663) ≤ (129225183 / 500000000) := by
  have h := checkLog_sound (w := (151 / 1175)) (n := 12)
    (lo := (51690073 / 200000000)) (hi := (129225183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 512) = 1/(512 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51690073 / 200000000) (129225183 / 500000000) (Real.log (663 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (663 / 512) = -Real.log (512 / 663) := by
    rw [show ((663 / 512) : ℝ) = ((512 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (174723333 / 500000000) ≤ -Real.log (361 / 512) ∧
    -Real.log (361 / 512) ≤ (349446667 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 873)) (n := 12)
    (lo := (174723333 / 500000000)) (hi := (349446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 361) = 1/(361 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-349446667 / 1000000000) (-174723333 / 500000000) (Real.log (361 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128998887 / 500000000) ≤ -Real.log (5120 / 6627) ∧
    -Real.log (5120 / 6627) ≤ (10319911 / 40000000) := by
  have h := checkLog_sound (w := (1507 / 11747)) (n := 12)
    (lo := (128998887 / 500000000)) (hi := (10319911 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6627 / 5120) = 1/(5120 / 6627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128998887 / 500000000) (10319911 / 40000000) (Real.log (6627 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6627 / 5120) = -Real.log (5120 / 6627) := by
    rw [show ((6627 / 5120) : ℝ) = ((5120 / 6627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (174307993 / 500000000) ≤ -Real.log (3613 / 5120) ∧
    -Real.log (3613 / 5120) ≤ (348615987 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 8733)) (n := 12)
    (lo := (174307993 / 500000000)) (hi := (348615987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3613) = 1/(3613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-348615987 / 1000000000) (-174307993 / 500000000) (Real.log (3613 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23181787 / 50000000) ≤ -Real.log (256 / 407) ∧
    -Real.log (256 / 407) ≤ (463635741 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 663)) (n := 12)
    (lo := (23181787 / 50000000)) (hi := (463635741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407 / 256) = 1/(256 / 407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23181787 / 50000000) (463635741 / 1000000000) (Real.log (407 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (407 / 256) = -Real.log (256 / 407) := by
    rw [show ((407 / 256) : ℝ) = ((256 / 407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (891217093 / 1000000000) ≤ -Real.log (105 / 256) ∧
    -Real.log (105 / 256) ≤ (178243419 / 200000000) := by
  have h := checkLog_sound (w := (23 / 233)) (n := 12)
    (lo := (198069913 / 1000000000)) (hi := (99034957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 105) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 105) = 1/(105 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-178243419 / 200000000) (-891217093 / 1000000000) (Real.log (105 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7232787 / 15625000) ≤ -Real.log (2560 / 4067) ∧
    -Real.log (2560 / 4067) ≤ (462898369 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 6627)) (n := 12)
    (lo := (7232787 / 15625000)) (hi := (462898369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4067 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4067 / 2560) = 1/(2560 / 4067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7232787 / 15625000) (462898369 / 1000000000) (Real.log (4067 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4067 / 2560) = -Real.log (2560 / 4067) := by
    rw [show ((4067 / 2560) : ℝ) = ((2560 / 4067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (111045503 / 125000000) ≤ -Real.log (1053 / 2560) ∧
    -Real.log (1053 / 2560) ≤ (444182013 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2333)) (n := 12)
    (lo := (48804211 / 250000000)) (hi := (39043369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1053) = 1/(1053 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-444182013 / 500000000) (-111045503 / 125000000) (Real.log (1053 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88250853 / 250000000) ≤ -Real.log (125000 / 177917) ∧
    -Real.log (125000 / 177917) ≤ (353003413 / 1000000000) := by
  have h := checkLog_sound (w := (52917 / 302917)) (n := 12)
    (lo := (88250853 / 250000000)) (hi := (353003413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177917 / 125000) = 1/(125000 / 177917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88250853 / 250000000) (353003413 / 1000000000) (Real.log (177917 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (177917 / 125000) = -Real.log (125000 / 177917) := by
    rw [show ((177917 / 125000) : ℝ) = ((125000 / 177917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34405969 / 62500000) ≤ -Real.log (72083 / 125000) ∧
    -Real.log (72083 / 125000) ≤ (110099101 / 200000000) := by
  have h := checkLog_sound (w := (52917 / 197083)) (n := 12)
    (lo := (34405969 / 62500000)) (hi := (110099101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72083) = 1/(72083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110099101 / 200000000) (-34405969 / 62500000) (Real.log (72083 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176810041 / 500000000) ≤ -Real.log (500000 / 712107) ∧
    -Real.log (500000 / 712107) ≤ (353620083 / 1000000000) := by
  have h := checkLog_sound (w := (212107 / 1212107)) (n := 12)
    (lo := (176810041 / 500000000)) (hi := (353620083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712107 / 500000) = 1/(500000 / 712107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176810041 / 500000000) (353620083 / 1000000000) (Real.log (712107 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (712107 / 500000) = -Real.log (500000 / 712107) := by
    rw [show ((712107 / 500000) : ℝ) = ((500000 / 712107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (110403843 / 200000000) ≤ -Real.log (287893 / 500000) ∧
    -Real.log (287893 / 500000) ≤ (34501201 / 62500000) := by
  have h := checkLog_sound (w := (212107 / 787893)) (n := 12)
    (lo := (110403843 / 200000000)) (hi := (34501201 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287893) = 1/(287893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34501201 / 62500000) (-110403843 / 200000000) (Real.log (287893 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273791037 / 1000000000) ≤ -Real.log (50000 / 65747) ∧
    -Real.log (50000 / 65747) ≤ (136895519 / 500000000) := by
  have h := checkLog_sound (w := (15747 / 115747)) (n := 12)
    (lo := (273791037 / 1000000000)) (hi := (136895519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65747 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65747 / 50000) = 1/(50000 / 65747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273791037 / 1000000000) (136895519 / 500000000) (Real.log (65747 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (65747 / 50000) = -Real.log (50000 / 65747) := by
    rw [show ((65747 / 50000) : ℝ) = ((50000 / 65747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (378248853 / 1000000000) ≤ -Real.log (34253 / 50000) ∧
    -Real.log (34253 / 50000) ≤ (189124427 / 500000000) := by
  have h := checkLog_sound (w := (15747 / 84253)) (n := 12)
    (lo := (378248853 / 1000000000)) (hi := (189124427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34253) = 1/(34253 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-189124427 / 500000000) (-378248853 / 1000000000) (Real.log (34253 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85731 / 312500) ≤ -Real.log (1000000 / 1315661) ∧
    -Real.log (1000000 / 1315661) ≤ (274339201 / 1000000000) := by
  have h := checkLog_sound (w := (315661 / 2315661)) (n := 12)
    (lo := (85731 / 312500)) (hi := (274339201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315661 / 1000000) = 1/(1000000 / 1315661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85731 / 312500) (274339201 / 1000000000) (Real.log (1315661 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1315661 / 1000000) = -Real.log (1000000 / 1315661) := by
    rw [show ((1315661 / 1000000) : ℝ) = ((1000000 / 1315661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37930187 / 100000000) ≤ -Real.log (684339 / 1000000) ∧
    -Real.log (684339 / 1000000) ≤ (379301871 / 1000000000) := by
  have h := checkLog_sound (w := (315661 / 1684339)) (n := 12)
    (lo := (37930187 / 100000000)) (hi := (379301871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684339) = 1/(684339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-379301871 / 1000000000) (-37930187 / 100000000) (Real.log (684339 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (180699783 / 200000000) ≤ -Real.log (250000000000 / 617056032629) ∧
    -Real.log (250000000000 / 617056032629) ≤ (903498917 / 1000000000) := by
  have h := checkLog_sound (w := (117056032629 / 1117056032629)) (n := 12)
    (lo := (42070347 / 200000000)) (hi := (26293967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617056032629 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(617056032629 / 500000000000) = 1/(250000000000 / 617056032629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (180699783 / 200000000) (903498917 / 1000000000) (Real.log (617056032629 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (617056032629 / 250000000000) = -Real.log (250000000000 / 617056032629) := by
    rw [show ((617056032629 / 250000000000) : ℝ) = ((250000000000 / 617056032629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (905639297 / 1000000000) ≤ -Real.log (62500000000 / 154594545543) ∧
    -Real.log (62500000000 / 154594545543) ≤ (905639299 / 1000000000) := by
  have h := checkLog_sound (w := (29594545543 / 279594545543)) (n := 12)
    (lo := (212492117 / 1000000000)) (hi := (106246059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154594545543 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154594545543 / 125000000000) = 1/(62500000000 / 154594545543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (905639297 / 1000000000) (905639299 / 1000000000) (Real.log (154594545543 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154594545543 / 62500000000) = -Real.log (62500000000 / 154594545543) := by
    rw [show ((154594545543 / 62500000000) : ℝ) = ((62500000000 / 154594545543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (65203989 / 100000000) ≤ -Real.log (500000000000 / 959726155373) ∧
    -Real.log (500000000000 / 959726155373) ≤ (652039891 / 1000000000) := by
  have h := checkLog_sound (w := (459726155373 / 1459726155373)) (n := 12)
    (lo := (65203989 / 100000000)) (hi := (652039891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959726155373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959726155373 / 500000000000) = 1/(500000000000 / 959726155373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (65203989 / 100000000) (652039891 / 1000000000) (Real.log (959726155373 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (959726155373 / 500000000000) = -Real.log (500000000000 / 959726155373) := by
    rw [show ((959726155373 / 500000000000) : ℝ) = ((500000000000 / 959726155373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (653641071 / 1000000000) ≤ -Real.log (500000000000 / 961264081107) ∧
    -Real.log (500000000000 / 961264081107) ≤ (40852567 / 62500000) := by
  have h := checkLog_sound (w := (461264081107 / 1461264081107)) (n := 12)
    (lo := (653641071 / 1000000000)) (hi := (40852567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961264081107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961264081107 / 500000000000) = 1/(500000000000 / 961264081107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (653641071 / 1000000000) (40852567 / 62500000) (Real.log (961264081107 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (961264081107 / 500000000000) = -Real.log (500000000000 / 961264081107) := by
    rw [show ((961264081107 / 500000000000) : ℝ) = ((500000000000 / 961264081107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0216
