import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0447
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

theorem reflection_log_1_neg : (94445861 / 500000000) ≤ -Real.log (10240 / 12369) ∧
    -Real.log (10240 / 12369) ≤ (188891723 / 1000000000) := by
  have h := checkLog_sound (w := (2129 / 22609)) (n := 12)
    (lo := (94445861 / 500000000)) (hi := (188891723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12369 / 10240) = 1/(10240 / 12369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (94445861 / 500000000) (188891723 / 1000000000) (Real.log (12369 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12369 / 10240) = -Real.log (10240 / 12369) := by
    rw [show ((12369 / 10240) : ℝ) = ((10240 / 12369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (116540227 / 500000000) ≤ -Real.log (8111 / 10240) ∧
    -Real.log (8111 / 10240) ≤ (46616091 / 200000000) := by
  have h := checkLog_sound (w := (2129 / 18351)) (n := 12)
    (lo := (116540227 / 500000000)) (hi := (46616091 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8111) = 1/(8111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46616091 / 200000000) (-116540227 / 500000000) (Real.log (8111 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188649151 / 1000000000) ≤ -Real.log (5120 / 6183) ∧
    -Real.log (5120 / 6183) ≤ (2947643 / 15625000) := by
  have h := checkLog_sound (w := (1063 / 11303)) (n := 12)
    (lo := (188649151 / 1000000000)) (hi := (2947643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6183 / 5120) = 1/(5120 / 6183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188649151 / 1000000000) (2947643 / 15625000) (Real.log (6183 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6183 / 5120) = -Real.log (5120 / 6183) := by
    rw [show ((6183 / 5120) : ℝ) = ((5120 / 6183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (116355327 / 500000000) ≤ -Real.log (4057 / 5120) ∧
    -Real.log (4057 / 5120) ≤ (46542131 / 200000000) := by
  have h := checkLog_sound (w := (1063 / 9177)) (n := 12)
    (lo := (116355327 / 500000000)) (hi := (46542131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4057) = 1/(4057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) (Real.log (4057 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (347709089 / 1000000000) ≤ -Real.log (5120 / 7249) ∧
    -Real.log (5120 / 7249) ≤ (34770909 / 100000000) := by
  have h := checkLog_sound (w := (2129 / 12369)) (n := 12)
    (lo := (347709089 / 1000000000)) (hi := (34770909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7249 / 5120) = 1/(5120 / 7249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (347709089 / 1000000000) (34770909 / 100000000) (Real.log (7249 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7249 / 5120) = -Real.log (5120 / 7249) := by
    rw [show ((7249 / 5120) : ℝ) = ((5120 / 7249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (537546659 / 1000000000) ≤ -Real.log (2991 / 5120) ∧
    -Real.log (2991 / 5120) ≤ (26877333 / 50000000) := by
  have h := checkLog_sound (w := (2129 / 8111)) (n := 12)
    (lo := (537546659 / 1000000000)) (hi := (26877333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2991) = 1/(2991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26877333 / 50000000) (-537546659 / 1000000000) (Real.log (2991 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (347295153 / 1000000000) ≤ -Real.log (2560 / 3623) ∧
    -Real.log (2560 / 3623) ≤ (173647577 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 6183)) (n := 12)
    (lo := (347295153 / 1000000000)) (hi := (173647577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3623 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3623 / 2560) = 1/(2560 / 3623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (347295153 / 1000000000) (173647577 / 500000000) (Real.log (3623 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3623 / 2560) = -Real.log (2560 / 3623) := by
    rw [show ((3623 / 2560) : ℝ) = ((2560 / 3623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (536544153 / 1000000000) ≤ -Real.log (1497 / 2560) ∧
    -Real.log (1497 / 2560) ≤ (268272077 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 4057)) (n := 12)
    (lo := (536544153 / 1000000000)) (hi := (268272077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1497) = 1/(1497 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) (Real.log (1497 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (259197717 / 1000000000) ≤ -Real.log (100000 / 129589) ∧
    -Real.log (100000 / 129589) ≤ (129598859 / 500000000) := by
  have h := checkLog_sound (w := (29589 / 229589)) (n := 12)
    (lo := (259197717 / 1000000000)) (hi := (129598859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129589 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129589 / 100000) = 1/(100000 / 129589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (259197717 / 1000000000) (129598859 / 500000000) (Real.log (129589 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (129589 / 100000) = -Real.log (100000 / 129589) := by
    rw [show ((129589 / 100000) : ℝ) = ((100000 / 129589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70164137 / 200000000) ≤ -Real.log (70411 / 100000) ∧
    -Real.log (70411 / 100000) ≤ (175410343 / 500000000) := by
  have h := checkLog_sound (w := (29589 / 170411)) (n := 12)
    (lo := (70164137 / 200000000)) (hi := (175410343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 70411) = 1/(70411 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-175410343 / 500000000) (-70164137 / 200000000) (Real.log (70411 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51905279 / 200000000) ≤ -Real.log (250000 / 324079) ∧
    -Real.log (250000 / 324079) ≤ (64881599 / 250000000) := by
  have h := checkLog_sound (w := (74079 / 574079)) (n := 12)
    (lo := (51905279 / 200000000)) (hi := (64881599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324079 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324079 / 250000) = 1/(250000 / 324079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51905279 / 200000000) (64881599 / 250000000) (Real.log (324079 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (324079 / 250000) = -Real.log (250000 / 324079) := by
    rw [show ((324079 / 250000) : ℝ) = ((250000 / 324079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (351425887 / 1000000000) ≤ -Real.log (175921 / 250000) ∧
    -Real.log (175921 / 250000) ≤ (10982059 / 31250000) := by
  have h := checkLog_sound (w := (74079 / 425921)) (n := 12)
    (lo := (351425887 / 1000000000)) (hi := (10982059 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175921) = 1/(175921 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10982059 / 31250000) (-351425887 / 1000000000) (Real.log (175921 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19426989 / 100000000) ≤ -Real.log (125000 / 151803) ∧
    -Real.log (125000 / 151803) ≤ (194269891 / 1000000000) := by
  have h := checkLog_sound (w := (26803 / 276803)) (n := 12)
    (lo := (19426989 / 100000000)) (hi := (194269891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151803 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151803 / 125000) = 1/(125000 / 151803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19426989 / 100000000) (194269891 / 1000000000) (Real.log (151803 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (151803 / 125000) = -Real.log (125000 / 151803) := by
    rw [show ((151803 / 125000) : ℝ) = ((125000 / 151803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (30167259 / 125000000) ≤ -Real.log (98197 / 125000) ∧
    -Real.log (98197 / 125000) ≤ (241338073 / 1000000000) := by
  have h := checkLog_sound (w := (26803 / 223197)) (n := 12)
    (lo := (30167259 / 125000000)) (hi := (241338073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98197) = 1/(98197 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-241338073 / 1000000000) (-30167259 / 125000000) (Real.log (98197 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194536647 / 1000000000) ≤ -Real.log (250000 / 303687) ∧
    -Real.log (250000 / 303687) ≤ (24317081 / 125000000) := by
  have h := checkLog_sound (w := (53687 / 553687)) (n := 12)
    (lo := (194536647 / 1000000000)) (hi := (24317081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303687 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303687 / 250000) = 1/(250000 / 303687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194536647 / 1000000000) (24317081 / 125000000) (Real.log (303687 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (303687 / 250000) = -Real.log (250000 / 303687) := by
    rw [show ((303687 / 250000) : ℝ) = ((250000 / 303687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (241750593 / 1000000000) ≤ -Real.log (196313 / 250000) ∧
    -Real.log (196313 / 250000) ≤ (120875297 / 500000000) := by
  have h := checkLog_sound (w := (53687 / 446313)) (n := 12)
    (lo := (241750593 / 1000000000)) (hi := (120875297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196313) = 1/(196313 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120875297 / 500000000) (-241750593 / 1000000000) (Real.log (196313 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (305009201 / 500000000) ≤ -Real.log (100000000000 / 184046526821) ∧
    -Real.log (100000000000 / 184046526821) ≤ (610018403 / 1000000000) := by
  have h := checkLog_sound (w := (84046526821 / 284046526821)) (n := 12)
    (lo := (305009201 / 500000000)) (hi := (610018403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184046526821 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184046526821 / 100000000000) = 1/(100000000000 / 184046526821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305009201 / 500000000) (610018403 / 1000000000) (Real.log (184046526821 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184046526821 / 100000000000) = -Real.log (100000000000 / 184046526821) := by
    rw [show ((184046526821 / 100000000000) : ℝ) = ((100000000000 / 184046526821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305476141 / 500000000) ≤ -Real.log (500000000000 / 921092422167) ∧
    -Real.log (500000000000 / 921092422167) ≤ (610952283 / 1000000000) := by
  have h := checkLog_sound (w := (421092422167 / 1421092422167)) (n := 12)
    (lo := (305476141 / 500000000)) (hi := (610952283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921092422167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921092422167 / 500000000000) = 1/(500000000000 / 921092422167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305476141 / 500000000) (610952283 / 1000000000) (Real.log (921092422167 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (921092422167 / 500000000000) = -Real.log (500000000000 / 921092422167) := by
    rw [show ((921092422167 / 500000000000) : ℝ) = ((500000000000 / 921092422167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217803981 / 500000000) ≤ -Real.log (250000000000 / 386475656079) ∧
    -Real.log (250000000000 / 386475656079) ≤ (435607963 / 1000000000) := by
  have h := checkLog_sound (w := (136475656079 / 636475656079)) (n := 12)
    (lo := (217803981 / 500000000)) (hi := (435607963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386475656079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386475656079 / 250000000000) = 1/(250000000000 / 386475656079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217803981 / 500000000) (435607963 / 1000000000) (Real.log (386475656079 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (386475656079 / 250000000000) = -Real.log (250000000000 / 386475656079) := by
    rw [show ((386475656079 / 250000000000) : ℝ) = ((250000000000 / 386475656079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (436287241 / 1000000000) ≤ -Real.log (31250000000 / 48342283751) ∧
    -Real.log (31250000000 / 48342283751) ≤ (218143621 / 500000000) := by
  have h := checkLog_sound (w := (17092283751 / 79592283751)) (n := 12)
    (lo := (436287241 / 1000000000)) (hi := (218143621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48342283751 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48342283751 / 31250000000) = 1/(31250000000 / 48342283751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (436287241 / 1000000000) (218143621 / 500000000) (Real.log (48342283751 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48342283751 / 31250000000) = -Real.log (31250000000 / 48342283751) := by
    rw [show ((48342283751 / 31250000000) : ℝ) = ((31250000000 / 48342283751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0447
