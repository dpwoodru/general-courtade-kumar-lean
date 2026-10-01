import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell079
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

theorem reflection_log_1_neg : (64989381 / 250000000) ≤ -Real.log (64 / 83) ∧
    -Real.log (64 / 83) ≤ (10398301 / 40000000) := by
  have h := checkLog_sound (w := (19 / 147)) (n := 12)
    (lo := (64989381 / 250000000)) (hi := (10398301 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 64) = 1/(64 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (64989381 / 250000000) (10398301 / 40000000) (Real.log (83 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (83 / 64) = -Real.log (64 / 83) := by
    rw [show ((83 / 64) : ℝ) = ((64 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (352220593 / 1000000000) ≤ -Real.log (45 / 64) ∧
    -Real.log (45 / 64) ≤ (176110297 / 500000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 45) = 1/(45 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176110297 / 500000000) (-352220593 / 1000000000) (Real.log (45 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51901123 / 200000000) ≤ -Real.log (5120 / 6637) ∧
    -Real.log (5120 / 6637) ≤ (16219101 / 62500000) := by
  have h := checkLog_sound (w := (1517 / 11757)) (n := 12)
    (lo := (51901123 / 200000000)) (hi := (16219101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 5120) = 1/(5120 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51901123 / 200000000) (16219101 / 62500000) (Real.log (6637 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6637 / 5120) = -Real.log (5120 / 6637) := by
    rw [show ((6637 / 5120) : ℝ) = ((5120 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (351387607 / 1000000000) ≤ -Real.log (3603 / 5120) ∧
    -Real.log (3603 / 5120) ≤ (43923451 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 8723)) (n := 12)
    (lo := (351387607 / 1000000000)) (hi := (43923451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3603) = 1/(3603 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-43923451 / 125000000) (-351387607 / 1000000000) (Real.log (3603 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190870741 / 1000000000) ≤ -Real.log (1000000 / 1210303) ∧
    -Real.log (1000000 / 1210303) ≤ (95435371 / 500000000) := by
  have h := checkLog_sound (w := (210303 / 2210303)) (n := 12)
    (lo := (190870741 / 1000000000)) (hi := (95435371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210303 / 1000000) = 1/(1000000 / 1210303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190870741 / 1000000000) (95435371 / 500000000) (Real.log (1210303 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1210303 / 1000000) = -Real.log (1000000 / 1210303) := by
    rw [show ((1210303 / 1000000) : ℝ) = ((1000000 / 1210303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (236105951 / 1000000000) ≤ -Real.log (789697 / 1000000) ∧
    -Real.log (789697 / 1000000) ≤ (7378311 / 31250000) := by
  have h := checkLog_sound (w := (210303 / 1789697)) (n := 12)
    (lo := (236105951 / 1000000000)) (hi := (7378311 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789697) = 1/(789697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7378311 / 31250000) (-236105951 / 1000000000) (Real.log (789697 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191217701 / 1000000000) ≤ -Real.log (1000000 / 1210723) ∧
    -Real.log (1000000 / 1210723) ≤ (95608851 / 500000000) := by
  have h := checkLog_sound (w := (210723 / 2210723)) (n := 12)
    (lo := (191217701 / 1000000000)) (hi := (95608851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210723 / 1000000) = 1/(1000000 / 1210723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191217701 / 1000000000) (95608851 / 500000000) (Real.log (1210723 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1210723 / 1000000) = -Real.log (1000000 / 1210723) := by
    rw [show ((1210723 / 1000000) : ℝ) = ((1000000 / 1210723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (118318971 / 500000000) ≤ -Real.log (789277 / 1000000) ∧
    -Real.log (789277 / 1000000) ≤ (236637943 / 1000000000) := by
  have h := checkLog_sound (w := (210723 / 1789277)) (n := 12)
    (lo := (118318971 / 500000000)) (hi := (236637943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789277) = 1/(789277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-236637943 / 1000000000) (-118318971 / 500000000) (Real.log (789277 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (140241827 / 1000000000) ≤ -Real.log (125000 / 143819) ∧
    -Real.log (125000 / 143819) ≤ (35060457 / 250000000) := by
  have h := checkLog_sound (w := (18819 / 268819)) (n := 12)
    (lo := (140241827 / 1000000000)) (hi := (35060457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143819 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143819 / 125000) = 1/(125000 / 143819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (140241827 / 1000000000) (35060457 / 250000000) (Real.log (143819 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143819 / 125000) = -Real.log (125000 / 143819) := by
    rw [show ((143819 / 125000) : ℝ) = ((125000 / 143819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20396069 / 125000000) ≤ -Real.log (106181 / 125000) ∧
    -Real.log (106181 / 125000) ≤ (163168553 / 1000000000) := by
  have h := checkLog_sound (w := (18819 / 231181)) (n := 12)
    (lo := (20396069 / 125000000)) (hi := (163168553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106181) = 1/(106181 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-163168553 / 1000000000) (-20396069 / 125000000) (Real.log (106181 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8781843 / 62500000) ≤ -Real.log (50000 / 57543) ∧
    -Real.log (50000 / 57543) ≤ (140509489 / 1000000000) := by
  have h := checkLog_sound (w := (7543 / 107543)) (n := 12)
    (lo := (8781843 / 62500000)) (hi := (140509489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57543 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57543 / 50000) = 1/(50000 / 57543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8781843 / 62500000) (140509489 / 1000000000) (Real.log (57543 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57543 / 50000) = -Real.log (50000 / 57543) := by
    rw [show ((57543 / 50000) : ℝ) = ((50000 / 57543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81765603 / 500000000) ≤ -Real.log (42457 / 50000) ∧
    -Real.log (42457 / 50000) ≤ (163531207 / 1000000000) := by
  have h := checkLog_sound (w := (7543 / 92457)) (n := 12)
    (lo := (81765603 / 500000000)) (hi := (163531207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42457) = 1/(42457 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-163531207 / 1000000000) (-81765603 / 500000000) (Real.log (42457 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305446611 / 500000000) ≤ -Real.log (125000000000 / 230259505967) ∧
    -Real.log (125000000000 / 230259505967) ≤ (610893223 / 1000000000) := by
  have h := checkLog_sound (w := (105259505967 / 355259505967)) (n := 12)
    (lo := (305446611 / 500000000)) (hi := (610893223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230259505967 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230259505967 / 125000000000) = 1/(125000000000 / 230259505967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305446611 / 500000000) (610893223 / 1000000000) (Real.log (230259505967 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (230259505967 / 125000000000) = -Real.log (125000000000 / 230259505967) := by
    rw [show ((230259505967 / 125000000000) : ℝ) = ((125000000000 / 230259505967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (306089059 / 500000000) ≤ -Real.log (500000000000 / 922222222223) ∧
    -Real.log (500000000000 / 922222222223) ≤ (612178119 / 1000000000) := by
  have h := checkLog_sound (w := (422222222223 / 1422222222223)) (n := 12)
    (lo := (306089059 / 500000000)) (hi := (612178119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((922222222223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(922222222223 / 500000000000) = 1/(500000000000 / 922222222223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (306089059 / 500000000) (612178119 / 1000000000) (Real.log (922222222223 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (922222222223 / 500000000000) = -Real.log (500000000000 / 922222222223) := by
    rw [show ((922222222223 / 500000000000) : ℝ) = ((500000000000 / 922222222223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106744173 / 250000000) ≤ -Real.log (50000000000 / 76630847021) ∧
    -Real.log (50000000000 / 76630847021) ≤ (426976693 / 1000000000) := by
  have h := checkLog_sound (w := (26630847021 / 126630847021)) (n := 12)
    (lo := (106744173 / 250000000)) (hi := (426976693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76630847021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76630847021 / 50000000000) = 1/(50000000000 / 76630847021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106744173 / 250000000) (426976693 / 1000000000) (Real.log (76630847021 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (76630847021 / 50000000000) = -Real.log (50000000000 / 76630847021) := by
    rw [show ((76630847021 / 50000000000) : ℝ) = ((50000000000 / 76630847021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106963911 / 250000000) ≤ -Real.log (250000000000 / 383491157097) ∧
    -Real.log (250000000000 / 383491157097) ≤ (85571129 / 200000000) := by
  have h := checkLog_sound (w := (133491157097 / 633491157097)) (n := 12)
    (lo := (106963911 / 250000000)) (hi := (85571129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383491157097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383491157097 / 250000000000) = 1/(250000000000 / 383491157097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (106963911 / 250000000) (85571129 / 200000000) (Real.log (383491157097 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (383491157097 / 250000000000) = -Real.log (250000000000 / 383491157097) := by
    rw [show ((383491157097 / 250000000000) : ℝ) = ((250000000000 / 383491157097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (303410379 / 1000000000) ≤ -Real.log (250000000000 / 338617549279) ∧
    -Real.log (250000000000 / 338617549279) ≤ (15170519 / 50000000) := by
  have h := checkLog_sound (w := (88617549279 / 588617549279)) (n := 12)
    (lo := (303410379 / 1000000000)) (hi := (15170519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338617549279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338617549279 / 250000000000) = 1/(250000000000 / 338617549279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (303410379 / 1000000000) (15170519 / 50000000) (Real.log (338617549279 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338617549279 / 250000000000) = -Real.log (250000000000 / 338617549279) := by
    rw [show ((338617549279 / 250000000000) : ℝ) = ((250000000000 / 338617549279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (60808139 / 200000000) ≤ -Real.log (500000000000 / 677662105189) ∧
    -Real.log (500000000000 / 677662105189) ≤ (38005087 / 125000000) := by
  have h := checkLog_sound (w := (177662105189 / 1177662105189)) (n := 12)
    (lo := (60808139 / 200000000)) (hi := (38005087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677662105189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677662105189 / 500000000000) = 1/(500000000000 / 677662105189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (60808139 / 200000000) (38005087 / 125000000) (Real.log (677662105189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (677662105189 / 500000000000) = -Real.log (500000000000 / 677662105189) := by
    rw [show ((677662105189 / 500000000000) : ℝ) = ((500000000000 / 677662105189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23021717 / 1000000000) ≤ -Real.log (2443103151 / 2500000000) ∧
    -Real.log (2443103151 / 2500000000) ≤ (11510859 / 500000000) := by
  have h := checkLog_sound (w := (56896849 / 4943103151)) (n := 12)
    (lo := (23021717 / 1000000000)) (hi := (11510859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2443103151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2443103151) = 1/(2443103151 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11510859 / 500000000) (-23021717 / 1000000000) (Real.log (2443103151 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (917069 / 40000000) ≤ -Real.log (15270845239 / 15625000000) ∧
    -Real.log (15270845239 / 15625000000) ≤ (11463363 / 500000000) := by
  have h := checkLog_sound (w := (354154761 / 30895845239)) (n := 12)
    (lo := (917069 / 40000000)) (hi := (11463363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15270845239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15270845239) = 1/(15270845239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11463363 / 500000000) (-917069 / 40000000) (Real.log (15270845239 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell079
