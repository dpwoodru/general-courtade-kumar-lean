import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0337
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

theorem reflection_log_1_neg : (21522163 / 100000000) ≤ -Real.log (10240 / 12699) ∧
    -Real.log (10240 / 12699) ≤ (215221631 / 1000000000) := by
  have h := checkLog_sound (w := (2459 / 22939)) (n := 12)
    (lo := (21522163 / 100000000)) (hi := (215221631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12699 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12699 / 10240) = 1/(10240 / 12699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21522163 / 100000000) (215221631 / 1000000000) (Real.log (12699 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12699 / 10240) = -Real.log (10240 / 12699) := by
    rw [show ((12699 / 10240) : ℝ) = ((10240 / 12699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137308377 / 500000000) ≤ -Real.log (7781 / 10240) ∧
    -Real.log (7781 / 10240) ≤ (54923351 / 200000000) := by
  have h := checkLog_sound (w := (2459 / 18021)) (n := 12)
    (lo := (137308377 / 500000000)) (hi := (54923351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7781) = 1/(7781 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-54923351 / 200000000) (-137308377 / 500000000) (Real.log (7781 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214985363 / 1000000000) ≤ -Real.log (1280 / 1587) ∧
    -Real.log (1280 / 1587) ≤ (53746341 / 250000000) := by
  have h := checkLog_sound (w := (307 / 2867)) (n := 12)
    (lo := (214985363 / 1000000000)) (hi := (53746341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1587 / 1280) = 1/(1280 / 1587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214985363 / 1000000000) (53746341 / 250000000) (Real.log (1587 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1587 / 1280) = -Real.log (1280 / 1587) := by
    rw [show ((1587 / 1280) : ℝ) = ((1280 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137115637 / 500000000) ≤ -Real.log (973 / 1280) ∧
    -Real.log (973 / 1280) ≤ (10969251 / 40000000) := by
  have h := checkLog_sound (w := (307 / 2253)) (n := 12)
    (lo := (137115637 / 500000000)) (hi := (10969251 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 973) = 1/(973 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10969251 / 40000000) (-137115637 / 500000000) (Real.log (973 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15689073 / 40000000) ≤ -Real.log (5120 / 7579) ∧
    -Real.log (5120 / 7579) ≤ (196113413 / 500000000) := by
  have h := checkLog_sound (w := (2459 / 12699)) (n := 12)
    (lo := (15689073 / 40000000)) (hi := (196113413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7579 / 5120) = 1/(5120 / 7579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15689073 / 40000000) (196113413 / 500000000) (Real.log (7579 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7579 / 5120) = -Real.log (5120 / 7579) := by
    rw [show ((7579 / 5120) : ℝ) = ((5120 / 7579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (654452447 / 1000000000) ≤ -Real.log (2661 / 5120) ∧
    -Real.log (2661 / 5120) ≤ (20451639 / 31250000) := by
  have h := checkLog_sound (w := (2459 / 7781)) (n := 12)
    (lo := (654452447 / 1000000000)) (hi := (20451639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2661) = 1/(2661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20451639 / 31250000) (-654452447 / 1000000000) (Real.log (2661 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97957729 / 250000000) ≤ -Real.log (640 / 947) ∧
    -Real.log (640 / 947) ≤ (391830917 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 1587)) (n := 12)
    (lo := (97957729 / 250000000)) (hi := (391830917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((947 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(947 / 640) = 1/(640 / 947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97957729 / 250000000) (391830917 / 1000000000) (Real.log (947 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (947 / 640) = -Real.log (640 / 947) := by
    rw [show ((947 / 640) : ℝ) = ((640 / 947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (326662843 / 500000000) ≤ -Real.log (333 / 640) ∧
    -Real.log (333 / 640) ≤ (653325687 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 333) = 1/(333 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-653325687 / 1000000000) (-326662843 / 500000000) (Real.log (333 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (294754751 / 1000000000) ≤ -Real.log (1000000 / 1342797) ∧
    -Real.log (1000000 / 1342797) ≤ (4605543 / 15625000) := by
  have h := checkLog_sound (w := (342797 / 2342797)) (n := 12)
    (lo := (294754751 / 1000000000)) (hi := (4605543 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342797 / 1000000) = 1/(1000000 / 1342797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (294754751 / 1000000000) (4605543 / 15625000) (Real.log (1342797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1342797 / 1000000) = -Real.log (1000000 / 1342797) := by
    rw [show ((1342797 / 1000000) : ℝ) = ((1000000 / 1342797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52470291 / 125000000) ≤ -Real.log (657203 / 1000000) ∧
    -Real.log (657203 / 1000000) ≤ (419762329 / 1000000000) := by
  have h := checkLog_sound (w := (342797 / 1657203)) (n := 12)
    (lo := (52470291 / 125000000)) (hi := (419762329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657203) = 1/(657203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-419762329 / 1000000000) (-52470291 / 125000000) (Real.log (657203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (295074183 / 1000000000) ≤ -Real.log (500000 / 671613) ∧
    -Real.log (500000 / 671613) ≤ (36884273 / 125000000) := by
  have h := checkLog_sound (w := (171613 / 1171613)) (n := 12)
    (lo := (295074183 / 1000000000)) (hi := (36884273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671613 / 500000) = 1/(500000 / 671613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (295074183 / 1000000000) (36884273 / 125000000) (Real.log (671613 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (671613 / 500000) = -Real.log (500000 / 671613) := by
    rw [show ((671613 / 500000) : ℝ) = ((500000 / 671613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (420415307 / 1000000000) ≤ -Real.log (328387 / 500000) ∧
    -Real.log (328387 / 500000) ≤ (105103827 / 250000000) := by
  have h := checkLog_sound (w := (171613 / 828387)) (n := 12)
    (lo := (420415307 / 1000000000)) (hi := (105103827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328387) = 1/(328387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105103827 / 250000000) (-420415307 / 1000000000) (Real.log (328387 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (223576257 / 1000000000) ≤ -Real.log (1000000 / 1250541) ∧
    -Real.log (1000000 / 1250541) ≤ (111788129 / 500000000) := by
  have h := checkLog_sound (w := (250541 / 2250541)) (n := 12)
    (lo := (223576257 / 1000000000)) (hi := (111788129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250541 / 1000000) = 1/(1000000 / 1250541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (223576257 / 1000000000) (111788129 / 500000000) (Real.log (1250541 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1250541 / 1000000) = -Real.log (1000000 / 1250541) := by
    rw [show ((1250541 / 1000000) : ℝ) = ((1000000 / 1250541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144201833 / 500000000) ≤ -Real.log (749459 / 1000000) ∧
    -Real.log (749459 / 1000000) ≤ (288403667 / 1000000000) := by
  have h := checkLog_sound (w := (250541 / 1749459)) (n := 12)
    (lo := (144201833 / 500000000)) (hi := (288403667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749459) = 1/(749459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-288403667 / 1000000000) (-144201833 / 500000000) (Real.log (749459 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (44768821 / 200000000) ≤ -Real.log (250000 / 312719) ∧
    -Real.log (250000 / 312719) ≤ (111922053 / 500000000) := by
  have h := checkLog_sound (w := (62719 / 562719)) (n := 12)
    (lo := (44768821 / 200000000)) (hi := (111922053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312719 / 250000) = 1/(250000 / 312719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44768821 / 200000000) (111922053 / 500000000) (Real.log (312719 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (312719 / 250000) = -Real.log (250000 / 312719) := by
    rw [show ((312719 / 250000) : ℝ) = ((250000 / 312719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57770151 / 200000000) ≤ -Real.log (187281 / 250000) ∧
    -Real.log (187281 / 250000) ≤ (72212689 / 250000000) := by
  have h := checkLog_sound (w := (62719 / 437281)) (n := 12)
    (lo := (57770151 / 200000000)) (hi := (72212689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187281) = 1/(187281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-72212689 / 250000000) (-57770151 / 200000000) (Real.log (187281 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (714517079 / 1000000000) ≤ -Real.log (62500000000 / 127699983871) ∧
    -Real.log (62500000000 / 127699983871) ≤ (714517081 / 1000000000) := by
  have h := checkLog_sound (w := (2699983871 / 252699983871)) (n := 12)
    (lo := (21369899 / 1000000000)) (hi := (213699 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127699983871 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127699983871 / 125000000000) = 1/(62500000000 / 127699983871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (714517079 / 1000000000) (714517081 / 1000000000) (Real.log (127699983871 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (127699983871 / 62500000000) = -Real.log (62500000000 / 127699983871) := by
    rw [show ((127699983871 / 62500000000) : ℝ) = ((62500000000 / 127699983871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (71548949 / 100000000) ≤ -Real.log (250000000000 / 511296884469) ∧
    -Real.log (250000000000 / 511296884469) ≤ (178872373 / 250000000) := by
  have h := checkLog_sound (w := (11296884469 / 1011296884469)) (n := 12)
    (lo := (2234231 / 100000000)) (hi := (22342311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511296884469 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511296884469 / 500000000000) = 1/(250000000000 / 511296884469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (71548949 / 100000000) (178872373 / 250000000) (Real.log (511296884469 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (511296884469 / 250000000000) = -Real.log (250000000000 / 511296884469) := by
    rw [show ((511296884469 / 250000000000) : ℝ) = ((250000000000 / 511296884469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (511979923 / 1000000000) ≤ -Real.log (250000000000 / 417147902687) ∧
    -Real.log (250000000000 / 417147902687) ≤ (127994981 / 250000000) := by
  have h := checkLog_sound (w := (167147902687 / 667147902687)) (n := 12)
    (lo := (511979923 / 1000000000)) (hi := (127994981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417147902687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417147902687 / 250000000000) = 1/(250000000000 / 417147902687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (511979923 / 1000000000) (127994981 / 250000000) (Real.log (417147902687 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (417147902687 / 250000000000) = -Real.log (250000000000 / 417147902687) := by
    rw [show ((417147902687 / 250000000000) : ℝ) = ((250000000000 / 417147902687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25634743 / 50000000) ≤ -Real.log (6250000000 / 10436156097) ∧
    -Real.log (6250000000 / 10436156097) ≤ (512694861 / 1000000000) := by
  have h := checkLog_sound (w := (4186156097 / 16686156097)) (n := 12)
    (lo := (25634743 / 50000000)) (hi := (512694861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10436156097 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10436156097 / 6250000000) = 1/(6250000000 / 10436156097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25634743 / 50000000) (512694861 / 1000000000) (Real.log (10436156097 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10436156097 / 6250000000) = -Real.log (6250000000 / 10436156097) := by
    rw [show ((10436156097 / 6250000000) : ℝ) = ((6250000000 / 10436156097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0337
