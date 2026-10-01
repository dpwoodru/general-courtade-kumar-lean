import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0195
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

theorem reflection_log_1_neg : (53581553 / 200000000) ≤ -Real.log (5120 / 6693) ∧
    -Real.log (5120 / 6693) ≤ (133953883 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 11813)) (n := 12)
    (lo := (53581553 / 200000000)) (hi := (133953883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6693 / 5120) = 1/(5120 / 6693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53581553 / 200000000) (133953883 / 500000000) (Real.log (6693 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6693 / 5120) = -Real.log (5120 / 6693) := by
    rw [show ((6693 / 5120) : ℝ) = ((5120 / 6693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (367052263 / 1000000000) ≤ -Real.log (3547 / 5120) ∧
    -Real.log (3547 / 5120) ≤ (45881533 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 8667)) (n := 12)
    (lo := (367052263 / 1000000000)) (hi := (45881533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3547) = 1/(3547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45881533 / 125000000) (-367052263 / 1000000000) (Real.log (3547 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53491887 / 200000000) ≤ -Real.log (512 / 669) ∧
    -Real.log (512 / 669) ≤ (66864859 / 250000000) := by
  have h := checkLog_sound (w := (157 / 1181)) (n := 12)
    (lo := (53491887 / 200000000)) (hi := (66864859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669 / 512) = 1/(512 / 669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53491887 / 200000000) (66864859 / 250000000) (Real.log (669 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (669 / 512) = -Real.log (512 / 669) := by
    rw [show ((669 / 512) : ℝ) = ((512 / 669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73241367 / 200000000) ≤ -Real.log (355 / 512) ∧
    -Real.log (355 / 512) ≤ (91551709 / 250000000) := by
  have h := checkLog_sound (w := (157 / 867)) (n := 12)
    (lo := (73241367 / 200000000)) (hi := (91551709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 355) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 355) = 1/(355 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91551709 / 250000000) (-73241367 / 200000000) (Real.log (355 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (478996277 / 1000000000) ≤ -Real.log (2560 / 4133) ∧
    -Real.log (2560 / 4133) ≤ (239498139 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 6693)) (n := 12)
    (lo := (478996277 / 1000000000)) (hi := (239498139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4133 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4133 / 2560) = 1/(2560 / 4133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (478996277 / 1000000000) (239498139 / 500000000) (Real.log (4133 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4133 / 2560) = -Real.log (2560 / 4133) := by
    rw [show ((4133 / 2560) : ℝ) = ((2560 / 4133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (953092497 / 1000000000) ≤ -Real.log (987 / 2560) ∧
    -Real.log (987 / 2560) ≤ (953092499 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2267)) (n := 12)
    (lo := (259945317 / 1000000000)) (hi := (129972659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 987) = 1/(987 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-953092499 / 1000000000) (-953092497 / 1000000000) (Real.log (987 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119567537 / 250000000) ≤ -Real.log (256 / 413) ∧
    -Real.log (256 / 413) ≤ (478270149 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 669)) (n := 12)
    (lo := (119567537 / 250000000)) (hi := (478270149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413 / 256) = 1/(256 / 413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119567537 / 250000000) (478270149 / 1000000000) (Real.log (413 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (413 / 256) = -Real.log (256 / 413) := by
    rw [show ((413 / 256) : ℝ) = ((256 / 413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (950057593 / 1000000000) ≤ -Real.log (99 / 256) ∧
    -Real.log (99 / 256) ≤ (190011519 / 200000000) := by
  have h := checkLog_sound (w := (29 / 227)) (n := 12)
    (lo := (256910413 / 1000000000)) (hi := (128455207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 99) = 1/(99 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-190011519 / 200000000) (-950057593 / 1000000000) (Real.log (99 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91472563 / 250000000) ≤ -Real.log (1000000 / 1441797) ∧
    -Real.log (1000000 / 1441797) ≤ (365890253 / 1000000000) := by
  have h := checkLog_sound (w := (441797 / 2441797)) (n := 12)
    (lo := (91472563 / 250000000)) (hi := (365890253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441797 / 1000000) = 1/(1000000 / 1441797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91472563 / 250000000) (365890253 / 1000000000) (Real.log (1441797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1441797 / 1000000) = -Real.log (1000000 / 1441797) := by
    rw [show ((1441797 / 1000000) : ℝ) = ((1000000 / 1441797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (583032583 / 1000000000) ≤ -Real.log (558203 / 1000000) ∧
    -Real.log (558203 / 1000000) ≤ (72879073 / 125000000) := by
  have h := checkLog_sound (w := (441797 / 1558203)) (n := 12)
    (lo := (583032583 / 1000000000)) (hi := (72879073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 558203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 558203) = 1/(558203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72879073 / 125000000) (-583032583 / 1000000000) (Real.log (558203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183251247 / 500000000) ≤ -Real.log (25000 / 36067) ∧
    -Real.log (25000 / 36067) ≤ (73300499 / 200000000) := by
  have h := checkLog_sound (w := (11067 / 61067)) (n := 12)
    (lo := (183251247 / 500000000)) (hi := (73300499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36067 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36067 / 25000) = 1/(25000 / 36067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183251247 / 500000000) (73300499 / 200000000) (Real.log (36067 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (36067 / 25000) = -Real.log (25000 / 36067) := by
    rw [show ((36067 / 25000) : ℝ) = ((25000 / 36067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (584615697 / 1000000000) ≤ -Real.log (13933 / 25000) ∧
    -Real.log (13933 / 25000) ≤ (292307849 / 500000000) := by
  have h := checkLog_sound (w := (11067 / 38933)) (n := 12)
    (lo := (584615697 / 1000000000)) (hi := (292307849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13933) = 1/(13933 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-292307849 / 500000000) (-584615697 / 1000000000) (Real.log (13933 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (142664653 / 500000000) ≤ -Real.log (5000 / 6651) ∧
    -Real.log (5000 / 6651) ≤ (285329307 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 11651)) (n := 12)
    (lo := (142664653 / 500000000)) (hi := (285329307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5000) = 1/(5000 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (142664653 / 500000000) (285329307 / 1000000000) (Real.log (6651 / 5000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (6651 / 5000) = -Real.log (5000 / 6651) := by
    rw [show ((6651 / 5000) : ℝ) = ((5000 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (200388059 / 500000000) ≤ -Real.log (3349 / 5000) ∧
    -Real.log (3349 / 5000) ≤ (400776119 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 8349)) (n := 12)
    (lo := (200388059 / 500000000)) (hi := (400776119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3349) = 1/(3349 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-400776119 / 1000000000) (-200388059 / 500000000) (Real.log (3349 / 5000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (142940851 / 500000000) ≤ -Real.log (200000 / 266187) ∧
    -Real.log (200000 / 266187) ≤ (285881703 / 1000000000) := by
  have h := checkLog_sound (w := (66187 / 466187)) (n := 12)
    (lo := (142940851 / 500000000)) (hi := (285881703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266187 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266187 / 200000) = 1/(200000 / 266187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142940851 / 500000000) (285881703 / 1000000000) (Real.log (266187 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (266187 / 200000) = -Real.log (200000 / 266187) := by
    rw [show ((266187 / 200000) : ℝ) = ((200000 / 266187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (401874063 / 1000000000) ≤ -Real.log (133813 / 200000) ∧
    -Real.log (133813 / 200000) ≤ (25117129 / 62500000) := by
  have h := checkLog_sound (w := (66187 / 333813)) (n := 12)
    (lo := (401874063 / 1000000000)) (hi := (25117129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133813) = 1/(133813 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-25117129 / 62500000) (-401874063 / 1000000000) (Real.log (133813 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189784567 / 200000000) ≤ -Real.log (250000000000 / 645731481199) ∧
    -Real.log (250000000000 / 645731481199) ≤ (948922837 / 1000000000) := by
  have h := checkLog_sound (w := (145731481199 / 1145731481199)) (n := 12)
    (lo := (51155131 / 200000000)) (hi := (31971957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645731481199 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(645731481199 / 500000000000) = 1/(250000000000 / 645731481199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189784567 / 200000000) (948922837 / 1000000000) (Real.log (645731481199 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645731481199 / 250000000000) = -Real.log (250000000000 / 645731481199) := by
    rw [show ((645731481199 / 250000000000) : ℝ) = ((250000000000 / 645731481199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59444887 / 62500000) ≤ -Real.log (20000000000 / 51772051963) ∧
    -Real.log (20000000000 / 51772051963) ≤ (475559097 / 500000000) := by
  have h := checkLog_sound (w := (11772051963 / 91772051963)) (n := 12)
    (lo := (64492753 / 250000000)) (hi := (257971013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51772051963 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51772051963 / 40000000000) = 1/(20000000000 / 51772051963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59444887 / 62500000) (475559097 / 500000000) (Real.log (51772051963 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51772051963 / 20000000000) = -Real.log (20000000000 / 51772051963) := by
    rw [show ((51772051963 / 20000000000) : ℝ) = ((20000000000 / 51772051963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27444217 / 40000000) ≤ -Real.log (250000000000 / 496491489997) ∧
    -Real.log (250000000000 / 496491489997) ≤ (343052713 / 500000000) := by
  have h := checkLog_sound (w := (246491489997 / 746491489997)) (n := 12)
    (lo := (27444217 / 40000000)) (hi := (343052713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((496491489997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(496491489997 / 250000000000) = 1/(250000000000 / 496491489997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (27444217 / 40000000) (343052713 / 500000000) (Real.log (496491489997 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (496491489997 / 250000000000) = -Real.log (250000000000 / 496491489997) := by
    rw [show ((496491489997 / 250000000000) : ℝ) = ((250000000000 / 496491489997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (343877883 / 500000000) ≤ -Real.log (250000000000 / 497311546711) ∧
    -Real.log (250000000000 / 497311546711) ≤ (687755767 / 1000000000) := by
  have h := checkLog_sound (w := (247311546711 / 747311546711)) (n := 12)
    (lo := (343877883 / 500000000)) (hi := (687755767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497311546711 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497311546711 / 250000000000) = 1/(250000000000 / 497311546711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (343877883 / 500000000) (687755767 / 1000000000) (Real.log (497311546711 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (497311546711 / 250000000000) = -Real.log (250000000000 / 497311546711) := by
    rw [show ((497311546711 / 250000000000) : ℝ) = ((250000000000 / 497311546711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0195
