import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0224
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

theorem reflection_log_1_neg : (254823887 / 1000000000) ≤ -Real.log (2560 / 3303) ∧
    -Real.log (2560 / 3303) ≤ (15926493 / 62500000) := by
  have h := checkLog_sound (w := (743 / 5863)) (n := 12)
    (lo := (254823887 / 1000000000)) (hi := (15926493 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3303 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3303 / 2560) = 1/(2560 / 3303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254823887 / 1000000000) (15926493 / 62500000) (Real.log (3303 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3303 / 2560) = -Real.log (2560 / 3303) := by
    rw [show ((3303 / 2560) : ℝ) = ((2560 / 3303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (342820469 / 1000000000) ≤ -Real.log (1817 / 2560) ∧
    -Real.log (1817 / 2560) ≤ (34282047 / 100000000) := by
  have h := checkLog_sound (w := (743 / 4377)) (n := 12)
    (lo := (342820469 / 1000000000)) (hi := (34282047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1817) = 1/(1817 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34282047 / 100000000) (-342820469 / 1000000000) (Real.log (1817 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (63592413 / 250000000) ≤ -Real.log (5120 / 6603) ∧
    -Real.log (5120 / 6603) ≤ (254369653 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 11723)) (n := 12)
    (lo := (63592413 / 250000000)) (hi := (254369653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6603 / 5120) = 1/(5120 / 6603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (63592413 / 250000000) (254369653 / 1000000000) (Real.log (6603 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6603 / 5120) = -Real.log (5120 / 6603) := by
    rw [show ((6603 / 5120) : ℝ) = ((5120 / 6603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (341995273 / 1000000000) ≤ -Real.log (3637 / 5120) ∧
    -Real.log (3637 / 5120) ≤ (170997637 / 500000000) := by
  have h := checkLog_sound (w := (1483 / 8757)) (n := 12)
    (lo := (341995273 / 1000000000)) (hi := (170997637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3637) = 1/(3637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170997637 / 500000000) (-341995273 / 1000000000) (Real.log (3637 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11443037 / 25000000) ≤ -Real.log (1280 / 2023) ∧
    -Real.log (1280 / 2023) ≤ (457721481 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 3303)) (n := 12)
    (lo := (11443037 / 25000000)) (hi := (457721481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2023 / 1280) = 1/(1280 / 2023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11443037 / 25000000) (457721481 / 1000000000) (Real.log (2023 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2023 / 1280) = -Real.log (1280 / 2023) := by
    rw [show ((2023 / 1280) : ℝ) = ((1280 / 2023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (868617261 / 1000000000) ≤ -Real.log (537 / 1280) ∧
    -Real.log (537 / 1280) ≤ (868617263 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1177)) (n := 12)
    (lo := (175470081 / 1000000000)) (hi := (87735041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 537) = 1/(537 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-868617263 / 1000000000) (-868617261 / 1000000000) (Real.log (537 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (114244933 / 250000000) ≤ -Real.log (2560 / 4043) ∧
    -Real.log (2560 / 4043) ≤ (456979733 / 1000000000) := by
  have h := checkLog_sound (w := (1483 / 6603)) (n := 12)
    (lo := (114244933 / 250000000)) (hi := (456979733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4043 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4043 / 2560) = 1/(2560 / 4043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (114244933 / 250000000) (456979733 / 1000000000) (Real.log (4043 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4043 / 2560) = -Real.log (2560 / 4043) := by
    rw [show ((4043 / 2560) : ℝ) = ((2560 / 4043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (865827859 / 1000000000) ≤ -Real.log (1077 / 2560) ∧
    -Real.log (1077 / 2560) ≤ (865827861 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2357)) (n := 12)
    (lo := (172680679 / 1000000000)) (hi := (4317017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1077) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1077) = 1/(1077 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-865827861 / 1000000000) (-865827859 / 1000000000) (Real.log (1077 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (348071843 / 1000000000) ≤ -Real.log (500000 / 708167) ∧
    -Real.log (500000 / 708167) ≤ (87017961 / 250000000) := by
  have h := checkLog_sound (w := (208167 / 1208167)) (n := 12)
    (lo := (348071843 / 1000000000)) (hi := (87017961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708167 / 500000) = 1/(500000 / 708167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (348071843 / 1000000000) (87017961 / 250000000) (Real.log (708167 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (708167 / 500000) = -Real.log (500000 / 708167) := by
    rw [show ((708167 / 500000) : ℝ) = ((500000 / 708167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (538426377 / 1000000000) ≤ -Real.log (291833 / 500000) ∧
    -Real.log (291833 / 500000) ≤ (269213189 / 500000000) := by
  have h := checkLog_sound (w := (208167 / 791833)) (n := 12)
    (lo := (538426377 / 1000000000)) (hi := (269213189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 291833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 291833) = 1/(291833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-269213189 / 500000000) (-538426377 / 1000000000) (Real.log (291833 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (87172361 / 250000000) ≤ -Real.log (1000000 / 1417209) ∧
    -Real.log (1000000 / 1417209) ≤ (69737889 / 200000000) := by
  have h := checkLog_sound (w := (417209 / 2417209)) (n := 12)
    (lo := (87172361 / 250000000)) (hi := (69737889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417209 / 1000000) = 1/(1000000 / 1417209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (87172361 / 250000000) (69737889 / 200000000) (Real.log (1417209 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1417209 / 1000000) = -Real.log (1000000 / 1417209) := by
    rw [show ((1417209 / 1000000) : ℝ) = ((1000000 / 1417209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (539926647 / 1000000000) ≤ -Real.log (582791 / 1000000) ∧
    -Real.log (582791 / 1000000) ≤ (67490831 / 125000000) := by
  have h := checkLog_sound (w := (417209 / 1582791)) (n := 12)
    (lo := (539926647 / 1000000000)) (hi := (67490831 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 582791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 582791) = 1/(582791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67490831 / 125000000) (-539926647 / 1000000000) (Real.log (582791 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (134709659 / 500000000) ≤ -Real.log (250000 / 327301) ∧
    -Real.log (250000 / 327301) ≤ (269419319 / 1000000000) := by
  have h := checkLog_sound (w := (77301 / 577301)) (n := 12)
    (lo := (134709659 / 500000000)) (hi := (269419319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327301 / 250000) = 1/(250000 / 327301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (134709659 / 500000000) (269419319 / 1000000000) (Real.log (327301 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (327301 / 250000) = -Real.log (250000 / 327301) := by
    rw [show ((327301 / 250000) : ℝ) = ((250000 / 327301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369910723 / 1000000000) ≤ -Real.log (172699 / 250000) ∧
    -Real.log (172699 / 250000) ≤ (92477681 / 250000000) := by
  have h := checkLog_sound (w := (77301 / 422699)) (n := 12)
    (lo := (369910723 / 1000000000)) (hi := (92477681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 172699) = 1/(172699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-92477681 / 250000000) (-369910723 / 1000000000) (Real.log (172699 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (134983033 / 500000000) ≤ -Real.log (6250 / 8187) ∧
    -Real.log (6250 / 8187) ≤ (269966067 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 14437)) (n := 12)
    (lo := (134983033 / 500000000)) (hi := (269966067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8187 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8187 / 6250) = 1/(6250 / 8187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134983033 / 500000000) (269966067 / 1000000000) (Real.log (8187 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (8187 / 6250) = -Real.log (6250 / 8187) := by
    rw [show ((8187 / 6250) : ℝ) = ((6250 / 8187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (185473873 / 500000000) ≤ -Real.log (4313 / 6250) ∧
    -Real.log (4313 / 6250) ≤ (370947747 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 10563)) (n := 12)
    (lo := (185473873 / 500000000)) (hi := (370947747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4313) = 1/(4313 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-370947747 / 1000000000) (-185473873 / 500000000) (Real.log (4313 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (44324911 / 50000000) ≤ -Real.log (125000000000 / 303327159711) ∧
    -Real.log (125000000000 / 303327159711) ≤ (443249111 / 500000000) := by
  have h := checkLog_sound (w := (53327159711 / 553327159711)) (n := 12)
    (lo := (302111 / 1562500)) (hi := (193351041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303327159711 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(303327159711 / 250000000000) = 1/(125000000000 / 303327159711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (44324911 / 50000000) (443249111 / 500000000) (Real.log (303327159711 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (303327159711 / 125000000000) = -Real.log (125000000000 / 303327159711) := by
    rw [show ((303327159711 / 125000000000) : ℝ) = ((125000000000 / 303327159711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (888616091 / 1000000000) ≤ -Real.log (250000000000 / 607940496679) ∧
    -Real.log (250000000000 / 607940496679) ≤ (888616093 / 1000000000) := by
  have h := checkLog_sound (w := (107940496679 / 1107940496679)) (n := 12)
    (lo := (195468911 / 1000000000)) (hi := (12216807 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607940496679 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(607940496679 / 500000000000) = 1/(250000000000 / 607940496679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (888616091 / 1000000000) (888616093 / 1000000000) (Real.log (607940496679 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (607940496679 / 250000000000) = -Real.log (250000000000 / 607940496679) := by
    rw [show ((607940496679 / 250000000000) : ℝ) = ((250000000000 / 607940496679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (319665021 / 500000000) ≤ -Real.log (250000000000 / 473802685597) ∧
    -Real.log (250000000000 / 473802685597) ≤ (639330043 / 1000000000) := by
  have h := checkLog_sound (w := (223802685597 / 723802685597)) (n := 12)
    (lo := (319665021 / 500000000)) (hi := (639330043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473802685597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473802685597 / 250000000000) = 1/(250000000000 / 473802685597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (319665021 / 500000000) (639330043 / 1000000000) (Real.log (473802685597 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (473802685597 / 250000000000) = -Real.log (250000000000 / 473802685597) := by
    rw [show ((473802685597 / 250000000000) : ℝ) = ((250000000000 / 473802685597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (160228453 / 250000000) ≤ -Real.log (500000000000 / 949107349873) ∧
    -Real.log (500000000000 / 949107349873) ≤ (640913813 / 1000000000) := by
  have h := checkLog_sound (w := (449107349873 / 1449107349873)) (n := 12)
    (lo := (160228453 / 250000000)) (hi := (640913813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949107349873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949107349873 / 500000000000) = 1/(500000000000 / 949107349873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (160228453 / 250000000) (640913813 / 1000000000) (Real.log (949107349873 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (949107349873 / 500000000000) = -Real.log (500000000000 / 949107349873) := by
    rw [show ((949107349873 / 500000000000) : ℝ) = ((500000000000 / 949107349873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0224
