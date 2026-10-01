import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0299
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

theorem reflection_log_1_neg : (11207933 / 50000000) ≤ -Real.log (10240 / 12813) ∧
    -Real.log (10240 / 12813) ≤ (224158661 / 1000000000) := by
  have h := checkLog_sound (w := (2573 / 23053)) (n := 12)
    (lo := (11207933 / 50000000)) (hi := (224158661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12813 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12813 / 10240) = 1/(10240 / 12813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11207933 / 50000000) (224158661 / 1000000000) (Real.log (12813 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12813 / 10240) = -Real.log (10240 / 12813) := by
    rw [show ((12813 / 10240) : ℝ) = ((10240 / 12813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57875243 / 200000000) ≤ -Real.log (7667 / 10240) ∧
    -Real.log (7667 / 10240) ≤ (36172027 / 125000000) := by
  have h := checkLog_sound (w := (2573 / 17907)) (n := 12)
    (lo := (57875243 / 200000000)) (hi := (36172027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7667) = 1/(7667 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-36172027 / 125000000) (-57875243 / 200000000) (Real.log (7667 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13995281 / 62500000) ≤ -Real.log (1024 / 1281) ∧
    -Real.log (1024 / 1281) ≤ (223924497 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 2305)) (n := 12)
    (lo := (13995281 / 62500000)) (hi := (223924497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281 / 1024) = 1/(1024 / 1281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13995281 / 62500000) (223924497 / 1000000000) (Real.log (1281 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1281 / 1024) = -Real.log (1024 / 1281) := by
    rw [show ((1281 / 1024) : ℝ) = ((1024 / 1281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (72246251 / 250000000) ≤ -Real.log (767 / 1024) ∧
    -Real.log (767 / 1024) ≤ (57797001 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1791)) (n := 12)
    (lo := (72246251 / 250000000)) (hi := (57797001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 767) = 1/(767 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57797001 / 200000000) (-72246251 / 250000000) (Real.log (767 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81431277 / 200000000) ≤ -Real.log (5120 / 7693) ∧
    -Real.log (5120 / 7693) ≤ (203578193 / 500000000) := by
  have h := checkLog_sound (w := (2573 / 12813)) (n := 12)
    (lo := (81431277 / 200000000)) (hi := (203578193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7693 / 5120) = 1/(5120 / 7693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81431277 / 200000000) (203578193 / 500000000) (Real.log (7693 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7693 / 5120) = -Real.log (5120 / 7693) := by
    rw [show ((7693 / 5120) : ℝ) = ((5120 / 7693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (349119121 / 500000000) ≤ -Real.log (2547 / 5120) ∧
    -Real.log (2547 / 5120) ≤ (174559561 / 250000000) := by
  have h := checkLog_sound (w := (13 / 5107)) (n := 12)
    (lo := (2545531 / 500000000)) (hi := (5091063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2547) = 1/(2547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-174559561 / 250000000) (-349119121 / 500000000) (Real.log (2547 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50845793 / 125000000) ≤ -Real.log (512 / 769) ∧
    -Real.log (512 / 769) ≤ (81353269 / 200000000) := by
  have h := checkLog_sound (w := (257 / 1281)) (n := 12)
    (lo := (50845793 / 125000000)) (hi := (81353269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769 / 512) = 1/(512 / 769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50845793 / 125000000) (81353269 / 200000000) (Real.log (769 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (769 / 512) = -Real.log (512 / 769) := by
    rw [show ((769 / 512) : ℝ) = ((512 / 769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697061079 / 1000000000) ≤ -Real.log (255 / 512) ∧
    -Real.log (255 / 512) ≤ (697061081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 511)) (n := 12)
    (lo := (3913899 / 1000000000)) (hi := (39139 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 255) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 255) = 1/(255 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-697061081 / 1000000000) (-697061079 / 1000000000) (Real.log (255 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61366309 / 200000000) ≤ -Real.log (125000 / 169889) ∧
    -Real.log (125000 / 169889) ≤ (153415773 / 500000000) := by
  have h := checkLog_sound (w := (44889 / 294889)) (n := 12)
    (lo := (61366309 / 200000000)) (hi := (153415773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169889 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169889 / 125000) = 1/(125000 / 169889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61366309 / 200000000) (153415773 / 500000000) (Real.log (169889 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169889 / 125000) = -Real.log (125000 / 169889) := by
    rw [show ((169889 / 125000) : ℝ) = ((125000 / 169889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111225141 / 250000000) ≤ -Real.log (80111 / 125000) ∧
    -Real.log (80111 / 125000) ≤ (88980113 / 200000000) := by
  have h := checkLog_sound (w := (44889 / 205111)) (n := 12)
    (lo := (111225141 / 250000000)) (hi := (88980113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80111) = 1/(80111 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-88980113 / 200000000) (-111225141 / 250000000) (Real.log (80111 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (307148613 / 1000000000) ≤ -Real.log (1000000 / 1359543) ∧
    -Real.log (1000000 / 1359543) ≤ (153574307 / 500000000) := by
  have h := checkLog_sound (w := (359543 / 2359543)) (n := 12)
    (lo := (307148613 / 1000000000)) (hi := (153574307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359543 / 1000000) = 1/(1000000 / 1359543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (307148613 / 1000000000) (153574307 / 500000000) (Real.log (1359543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1359543 / 1000000) = -Real.log (1000000 / 1359543) := by
    rw [show ((1359543 / 1000000) : ℝ) = ((1000000 / 1359543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (222786647 / 500000000) ≤ -Real.log (640457 / 1000000) ∧
    -Real.log (640457 / 1000000) ≤ (89114659 / 200000000) := by
  have h := checkLog_sound (w := (359543 / 1640457)) (n := 12)
    (lo := (222786647 / 500000000)) (hi := (89114659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640457) = 1/(640457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89114659 / 200000000) (-222786647 / 500000000) (Real.log (640457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116873567 / 500000000) ≤ -Real.log (40000 / 50533) ∧
    -Real.log (40000 / 50533) ≤ (46749427 / 200000000) := by
  have h := checkLog_sound (w := (10533 / 90533)) (n := 12)
    (lo := (116873567 / 500000000)) (hi := (46749427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50533 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50533 / 40000) = 1/(40000 / 50533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116873567 / 500000000) (46749427 / 200000000) (Real.log (50533 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50533 / 40000) = -Real.log (40000 / 50533) := by
    rw [show ((50533 / 40000) : ℝ) = ((40000 / 50533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15280423 / 50000000) ≤ -Real.log (29467 / 40000) ∧
    -Real.log (29467 / 40000) ≤ (305608461 / 1000000000) := by
  have h := checkLog_sound (w := (10533 / 69467)) (n := 12)
    (lo := (15280423 / 50000000)) (hi := (305608461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29467) = 1/(29467 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-305608461 / 1000000000) (-15280423 / 50000000) (Real.log (29467 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (58504057 / 250000000) ≤ -Real.log (200000 / 252733) ∧
    -Real.log (200000 / 252733) ≤ (234016229 / 1000000000) := by
  have h := checkLog_sound (w := (52733 / 452733)) (n := 12)
    (lo := (58504057 / 250000000)) (hi := (234016229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252733 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252733 / 200000) = 1/(200000 / 252733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (58504057 / 250000000) (234016229 / 1000000000) (Real.log (252733 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (252733 / 200000) = -Real.log (200000 / 252733) := by
    rw [show ((252733 / 200000) : ℝ) = ((200000 / 252733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3060701 / 10000000) ≤ -Real.log (147267 / 200000) ∧
    -Real.log (147267 / 200000) ≤ (306070101 / 1000000000) := by
  have h := checkLog_sound (w := (52733 / 347267)) (n := 12)
    (lo := (3060701 / 10000000)) (hi := (306070101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147267) = 1/(147267 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-306070101 / 1000000000) (-3060701 / 10000000) (Real.log (147267 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (751732109 / 1000000000) ≤ -Real.log (250000000000 / 530167517569) ∧
    -Real.log (250000000000 / 530167517569) ≤ (751732111 / 1000000000) := by
  have h := checkLog_sound (w := (30167517569 / 1030167517569)) (n := 12)
    (lo := (58584929 / 1000000000)) (hi := (5858493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((530167517569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(530167517569 / 500000000000) = 1/(250000000000 / 530167517569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (751732109 / 1000000000) (751732111 / 1000000000) (Real.log (530167517569 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (530167517569 / 250000000000) = -Real.log (250000000000 / 530167517569) := by
    rw [show ((530167517569 / 250000000000) : ℝ) = ((250000000000 / 530167517569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188180477 / 250000000) ≤ -Real.log (500000000000 / 1061385073471) ∧
    -Real.log (500000000000 / 1061385073471) ≤ (75272191 / 100000000) := by
  have h := checkLog_sound (w := (61385073471 / 2061385073471)) (n := 12)
    (lo := (7446841 / 125000000)) (hi := (59574729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061385073471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061385073471 / 1000000000000) = 1/(500000000000 / 1061385073471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188180477 / 250000000) (75272191 / 100000000) (Real.log (1061385073471 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1061385073471 / 500000000000) = -Real.log (500000000000 / 1061385073471) := by
    rw [show ((1061385073471 / 500000000000) : ℝ) = ((500000000000 / 1061385073471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (107871119 / 200000000) ≤ -Real.log (500000000000 / 857450707571) ∧
    -Real.log (500000000000 / 857450707571) ≤ (134838899 / 250000000) := by
  have h := checkLog_sound (w := (357450707571 / 1357450707571)) (n := 12)
    (lo := (107871119 / 200000000)) (hi := (134838899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857450707571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857450707571 / 500000000000) = 1/(500000000000 / 857450707571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (107871119 / 200000000) (134838899 / 250000000) (Real.log (857450707571 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (857450707571 / 500000000000) = -Real.log (500000000000 / 857450707571) := by
    rw [show ((857450707571 / 500000000000) : ℝ) = ((500000000000 / 857450707571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (540086329 / 1000000000) ≤ -Real.log (125000000000 / 214519376371) ∧
    -Real.log (125000000000 / 214519376371) ≤ (54008633 / 100000000) := by
  have h := checkLog_sound (w := (89519376371 / 339519376371)) (n := 12)
    (lo := (540086329 / 1000000000)) (hi := (54008633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214519376371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(214519376371 / 125000000000) = 1/(125000000000 / 214519376371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (540086329 / 1000000000) (54008633 / 100000000) (Real.log (214519376371 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (214519376371 / 125000000000) = -Real.log (125000000000 / 214519376371) := by
    rw [show ((214519376371 / 125000000000) : ℝ) = ((125000000000 / 214519376371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0299
