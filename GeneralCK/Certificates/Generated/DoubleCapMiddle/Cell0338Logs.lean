import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0338
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

theorem reflection_log_1_neg : (214985363 / 1000000000) ≤ -Real.log (1280 / 1587) ∧
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


theorem reflection_log_1 : Bounds (214985363 / 1000000000) (53746341 / 250000000) (Real.log (1587 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1587 / 1280) = -Real.log (1280 / 1587) := by
    rw [show ((1587 / 1280) : ℝ) = ((1280 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137115637 / 500000000) ≤ -Real.log (973 / 1280) ∧
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


theorem reflection_log_2 : Bounds (-10969251 / 40000000) (-137115637 / 500000000) (Real.log (973 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2684363 / 12500000) ≤ -Real.log (10240 / 12693) ∧
    -Real.log (10240 / 12693) ≤ (214749041 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 22933)) (n := 12)
    (lo := (2684363 / 12500000)) (hi := (214749041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12693 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12693 / 10240) = 1/(10240 / 12693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2684363 / 12500000) (214749041 / 1000000000) (Real.log (12693 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12693 / 10240) = -Real.log (10240 / 12693) := by
    rw [show ((12693 / 10240) : ℝ) = ((10240 / 12693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (273845943 / 1000000000) ≤ -Real.log (7787 / 10240) ∧
    -Real.log (7787 / 10240) ≤ (34230743 / 125000000) := by
  have h := checkLog_sound (w := (2453 / 18027)) (n := 12)
    (lo := (273845943 / 1000000000)) (hi := (34230743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7787) = 1/(7787 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34230743 / 125000000) (-273845943 / 1000000000) (Real.log (7787 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97957729 / 250000000) ≤ -Real.log (640 / 947) ∧
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


theorem reflection_log_5 : Bounds (97957729 / 250000000) (391830917 / 1000000000) (Real.log (947 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (947 / 640) = -Real.log (640 / 947) := by
    rw [show ((947 / 640) : ℝ) = ((640 / 947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (326662843 / 500000000) ≤ -Real.log (333 / 640) ∧
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


theorem reflection_log_6 : Bounds (-653325687 / 1000000000) (-326662843 / 500000000) (Real.log (333 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (391434851 / 1000000000) ≤ -Real.log (5120 / 7573) ∧
    -Real.log (5120 / 7573) ≤ (97858713 / 250000000) := by
  have h := checkLog_sound (w := (2453 / 12693)) (n := 12)
    (lo := (391434851 / 1000000000)) (hi := (97858713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7573 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7573 / 5120) = 1/(5120 / 7573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (391434851 / 1000000000) (97858713 / 250000000) (Real.log (7573 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7573 / 5120) = -Real.log (5120 / 7573) := by
    rw [show ((7573 / 5120) : ℝ) = ((5120 / 7573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (652200193 / 1000000000) ≤ -Real.log (2667 / 5120) ∧
    -Real.log (2667 / 5120) ≤ (326100097 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 7787)) (n := 12)
    (lo := (652200193 / 1000000000)) (hi := (326100097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2667) = 1/(2667 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-326100097 / 500000000) (-652200193 / 1000000000) (Real.log (2667 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147217609 / 500000000) ≤ -Real.log (31250 / 41949) ∧
    -Real.log (31250 / 41949) ≤ (294435219 / 1000000000) := by
  have h := checkLog_sound (w := (10699 / 73199)) (n := 12)
    (lo := (147217609 / 500000000)) (hi := (294435219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41949 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41949 / 31250) = 1/(31250 / 41949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147217609 / 500000000) (294435219 / 1000000000) (Real.log (41949 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (41949 / 31250) = -Real.log (31250 / 41949) := by
    rw [show ((41949 / 31250) : ℝ) = ((31250 / 41949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209554887 / 500000000) ≤ -Real.log (20551 / 31250) ∧
    -Real.log (20551 / 31250) ≤ (16764391 / 40000000) := by
  have h := checkLog_sound (w := (10699 / 51801)) (n := 12)
    (lo := (209554887 / 500000000)) (hi := (16764391 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20551) = 1/(20551 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16764391 / 40000000) (-209554887 / 500000000) (Real.log (20551 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36844437 / 125000000) ≤ -Real.log (500000 / 671399) ∧
    -Real.log (500000 / 671399) ≤ (294755497 / 1000000000) := by
  have h := checkLog_sound (w := (171399 / 1171399)) (n := 12)
    (lo := (36844437 / 125000000)) (hi := (294755497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671399 / 500000) = 1/(500000 / 671399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36844437 / 125000000) (294755497 / 1000000000) (Real.log (671399 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (671399 / 500000) = -Real.log (500000 / 671399) := by
    rw [show ((671399 / 500000) : ℝ) = ((500000 / 671399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (419763849 / 1000000000) ≤ -Real.log (328601 / 500000) ∧
    -Real.log (328601 / 500000) ≤ (8395277 / 20000000) := by
  have h := checkLog_sound (w := (171399 / 828601)) (n := 12)
    (lo := (419763849 / 1000000000)) (hi := (8395277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328601) = 1/(328601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8395277 / 20000000) (-419763849 / 1000000000) (Real.log (328601 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (223309137 / 1000000000) ≤ -Real.log (1000000 / 1250207) ∧
    -Real.log (1000000 / 1250207) ≤ (111654569 / 500000000) := by
  have h := checkLog_sound (w := (250207 / 2250207)) (n := 12)
    (lo := (223309137 / 1000000000)) (hi := (111654569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250207 / 1000000) = 1/(1000000 / 1250207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (223309137 / 1000000000) (111654569 / 500000000) (Real.log (1250207 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1250207 / 1000000) = -Real.log (1000000 / 1250207) := by
    rw [show ((1250207 / 1000000) : ℝ) = ((1000000 / 1250207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (28795811 / 100000000) ≤ -Real.log (749793 / 1000000) ∧
    -Real.log (749793 / 1000000) ≤ (287958111 / 1000000000) := by
  have h := checkLog_sound (w := (250207 / 1749793)) (n := 12)
    (lo := (28795811 / 100000000)) (hi := (287958111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 749793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 749793) = 1/(749793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-287958111 / 1000000000) (-28795811 / 100000000) (Real.log (749793 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (223577057 / 1000000000) ≤ -Real.log (500000 / 625271) ∧
    -Real.log (500000 / 625271) ≤ (111788529 / 500000000) := by
  have h := checkLog_sound (w := (125271 / 1125271)) (n := 12)
    (lo := (223577057 / 1000000000)) (hi := (111788529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625271 / 500000) = 1/(500000 / 625271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (223577057 / 1000000000) (111788529 / 500000000) (Real.log (625271 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (625271 / 500000) = -Real.log (500000 / 625271) := by
    rw [show ((625271 / 500000) : ℝ) = ((500000 / 625271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57681 / 200000) ≤ -Real.log (374729 / 500000) ∧
    -Real.log (374729 / 500000) ≤ (288405001 / 1000000000) := by
  have h := checkLog_sound (w := (125271 / 874729)) (n := 12)
    (lo := (57681 / 200000)) (hi := (288405001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374729) = 1/(374729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-288405001 / 1000000000) (-57681 / 200000) (Real.log (374729 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (22298281 / 31250000) ≤ -Real.log (500000000000 / 1020607269719) ∧
    -Real.log (500000000000 / 1020607269719) ≤ (356772497 / 500000000) := by
  have h := checkLog_sound (w := (20607269719 / 2020607269719)) (n := 12)
    (lo := (5099453 / 250000000)) (hi := (20397813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1020607269719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1020607269719 / 1000000000000) = 1/(500000000000 / 1020607269719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (22298281 / 31250000) (356772497 / 500000000) (Real.log (1020607269719 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1020607269719 / 500000000000) = -Real.log (500000000000 / 1020607269719) := by
    rw [show ((1020607269719 / 500000000000) : ℝ) = ((500000000000 / 1020607269719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142903869 / 200000000) ≤ -Real.log (500000000000 / 1021602186239) ∧
    -Real.log (500000000000 / 1021602186239) ≤ (714519347 / 1000000000) := by
  have h := checkLog_sound (w := (21602186239 / 2021602186239)) (n := 12)
    (lo := (4274433 / 200000000)) (hi := (10686083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021602186239 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021602186239 / 1000000000000) = 1/(500000000000 / 1021602186239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142903869 / 200000000) (714519347 / 1000000000) (Real.log (1021602186239 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1021602186239 / 500000000000) = -Real.log (500000000000 / 1021602186239) := by
    rw [show ((1021602186239 / 500000000000) : ℝ) = ((500000000000 / 1021602186239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31954203 / 62500000) ≤ -Real.log (500000000000 / 833701434929) ∧
    -Real.log (500000000000 / 833701434929) ≤ (511267249 / 1000000000) := by
  have h := checkLog_sound (w := (333701434929 / 1333701434929)) (n := 12)
    (lo := (31954203 / 62500000)) (hi := (511267249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833701434929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833701434929 / 500000000000) = 1/(500000000000 / 833701434929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (31954203 / 62500000) (511267249 / 1000000000) (Real.log (833701434929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (833701434929 / 500000000000) = -Real.log (500000000000 / 833701434929) := by
    rw [show ((833701434929 / 500000000000) : ℝ) = ((500000000000 / 833701434929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (511982057 / 1000000000) ≤ -Real.log (250000000000 / 417148792861) ∧
    -Real.log (250000000000 / 417148792861) ≤ (255991029 / 500000000) := by
  have h := checkLog_sound (w := (167148792861 / 667148792861)) (n := 12)
    (lo := (511982057 / 1000000000)) (hi := (255991029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417148792861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417148792861 / 250000000000) = 1/(250000000000 / 417148792861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (511982057 / 1000000000) (255991029 / 500000000) (Real.log (417148792861 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (417148792861 / 250000000000) = -Real.log (250000000000 / 417148792861) := by
    rw [show ((417148792861 / 250000000000) : ℝ) = ((250000000000 / 417148792861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0338
