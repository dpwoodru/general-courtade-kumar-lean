import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0222
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

theorem reflection_log_1_neg : (12786587 / 50000000) ≤ -Real.log (1280 / 1653) ∧
    -Real.log (1280 / 1653) ≤ (255731741 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2933)) (n := 12)
    (lo := (12786587 / 50000000)) (hi := (255731741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1280) = 1/(1280 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12786587 / 50000000) (255731741 / 1000000000) (Real.log (1653 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1653 / 1280) = -Real.log (1280 / 1653) := by
    rw [show ((1653 / 1280) : ℝ) = ((1280 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172236453 / 500000000) ≤ -Real.log (907 / 1280) ∧
    -Real.log (907 / 1280) ≤ (344472907 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2187)) (n := 12)
    (lo := (172236453 / 500000000)) (hi := (344472907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 907) = 1/(907 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-344472907 / 1000000000) (-172236453 / 500000000) (Real.log (907 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (255277917 / 1000000000) ≤ -Real.log (5120 / 6609) ∧
    -Real.log (5120 / 6609) ≤ (127638959 / 500000000) := by
  have h := checkLog_sound (w := (1489 / 11729)) (n := 12)
    (lo := (255277917 / 1000000000)) (hi := (127638959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6609 / 5120) = 1/(5120 / 6609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (255277917 / 1000000000) (127638959 / 500000000) (Real.log (6609 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6609 / 5120) = -Real.log (5120 / 6609) := by
    rw [show ((6609 / 5120) : ℝ) = ((5120 / 6609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (171823173 / 500000000) ≤ -Real.log (3631 / 5120) ∧
    -Real.log (3631 / 5120) ≤ (343646347 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 8751)) (n := 12)
    (lo := (171823173 / 500000000)) (hi := (343646347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3631) = 1/(3631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-343646347 / 1000000000) (-171823173 / 500000000) (Real.log (3631 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (459203327 / 1000000000) ≤ -Real.log (640 / 1013) ∧
    -Real.log (640 / 1013) ≤ (1793763 / 3906250) := by
  have h := checkLog_sound (w := (373 / 1653)) (n := 12)
    (lo := (459203327 / 1000000000)) (hi := (1793763 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 640) = 1/(640 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (459203327 / 1000000000) (1793763 / 3906250) (Real.log (1013 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1013 / 640) = -Real.log (640 / 1013) := by
    rw [show ((1013 / 640) : ℝ) = ((640 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (874219517 / 1000000000) ≤ -Real.log (267 / 640) ∧
    -Real.log (267 / 640) ≤ (874219519 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 267) = 1/(267 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-874219519 / 1000000000) (-874219517 / 1000000000) (Real.log (267 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229231339 / 500000000) ≤ -Real.log (2560 / 4049) ∧
    -Real.log (2560 / 4049) ≤ (458462679 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 6609)) (n := 12)
    (lo := (229231339 / 500000000)) (hi := (458462679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4049 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4049 / 2560) = 1/(2560 / 4049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229231339 / 500000000) (458462679 / 1000000000) (Real.log (4049 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4049 / 2560) = -Real.log (2560 / 4049) := by
    rw [show ((4049 / 2560) : ℝ) = ((2560 / 4049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (435707233 / 500000000) ≤ -Real.log (1071 / 2560) ∧
    -Real.log (1071 / 2560) ≤ (217853617 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2351)) (n := 12)
    (lo := (89133643 / 500000000)) (hi := (178267287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1071) = 1/(1071 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217853617 / 250000000) (-435707233 / 500000000) (Real.log (1071 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (349305959 / 1000000000) ≤ -Real.log (1000000 / 1418083) ∧
    -Real.log (1000000 / 1418083) ≤ (8732649 / 25000000) := by
  have h := checkLog_sound (w := (418083 / 2418083)) (n := 12)
    (lo := (349305959 / 1000000000)) (hi := (8732649 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1418083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1418083 / 1000000) = 1/(1000000 / 1418083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (349305959 / 1000000000) (8732649 / 25000000) (Real.log (1418083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1418083 / 1000000) = -Real.log (1000000 / 1418083) := by
    rw [show ((1418083 / 1000000) : ℝ) = ((1000000 / 1418083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (541427453 / 1000000000) ≤ -Real.log (581917 / 1000000) ∧
    -Real.log (581917 / 1000000) ≤ (270713727 / 500000000) := by
  have h := checkLog_sound (w := (418083 / 1581917)) (n := 12)
    (lo := (541427453 / 1000000000)) (hi := (270713727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 581917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 581917) = 1/(581917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-270713727 / 500000000) (-541427453 / 1000000000) (Real.log (581917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21870219 / 62500000) ≤ -Real.log (1000000 / 1418959) ∧
    -Real.log (1000000 / 1418959) ≤ (69984701 / 200000000) := by
  have h := checkLog_sound (w := (418959 / 2418959)) (n := 12)
    (lo := (21870219 / 62500000)) (hi := (69984701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1418959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1418959 / 1000000) = 1/(1000000 / 1418959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21870219 / 62500000) (69984701 / 200000000) (Real.log (1418959 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1418959 / 1000000) = -Real.log (1000000 / 1418959) := by
    rw [show ((1418959 / 1000000) : ℝ) = ((1000000 / 1418959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (135733489 / 250000000) ≤ -Real.log (581041 / 1000000) ∧
    -Real.log (581041 / 1000000) ≤ (542933957 / 1000000000) := by
  have h := checkLog_sound (w := (418959 / 1581041)) (n := 12)
    (lo := (135733489 / 250000000)) (hi := (542933957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 581041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 581041) = 1/(581041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-542933957 / 1000000000) (-135733489 / 250000000) (Real.log (581041 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (270510989 / 1000000000) ≤ -Real.log (500000 / 655317) ∧
    -Real.log (500000 / 655317) ≤ (27051099 / 100000000) := by
  have h := checkLog_sound (w := (155317 / 1155317)) (n := 12)
    (lo := (270510989 / 1000000000)) (hi := (27051099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655317 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655317 / 500000) = 1/(500000 / 655317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (270510989 / 1000000000) (27051099 / 100000000) (Real.log (655317 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (655317 / 500000) = -Real.log (500000 / 655317) := by
    rw [show ((655317 / 500000) : ℝ) = ((500000 / 655317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11624467 / 31250000) ≤ -Real.log (344683 / 500000) ∧
    -Real.log (344683 / 500000) ≤ (74396589 / 200000000) := by
  have h := checkLog_sound (w := (155317 / 844683)) (n := 12)
    (lo := (11624467 / 31250000)) (hi := (74396589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344683) = 1/(344683 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-74396589 / 200000000) (-11624467 / 31250000) (Real.log (344683 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (271057903 / 1000000000) ≤ -Real.log (1000000 / 1311351) ∧
    -Real.log (1000000 / 1311351) ≤ (16941119 / 62500000) := by
  have h := checkLog_sound (w := (311351 / 2311351)) (n := 12)
    (lo := (271057903 / 1000000000)) (hi := (16941119 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311351 / 1000000) = 1/(1000000 / 1311351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (271057903 / 1000000000) (16941119 / 62500000) (Real.log (1311351 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1311351 / 1000000) = -Real.log (1000000 / 1311351) := by
    rw [show ((1311351 / 1000000) : ℝ) = ((1000000 / 1311351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (373023571 / 1000000000) ≤ -Real.log (688649 / 1000000) ∧
    -Real.log (688649 / 1000000) ≤ (93255893 / 250000000) := by
  have h := checkLog_sound (w := (311351 / 1688649)) (n := 12)
    (lo := (373023571 / 1000000000)) (hi := (93255893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688649) = 1/(688649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-93255893 / 250000000) (-373023571 / 1000000000) (Real.log (688649 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (222683353 / 250000000) ≤ -Real.log (250000000000 / 609229065313) ∧
    -Real.log (250000000000 / 609229065313) ≤ (445366707 / 500000000) := by
  have h := checkLog_sound (w := (109229065313 / 1109229065313)) (n := 12)
    (lo := (24698279 / 125000000)) (hi := (197586233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609229065313 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(609229065313 / 500000000000) = 1/(250000000000 / 609229065313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (222683353 / 250000000) (445366707 / 500000000) (Real.log (609229065313 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (609229065313 / 250000000000) = -Real.log (250000000000 / 609229065313) := by
    rw [show ((609229065313 / 250000000000) : ℝ) = ((250000000000 / 609229065313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (44642873 / 50000000) ≤ -Real.log (500000000000 / 1221048944911) ∧
    -Real.log (500000000000 / 1221048944911) ≤ (446428731 / 500000000) := by
  have h := checkLog_sound (w := (221048944911 / 2221048944911)) (n := 12)
    (lo := (4992757 / 25000000)) (hi := (199710281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221048944911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1221048944911 / 1000000000000) = 1/(500000000000 / 1221048944911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (44642873 / 50000000) (446428731 / 500000000) (Real.log (1221048944911 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1221048944911 / 500000000000) = -Real.log (500000000000 / 1221048944911) := by
    rw [show ((1221048944911 / 500000000000) : ℝ) = ((500000000000 / 1221048944911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (642493933 / 1000000000) ≤ -Real.log (100000000000 / 190121648007) ∧
    -Real.log (100000000000 / 190121648007) ≤ (321246967 / 500000000) := by
  have h := checkLog_sound (w := (90121648007 / 290121648007)) (n := 12)
    (lo := (642493933 / 1000000000)) (hi := (321246967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190121648007 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190121648007 / 100000000000) = 1/(100000000000 / 190121648007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (642493933 / 1000000000) (321246967 / 500000000) (Real.log (190121648007 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (190121648007 / 100000000000) = -Real.log (100000000000 / 190121648007) := by
    rw [show ((190121648007 / 100000000000) : ℝ) = ((100000000000 / 190121648007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25763259 / 40000000) ≤ -Real.log (250000000000 / 476059284193) ∧
    -Real.log (250000000000 / 476059284193) ≤ (161020369 / 250000000) := by
  have h := checkLog_sound (w := (226059284193 / 726059284193)) (n := 12)
    (lo := (25763259 / 40000000)) (hi := (161020369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476059284193 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476059284193 / 250000000000) = 1/(250000000000 / 476059284193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25763259 / 40000000) (161020369 / 250000000) (Real.log (476059284193 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (476059284193 / 250000000000) = -Real.log (250000000000 / 476059284193) := by
    rw [show ((476059284193 / 250000000000) : ℝ) = ((250000000000 / 476059284193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0222
