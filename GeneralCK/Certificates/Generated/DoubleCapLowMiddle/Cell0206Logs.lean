import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0206
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

theorem reflection_log_1_neg : (572214659 / 1000000000) ≤ -Real.log (3200 / 5671) ∧
    -Real.log (3200 / 5671) ≤ (28610733 / 50000000) := by
  have h := checkLog_sound (w := (2471 / 8871)) (n := 12)
    (lo := (572214659 / 1000000000)) (hi := (28610733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5671 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5671 / 3200) = 1/(3200 / 5671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (572214659 / 1000000000) (28610733 / 50000000) (Real.log (5671 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5671 / 3200) = -Real.log (3200 / 5671) := by
    rw [show ((5671 / 3200) : ℝ) = ((3200 / 5671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295846471 / 200000000) ≤ -Real.log (729 / 3200) ∧
    -Real.log (729 / 3200) ≤ (739616179 / 500000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 729) = 1/(729 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-739616179 / 500000000) (-295846471 / 200000000) (Real.log (729 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113771731 / 200000000) ≤ -Real.log (800 / 1413) ∧
    -Real.log (800 / 1413) ≤ (17776833 / 31250000) := by
  have h := checkLog_sound (w := (613 / 2213)) (n := 12)
    (lo := (113771731 / 200000000)) (hi := (17776833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 800) = 1/(800 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113771731 / 200000000) (17776833 / 31250000) (Real.log (1413 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1413 / 800) = -Real.log (800 / 1413) := by
    rw [show ((1413 / 800) : ℝ) = ((800 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1453503109 / 1000000000) ≤ -Real.log (187 / 800) ∧
    -Real.log (187 / 800) ≤ (181687889 / 125000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 187) = 1/(187 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-181687889 / 125000000) (-1453503109 / 1000000000) (Real.log (187 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (434619297 / 1000000000) ≤ -Real.log (1600 / 2471) ∧
    -Real.log (1600 / 2471) ≤ (217309649 / 500000000) := by
  have h := checkLog_sound (w := (871 / 4071)) (n := 12)
    (lo := (434619297 / 1000000000)) (hi := (217309649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 1600) = 1/(1600 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (434619297 / 1000000000) (217309649 / 500000000) (Real.log (2471 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2471 / 1600) = -Real.log (1600 / 2471) := by
    rw [show ((2471 / 1600) : ℝ) = ((1600 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31443407 / 40000000) ≤ -Real.log (729 / 1600) ∧
    -Real.log (729 / 1600) ≤ (786085177 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 1529)) (n := 12)
    (lo := (18587599 / 200000000)) (hi := (23234499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 729) = 1/(729 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-786085177 / 1000000000) (-31443407 / 40000000) (Real.log (729 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106725097 / 250000000) ≤ -Real.log (400 / 613) ∧
    -Real.log (400 / 613) ≤ (426900389 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1013)) (n := 12)
    (lo := (106725097 / 250000000)) (hi := (426900389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 400) = 1/(400 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106725097 / 250000000) (426900389 / 1000000000) (Real.log (613 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (613 / 400) = -Real.log (400 / 613) := by
    rw [show ((613 / 400) : ℝ) = ((400 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (760355929 / 1000000000) ≤ -Real.log (187 / 400) ∧
    -Real.log (187 / 400) ≤ (760355931 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 187) = 1/(187 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-760355931 / 1000000000) (-760355929 / 1000000000) (Real.log (187 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76600147 / 125000000) ≤ -Real.log (500000 / 922797) ∧
    -Real.log (500000 / 922797) ≤ (612801177 / 1000000000) := by
  have h := checkLog_sound (w := (422797 / 1422797)) (n := 12)
    (lo := (76600147 / 125000000)) (hi := (612801177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((922797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(922797 / 500000) = 1/(500000 / 922797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76600147 / 125000000) (612801177 / 1000000000) (Real.log (922797 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (922797 / 500000) = -Real.log (500000 / 922797) := by
    rw [show ((922797 / 500000) : ℝ) = ((500000 / 922797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (93408489 / 50000000) ≤ -Real.log (77203 / 500000) ∧
    -Real.log (77203 / 500000) ≤ (1868169783 / 1000000000) := by
  have h := checkLog_sound (w := (47797 / 202203)) (n := 12)
    (lo := (24093771 / 50000000)) (hi := (481875421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 77203) = 1/(77203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1868169783 / 1000000000) (-93408489 / 50000000) (Real.log (77203 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153588891 / 250000000) ≤ -Real.log (200000 / 369693) ∧
    -Real.log (200000 / 369693) ≤ (122871113 / 200000000) := by
  have h := checkLog_sound (w := (169693 / 569693)) (n := 12)
    (lo := (153588891 / 250000000)) (hi := (122871113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369693 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369693 / 200000) = 1/(200000 / 369693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153588891 / 250000000) (122871113 / 200000000) (Real.log (369693 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369693 / 200000) = -Real.log (200000 / 369693) := by
    rw [show ((369693 / 200000) : ℝ) = ((200000 / 369693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58966833 / 31250000) ≤ -Real.log (30307 / 200000) ∧
    -Real.log (30307 / 200000) ≤ (1886938659 / 1000000000) := by
  have h := checkLog_sound (w := (19693 / 80307)) (n := 12)
    (lo := (62580537 / 125000000)) (hi := (500644297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30307) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30307) = 1/(30307 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1886938659 / 1000000000) (-58966833 / 31250000) (Real.log (30307 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24120189 / 40000000) ≤ -Real.log (500000 / 913801) ∧
    -Real.log (500000 / 913801) ≤ (301502363 / 500000000) := by
  have h := checkLog_sound (w := (413801 / 1413801)) (n := 12)
    (lo := (24120189 / 40000000)) (hi := (301502363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913801 / 500000) = 1/(500000 / 913801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24120189 / 40000000) (301502363 / 500000000) (Real.log (913801 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (913801 / 500000) = -Real.log (500000 / 913801) := by
    rw [show ((913801 / 500000) : ℝ) = ((500000 / 913801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21974369 / 12500000) ≤ -Real.log (86199 / 500000) ∧
    -Real.log (86199 / 500000) ≤ (1757949523 / 1000000000) := by
  have h := checkLog_sound (w := (38801 / 211199)) (n := 12)
    (lo := (9291379 / 25000000)) (hi := (371655161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86199) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 86199) = 1/(86199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1757949523 / 1000000000) (-21974369 / 12500000) (Real.log (86199 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (302587307 / 500000000) ≤ -Real.log (250000 / 457893) ∧
    -Real.log (250000 / 457893) ≤ (121034923 / 200000000) := by
  have h := checkLog_sound (w := (207893 / 707893)) (n := 12)
    (lo := (302587307 / 500000000)) (hi := (121034923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457893 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457893 / 250000) = 1/(250000 / 457893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (302587307 / 500000000) (121034923 / 200000000) (Real.log (457893 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (457893 / 250000) = -Real.log (250000 / 457893) := by
    rw [show ((457893 / 250000) : ℝ) = ((250000 / 457893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1781246919 / 1000000000) ≤ -Real.log (42107 / 250000) ∧
    -Real.log (42107 / 250000) ≤ (890623461 / 500000000) := by
  have h := checkLog_sound (w := (20393 / 104607)) (n := 12)
    (lo := (394952559 / 1000000000)) (hi := (4936907 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42107) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 42107) = 1/(42107 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-890623461 / 500000000) (-1781246919 / 1000000000) (Real.log (42107 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2480970957 / 1000000000) ≤ -Real.log (250000000000 / 2988216131497) ∧
    -Real.log (250000000000 / 2988216131497) ≤ (2480970961 / 1000000000) := by
  have h := checkLog_sound (w := (988216131497 / 4988216131497)) (n := 12)
    (lo := (401529417 / 1000000000)) (hi := (200764709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2988216131497 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2988216131497 / 2000000000000) = 1/(250000000000 / 2988216131497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2480970957 / 1000000000) (2480970961 / 1000000000) (Real.log (2988216131497 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2988216131497 / 250000000000) = -Real.log (250000000000 / 2988216131497) := by
    rw [show ((2988216131497 / 250000000000) : ℝ) = ((250000000000 / 2988216131497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (125064711 / 50000000) ≤ -Real.log (15625000000 / 190597984789) ∧
    -Real.log (15625000000 / 190597984789) ≤ (156330889 / 62500000) := by
  have h := checkLog_sound (w := (65597984789 / 315597984789)) (n := 12)
    (lo := (10546317 / 25000000)) (hi := (421852681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190597984789 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(190597984789 / 125000000000) = 1/(15625000000 / 190597984789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (125064711 / 50000000) (156330889 / 62500000) (Real.log (190597984789 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190597984789 / 15625000000) = -Real.log (15625000000 / 190597984789) := by
    rw [show ((190597984789 / 15625000000) : ℝ) = ((15625000000 / 190597984789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (472190849 / 200000000) ≤ -Real.log (500000000000 / 5300531328669) ∧
    -Real.log (500000000000 / 5300531328669) ≤ (2360954249 / 1000000000) := by
  have h := checkLog_sound (w := (1300531328669 / 9300531328669)) (n := 12)
    (lo := (56302541 / 200000000)) (hi := (140756353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5300531328669 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5300531328669 / 4000000000000) = 1/(500000000000 / 5300531328669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (472190849 / 200000000) (2360954249 / 1000000000) (Real.log (5300531328669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5300531328669 / 500000000000) = -Real.log (500000000000 / 5300531328669) := by
    rw [show ((5300531328669 / 500000000000) : ℝ) = ((500000000000 / 5300531328669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2386421533 / 1000000000) ≤ -Real.log (125000000000 / 1359313772057) ∧
    -Real.log (125000000000 / 1359313772057) ≤ (2386421537 / 1000000000) := by
  have h := checkLog_sound (w := (359313772057 / 2359313772057)) (n := 12)
    (lo := (306979993 / 1000000000)) (hi := (153489997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359313772057 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1359313772057 / 1000000000000) = 1/(125000000000 / 1359313772057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2386421533 / 1000000000) (2386421537 / 1000000000) (Real.log (1359313772057 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1359313772057 / 125000000000) = -Real.log (125000000000 / 1359313772057) := by
    rw [show ((1359313772057 / 125000000000) : ℝ) = ((125000000000 / 1359313772057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0206
