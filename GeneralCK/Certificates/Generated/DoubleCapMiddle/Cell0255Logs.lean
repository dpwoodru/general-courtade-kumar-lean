import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0255
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

theorem reflection_log_1_neg : (12032287 / 50000000) ≤ -Real.log (5120 / 6513) ∧
    -Real.log (5120 / 6513) ≤ (240645741 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 11633)) (n := 12)
    (lo := (12032287 / 50000000)) (hi := (240645741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6513 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6513 / 5120) = 1/(5120 / 6513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12032287 / 50000000) (240645741 / 1000000000) (Real.log (6513 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6513 / 5120) = -Real.log (5120 / 6513) := by
    rw [show ((6513 / 5120) : ℝ) = ((5120 / 6513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (158775409 / 500000000) ≤ -Real.log (3727 / 5120) ∧
    -Real.log (3727 / 5120) ≤ (317550819 / 1000000000) := by
  have h := checkLog_sound (w := (1393 / 8847)) (n := 12)
    (lo := (158775409 / 500000000)) (hi := (317550819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3727) = 1/(3727 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-317550819 / 1000000000) (-158775409 / 500000000) (Real.log (3727 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (240185017 / 1000000000) ≤ -Real.log (512 / 651) ∧
    -Real.log (512 / 651) ≤ (120092509 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1163)) (n := 12)
    (lo := (240185017 / 1000000000)) (hi := (120092509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 512) = 1/(512 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (240185017 / 1000000000) (120092509 / 500000000) (Real.log (651 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (651 / 512) = -Real.log (512 / 651) := by
    rw [show ((651 / 512) : ℝ) = ((512 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (63349241 / 200000000) ≤ -Real.log (373 / 512) ∧
    -Real.log (373 / 512) ≤ (158373103 / 500000000) := by
  have h := checkLog_sound (w := (139 / 885)) (n := 12)
    (lo := (63349241 / 200000000)) (hi := (158373103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 373) = 1/(373 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158373103 / 500000000) (-63349241 / 200000000) (Real.log (373 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (17378701 / 40000000) ≤ -Real.log (2560 / 3953) ∧
    -Real.log (2560 / 3953) ≤ (217233763 / 500000000) := by
  have h := checkLog_sound (w := (1393 / 6513)) (n := 12)
    (lo := (17378701 / 40000000)) (hi := (217233763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3953 / 2560) = 1/(2560 / 3953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (17378701 / 40000000) (217233763 / 500000000) (Real.log (3953 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3953 / 2560) = -Real.log (2560 / 3953) := by
    rw [show ((3953 / 2560) : ℝ) = ((2560 / 3953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (98196363 / 125000000) ≤ -Real.log (1167 / 2560) ∧
    -Real.log (1167 / 2560) ≤ (392785453 / 500000000) := by
  have h := checkLog_sound (w := (113 / 2447)) (n := 12)
    (lo := (23105931 / 250000000)) (hi := (3696949 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1167) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1167) = 1/(1167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-392785453 / 500000000) (-98196363 / 125000000) (Real.log (1167 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2710677 / 6250000) ≤ -Real.log (256 / 395) ∧
    -Real.log (256 / 395) ≤ (433708321 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 651)) (n := 12)
    (lo := (2710677 / 6250000)) (hi := (433708321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395 / 256) = 1/(256 / 395) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2710677 / 6250000) (433708321 / 1000000000) (Real.log (395 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (395 / 256) = -Real.log (256 / 395) := by
    rw [show ((395 / 256) : ℝ) = ((256 / 395) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (783003509 / 1000000000) ≤ -Real.log (117 / 256) ∧
    -Real.log (117 / 256) ≤ (783003511 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 245)) (n := 12)
    (lo := (89856329 / 1000000000)) (hi := (8985633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 117) = 1/(117 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-783003511 / 1000000000) (-783003509 / 1000000000) (Real.log (117 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (328830253 / 1000000000) ≤ -Real.log (500000 / 694671) ∧
    -Real.log (500000 / 694671) ≤ (164415127 / 500000000) := by
  have h := checkLog_sound (w := (194671 / 1194671)) (n := 12)
    (lo := (328830253 / 1000000000)) (hi := (164415127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694671 / 500000) = 1/(500000 / 694671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (328830253 / 1000000000) (164415127 / 500000000) (Real.log (694671 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (694671 / 500000) = -Real.log (500000 / 694671) := by
    rw [show ((694671 / 500000) : ℝ) = ((500000 / 694671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (246609107 / 500000000) ≤ -Real.log (305329 / 500000) ∧
    -Real.log (305329 / 500000) ≤ (98643643 / 200000000) := by
  have h := checkLog_sound (w := (194671 / 805329)) (n := 12)
    (lo := (246609107 / 500000000)) (hi := (98643643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 305329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 305329) = 1/(305329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-98643643 / 200000000) (-246609107 / 500000000) (Real.log (305329 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164727767 / 500000000) ≤ -Real.log (1000000 / 1390211) ∧
    -Real.log (1000000 / 1390211) ≤ (65891107 / 200000000) := by
  have h := checkLog_sound (w := (390211 / 2390211)) (n := 12)
    (lo := (164727767 / 500000000)) (hi := (65891107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1390211 / 1000000) = 1/(1000000 / 1390211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164727767 / 500000000) (65891107 / 200000000) (Real.log (1390211 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1390211 / 1000000) = -Real.log (1000000 / 1390211) := by
    rw [show ((1390211 / 1000000) : ℝ) = ((1000000 / 1390211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (494642283 / 1000000000) ≤ -Real.log (609789 / 1000000) ∧
    -Real.log (609789 / 1000000) ≤ (123660571 / 250000000) := by
  have h := checkLog_sound (w := (390211 / 1609789)) (n := 12)
    (lo := (494642283 / 1000000000)) (hi := (123660571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 609789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 609789) = 1/(609789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-123660571 / 250000000) (-494642283 / 1000000000) (Real.log (609789 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (126293309 / 500000000) ≤ -Real.log (1000000 / 1287351) ∧
    -Real.log (1000000 / 1287351) ≤ (252586619 / 1000000000) := by
  have h := checkLog_sound (w := (287351 / 2287351)) (n := 12)
    (lo := (126293309 / 500000000)) (hi := (252586619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287351 / 1000000) = 1/(1000000 / 1287351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (126293309 / 500000000) (252586619 / 1000000000) (Real.log (1287351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1287351 / 1000000) = -Real.log (1000000 / 1287351) := by
    rw [show ((1287351 / 1000000) : ℝ) = ((1000000 / 1287351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67753253 / 200000000) ≤ -Real.log (712649 / 1000000) ∧
    -Real.log (712649 / 1000000) ≤ (169383133 / 500000000) := by
  have h := checkLog_sound (w := (287351 / 1712649)) (n := 12)
    (lo := (67753253 / 200000000)) (hi := (169383133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712649) = 1/(712649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-169383133 / 500000000) (-67753253 / 200000000) (Real.log (712649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (126563947 / 500000000) ≤ -Real.log (62500 / 80503) ∧
    -Real.log (62500 / 80503) ≤ (50625579 / 200000000) := by
  have h := checkLog_sound (w := (18003 / 143003)) (n := 12)
    (lo := (126563947 / 500000000)) (hi := (50625579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80503 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80503 / 62500) = 1/(62500 / 80503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (126563947 / 500000000) (50625579 / 200000000) (Real.log (80503 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80503 / 62500) = -Real.log (62500 / 80503) := by
    rw [show ((80503 / 62500) : ℝ) = ((62500 / 80503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (67948957 / 200000000) ≤ -Real.log (44497 / 62500) ∧
    -Real.log (44497 / 62500) ≤ (169872393 / 500000000) := by
  have h := checkLog_sound (w := (18003 / 106997)) (n := 12)
    (lo := (67948957 / 200000000)) (hi := (169872393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44497) = 1/(44497 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-169872393 / 500000000) (-67948957 / 200000000) (Real.log (44497 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (822048467 / 1000000000) ≤ -Real.log (250000000000 / 568788912943) ∧
    -Real.log (250000000000 / 568788912943) ≤ (822048469 / 1000000000) := by
  have h := checkLog_sound (w := (68788912943 / 1068788912943)) (n := 12)
    (lo := (128901287 / 1000000000)) (hi := (16112661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568788912943 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568788912943 / 500000000000) = 1/(250000000000 / 568788912943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (822048467 / 1000000000) (822048469 / 1000000000) (Real.log (568788912943 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (568788912943 / 250000000000) = -Real.log (250000000000 / 568788912943) := by
    rw [show ((568788912943 / 250000000000) : ℝ) = ((250000000000 / 568788912943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (103012227 / 125000000) ≤ -Real.log (4000000000 / 9119292083) ∧
    -Real.log (4000000000 / 9119292083) ≤ (412048909 / 500000000) := by
  have h := checkLog_sound (w := (1119292083 / 17119292083)) (n := 12)
    (lo := (32737659 / 250000000)) (hi := (130950637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9119292083 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9119292083 / 8000000000) = 1/(4000000000 / 9119292083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (103012227 / 125000000) (412048909 / 500000000) (Real.log (9119292083 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9119292083 / 4000000000) = -Real.log (4000000000 / 9119292083) := by
    rw [show ((9119292083 / 4000000000) : ℝ) = ((4000000000 / 9119292083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (147838221 / 250000000) ≤ -Real.log (500000000000 / 903215327601) ∧
    -Real.log (500000000000 / 903215327601) ≤ (118270577 / 200000000) := by
  have h := checkLog_sound (w := (403215327601 / 1403215327601)) (n := 12)
    (lo := (147838221 / 250000000)) (hi := (118270577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903215327601 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903215327601 / 500000000000) = 1/(500000000000 / 903215327601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (147838221 / 250000000) (118270577 / 200000000) (Real.log (903215327601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (903215327601 / 500000000000) = -Real.log (500000000000 / 903215327601) := by
    rw [show ((903215327601 / 500000000000) : ℝ) = ((500000000000 / 903215327601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (592872679 / 1000000000) ≤ -Real.log (500000000000 / 904589073421) ∧
    -Real.log (500000000000 / 904589073421) ≤ (14821817 / 25000000) := by
  have h := checkLog_sound (w := (404589073421 / 1404589073421)) (n := 12)
    (lo := (592872679 / 1000000000)) (hi := (14821817 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904589073421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904589073421 / 500000000000) = 1/(500000000000 / 904589073421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (592872679 / 1000000000) (14821817 / 25000000) (Real.log (904589073421 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (904589073421 / 500000000000) = -Real.log (500000000000 / 904589073421) := by
    rw [show ((904589073421 / 500000000000) : ℝ) = ((500000000000 / 904589073421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0255
