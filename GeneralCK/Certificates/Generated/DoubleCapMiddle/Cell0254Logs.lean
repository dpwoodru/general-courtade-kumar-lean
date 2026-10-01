import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0254
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

theorem reflection_log_1_neg : (241106251 / 1000000000) ≤ -Real.log (1280 / 1629) ∧
    -Real.log (1280 / 1629) ≤ (60276563 / 250000000) := by
  have h := checkLog_sound (w := (349 / 2909)) (n := 12)
    (lo := (241106251 / 1000000000)) (hi := (60276563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1629 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1629 / 1280) = 1/(1280 / 1629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (241106251 / 1000000000) (60276563 / 250000000) (Real.log (1629 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1629 / 1280) = -Real.log (1280 / 1629) := by
    rw [show ((1629 / 1280) : ℝ) = ((1280 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (318356079 / 1000000000) ≤ -Real.log (931 / 1280) ∧
    -Real.log (931 / 1280) ≤ (3979451 / 12500000) := by
  have h := checkLog_sound (w := (349 / 2211)) (n := 12)
    (lo := (318356079 / 1000000000)) (hi := (3979451 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 931) = 1/(931 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3979451 / 12500000) (-318356079 / 1000000000) (Real.log (931 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12032287 / 50000000) ≤ -Real.log (5120 / 6513) ∧
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


theorem reflection_log_3 : Bounds (12032287 / 50000000) (240645741 / 1000000000) (Real.log (6513 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6513 / 5120) = -Real.log (5120 / 6513) := by
    rw [show ((6513 / 5120) : ℝ) = ((5120 / 6513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (158775409 / 500000000) ≤ -Real.log (3727 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-317550819 / 1000000000) (-158775409 / 500000000) (Real.log (3727 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87045231 / 200000000) ≤ -Real.log (640 / 989) ∧
    -Real.log (640 / 989) ≤ (108806539 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1629)) (n := 12)
    (lo := (87045231 / 200000000)) (hi := (108806539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989 / 640) = 1/(640 / 989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87045231 / 200000000) (108806539 / 250000000) (Real.log (989 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (989 / 640) = -Real.log (640 / 989) := by
    rw [show ((989 / 640) : ℝ) = ((640 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197036227 / 250000000) ≤ -Real.log (291 / 640) ∧
    -Real.log (291 / 640) ≤ (78814491 / 100000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 291) = 1/(291 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78814491 / 100000000) (-197036227 / 250000000) (Real.log (291 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (17378701 / 40000000) ≤ -Real.log (2560 / 3953) ∧
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


theorem reflection_log_7 : Bounds (17378701 / 40000000) (217233763 / 500000000) (Real.log (3953 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3953 / 2560) = -Real.log (2560 / 3953) := by
    rw [show ((3953 / 2560) : ℝ) = ((2560 / 3953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (98196363 / 125000000) ≤ -Real.log (1167 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-392785453 / 500000000) (-98196363 / 125000000) (Real.log (1167 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164727407 / 500000000) ≤ -Real.log (100000 / 139021) ∧
    -Real.log (100000 / 139021) ≤ (65890963 / 200000000) := by
  have h := checkLog_sound (w := (39021 / 239021)) (n := 12)
    (lo := (164727407 / 500000000)) (hi := (65890963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139021 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139021 / 100000) = 1/(100000 / 139021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164727407 / 500000000) (65890963 / 200000000) (Real.log (139021 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (139021 / 100000) = -Real.log (100000 / 139021) := by
    rw [show ((139021 / 100000) : ℝ) = ((100000 / 139021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (494640643 / 1000000000) ≤ -Real.log (60979 / 100000) ∧
    -Real.log (60979 / 100000) ≤ (123660161 / 250000000) := by
  have h := checkLog_sound (w := (39021 / 160979)) (n := 12)
    (lo := (494640643 / 1000000000)) (hi := (123660161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 60979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 60979) = 1/(60979 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-123660161 / 250000000) (-494640643 / 1000000000) (Real.log (60979 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165039493 / 500000000) ≤ -Real.log (500000 / 695539) ∧
    -Real.log (500000 / 695539) ≤ (330078987 / 1000000000) := by
  have h := checkLog_sound (w := (195539 / 1195539)) (n := 12)
    (lo := (165039493 / 500000000)) (hi := (330078987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695539 / 500000) = 1/(500000 / 695539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165039493 / 500000000) (330078987 / 1000000000) (Real.log (695539 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (695539 / 500000) = -Real.log (500000 / 695539) := by
    rw [show ((695539 / 500000) : ℝ) = ((500000 / 695539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (248032549 / 500000000) ≤ -Real.log (304461 / 500000) ∧
    -Real.log (304461 / 500000) ≤ (496065099 / 1000000000) := by
  have h := checkLog_sound (w := (195539 / 804461)) (n := 12)
    (lo := (248032549 / 500000000)) (hi := (496065099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304461) = 1/(304461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-496065099 / 1000000000) (-248032549 / 500000000) (Real.log (304461 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (253127117 / 1000000000) ≤ -Real.log (1000000 / 1288047) ∧
    -Real.log (1000000 / 1288047) ≤ (126563559 / 500000000) := by
  have h := checkLog_sound (w := (288047 / 2288047)) (n := 12)
    (lo := (253127117 / 1000000000)) (hi := (126563559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288047 / 1000000) = 1/(1000000 / 1288047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (253127117 / 1000000000) (126563559 / 500000000) (Real.log (1288047 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1288047 / 1000000) = -Real.log (1000000 / 1288047) := by
    rw [show ((1288047 / 1000000) : ℝ) = ((1000000 / 1288047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16987169 / 50000000) ≤ -Real.log (711953 / 1000000) ∧
    -Real.log (711953 / 1000000) ≤ (339743381 / 1000000000) := by
  have h := checkLog_sound (w := (288047 / 1711953)) (n := 12)
    (lo := (16987169 / 50000000)) (hi := (339743381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711953) = 1/(711953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-339743381 / 1000000000) (-16987169 / 50000000) (Real.log (711953 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63417219 / 250000000) ≤ -Real.log (200000 / 257749) ∧
    -Real.log (200000 / 257749) ≤ (253668877 / 1000000000) := by
  have h := checkLog_sound (w := (57749 / 457749)) (n := 12)
    (lo := (63417219 / 250000000)) (hi := (253668877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257749 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257749 / 200000) = 1/(200000 / 257749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63417219 / 250000000) (253668877 / 1000000000) (Real.log (257749 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (257749 / 200000) = -Real.log (200000 / 257749) := by
    rw [show ((257749 / 200000) : ℝ) = ((200000 / 257749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (340724263 / 1000000000) ≤ -Real.log (142251 / 200000) ∧
    -Real.log (142251 / 200000) ≤ (42590533 / 125000000) := by
  have h := checkLog_sound (w := (57749 / 342251)) (n := 12)
    (lo := (340724263 / 1000000000)) (hi := (42590533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142251) = 1/(142251 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42590533 / 125000000) (-340724263 / 1000000000) (Real.log (142251 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (824095457 / 1000000000) ≤ -Real.log (500000000000 / 1139908821069) ∧
    -Real.log (500000000000 / 1139908821069) ≤ (824095459 / 1000000000) := by
  have h := checkLog_sound (w := (139908821069 / 2139908821069)) (n := 12)
    (lo := (130948277 / 1000000000)) (hi := (65474139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139908821069 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1139908821069 / 1000000000000) = 1/(500000000000 / 1139908821069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (824095457 / 1000000000) (824095459 / 1000000000) (Real.log (1139908821069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1139908821069 / 500000000000) = -Real.log (500000000000 / 1139908821069) := by
    rw [show ((1139908821069 / 500000000000) : ℝ) = ((500000000000 / 1139908821069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (826144083 / 1000000000) ≤ -Real.log (25000000000 / 57112323089) ∧
    -Real.log (25000000000 / 57112323089) ≤ (165228817 / 200000000) := by
  have h := checkLog_sound (w := (7112323089 / 107112323089)) (n := 12)
    (lo := (132996903 / 1000000000)) (hi := (16624613 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57112323089 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57112323089 / 50000000000) = 1/(25000000000 / 57112323089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (826144083 / 1000000000) (165228817 / 200000000) (Real.log (57112323089 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (57112323089 / 25000000000) = -Real.log (25000000000 / 57112323089) := by
    rw [show ((57112323089 / 25000000000) : ℝ) = ((25000000000 / 57112323089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (296435249 / 500000000) ≤ -Real.log (62500000000 / 113073387569) ∧
    -Real.log (62500000000 / 113073387569) ≤ (592870499 / 1000000000) := by
  have h := checkLog_sound (w := (50573387569 / 175573387569)) (n := 12)
    (lo := (296435249 / 500000000)) (hi := (592870499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113073387569 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113073387569 / 62500000000) = 1/(62500000000 / 113073387569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (296435249 / 500000000) (592870499 / 1000000000) (Real.log (113073387569 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (113073387569 / 62500000000) = -Real.log (62500000000 / 113073387569) := by
    rw [show ((113073387569 / 62500000000) : ℝ) = ((62500000000 / 113073387569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29719657 / 50000000) ≤ -Real.log (250000000000 / 452982755833) ∧
    -Real.log (250000000000 / 452982755833) ≤ (594393141 / 1000000000) := by
  have h := checkLog_sound (w := (202982755833 / 702982755833)) (n := 12)
    (lo := (29719657 / 50000000)) (hi := (594393141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452982755833 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452982755833 / 250000000000) = 1/(250000000000 / 452982755833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29719657 / 50000000) (594393141 / 1000000000) (Real.log (452982755833 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (452982755833 / 250000000000) = -Real.log (250000000000 / 452982755833) := by
    rw [show ((452982755833 / 250000000000) : ℝ) = ((250000000000 / 452982755833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0254
