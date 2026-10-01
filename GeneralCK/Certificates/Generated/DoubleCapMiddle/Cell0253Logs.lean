import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0253
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

theorem reflection_log_1_neg : (4831331 / 20000000) ≤ -Real.log (5120 / 6519) ∧
    -Real.log (5120 / 6519) ≤ (241566551 / 1000000000) := by
  have h := checkLog_sound (w := (1399 / 11639)) (n := 12)
    (lo := (4831331 / 20000000)) (hi := (241566551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6519 / 5120) = 1/(5120 / 6519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4831331 / 20000000) (241566551 / 1000000000) (Real.log (6519 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6519 / 5120) = -Real.log (5120 / 6519) := by
    rw [show ((6519 / 5120) : ℝ) = ((5120 / 6519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (319161989 / 1000000000) ≤ -Real.log (3721 / 5120) ∧
    -Real.log (3721 / 5120) ≤ (31916199 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 8841)) (n := 12)
    (lo := (319161989 / 1000000000)) (hi := (31916199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3721) = 1/(3721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-31916199 / 100000000) (-319161989 / 1000000000) (Real.log (3721 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (241106251 / 1000000000) ≤ -Real.log (1280 / 1629) ∧
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


theorem reflection_log_3 : Bounds (241106251 / 1000000000) (60276563 / 250000000) (Real.log (1629 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1629 / 1280) = -Real.log (1280 / 1629) := by
    rw [show ((1629 / 1280) : ℝ) = ((1280 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (318356079 / 1000000000) ≤ -Real.log (931 / 1280) ∧
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


theorem reflection_log_4 : Bounds (-3979451 / 12500000) (-318356079 / 1000000000) (Real.log (931 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (435984209 / 1000000000) ≤ -Real.log (2560 / 3959) ∧
    -Real.log (2560 / 3959) ≤ (43598421 / 100000000) := by
  have h := checkLog_sound (w := (1399 / 6519)) (n := 12)
    (lo := (435984209 / 1000000000)) (hi := (43598421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3959 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3959 / 2560) = 1/(2560 / 3959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (435984209 / 1000000000) (43598421 / 100000000) (Real.log (3959 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3959 / 2560) = -Real.log (2560 / 3959) := by
    rw [show ((3959 / 2560) : ℝ) = ((2560 / 3959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (158145111 / 200000000) ≤ -Real.log (1161 / 2560) ∧
    -Real.log (1161 / 2560) ≤ (790725557 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 2441)) (n := 12)
    (lo := (780627 / 8000000)) (hi := (12197297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1161) = 1/(1161 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-790725557 / 1000000000) (-158145111 / 200000000) (Real.log (1161 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (87045231 / 200000000) ≤ -Real.log (640 / 989) ∧
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


theorem reflection_log_7 : Bounds (87045231 / 200000000) (108806539 / 250000000) (Real.log (989 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (989 / 640) = -Real.log (640 / 989) := by
    rw [show ((989 / 640) : ℝ) = ((640 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (197036227 / 250000000) ≤ -Real.log (291 / 640) ∧
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


theorem reflection_log_8 : Bounds (-78814491 / 100000000) (-197036227 / 250000000) (Real.log (291 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330078267 / 1000000000) ≤ -Real.log (1000000 / 1391077) ∧
    -Real.log (1000000 / 1391077) ≤ (82519567 / 250000000) := by
  have h := checkLog_sound (w := (391077 / 2391077)) (n := 12)
    (lo := (330078267 / 1000000000)) (hi := (82519567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391077 / 1000000) = 1/(1000000 / 1391077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330078267 / 1000000000) (82519567 / 250000000) (Real.log (1391077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1391077 / 1000000) = -Real.log (1000000 / 1391077) := by
    rw [show ((1391077 / 1000000) : ℝ) = ((1000000 / 1391077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15501983 / 31250000) ≤ -Real.log (608923 / 1000000) ∧
    -Real.log (608923 / 1000000) ≤ (496063457 / 1000000000) := by
  have h := checkLog_sound (w := (391077 / 1608923)) (n := 12)
    (lo := (15501983 / 31250000)) (hi := (496063457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 608923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 608923) = 1/(608923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-496063457 / 1000000000) (-15501983 / 31250000) (Real.log (608923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20668923 / 62500000) ≤ -Real.log (500000 / 695973) ∧
    -Real.log (500000 / 695973) ≤ (330702769 / 1000000000) := by
  have h := checkLog_sound (w := (195973 / 1195973)) (n := 12)
    (lo := (20668923 / 62500000)) (hi := (330702769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695973 / 500000) = 1/(500000 / 695973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20668923 / 62500000) (330702769 / 1000000000) (Real.log (695973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (695973 / 500000) = -Real.log (500000 / 695973) := by
    rw [show ((695973 / 500000) : ℝ) = ((500000 / 695973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (99498317 / 200000000) ≤ -Real.log (304027 / 500000) ∧
    -Real.log (304027 / 500000) ≤ (248745793 / 500000000) := by
  have h := checkLog_sound (w := (195973 / 804027)) (n := 12)
    (lo := (99498317 / 200000000)) (hi := (248745793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304027) = 1/(304027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-248745793 / 500000000) (-99498317 / 200000000) (Real.log (304027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2536681 / 10000000) ≤ -Real.log (125000 / 161093) ∧
    -Real.log (125000 / 161093) ≤ (253668101 / 1000000000) := by
  have h := checkLog_sound (w := (36093 / 286093)) (n := 12)
    (lo := (2536681 / 10000000)) (hi := (253668101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161093 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161093 / 125000) = 1/(125000 / 161093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2536681 / 10000000) (253668101 / 1000000000) (Real.log (161093 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161093 / 125000) = -Real.log (125000 / 161093) := by
    rw [show ((161093 / 125000) : ℝ) = ((125000 / 161093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (340722857 / 1000000000) ≤ -Real.log (88907 / 125000) ∧
    -Real.log (88907 / 125000) ≤ (170361429 / 500000000) := by
  have h := checkLog_sound (w := (36093 / 213907)) (n := 12)
    (lo := (340722857 / 1000000000)) (hi := (170361429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88907) = 1/(88907 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-170361429 / 500000000) (-340722857 / 1000000000) (Real.log (88907 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (127104783 / 500000000) ≤ -Real.log (500000 / 644721) ∧
    -Real.log (500000 / 644721) ≤ (254209567 / 1000000000) := by
  have h := checkLog_sound (w := (144721 / 1144721)) (n := 12)
    (lo := (127104783 / 500000000)) (hi := (254209567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644721 / 500000) = 1/(500000 / 644721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (127104783 / 500000000) (254209567 / 1000000000) (Real.log (644721 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (644721 / 500000) = -Real.log (500000 / 644721) := by
    rw [show ((644721 / 500000) : ℝ) = ((500000 / 644721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170852351 / 500000000) ≤ -Real.log (355279 / 500000) ∧
    -Real.log (355279 / 500000) ≤ (341704703 / 1000000000) := by
  have h := checkLog_sound (w := (144721 / 855279)) (n := 12)
    (lo := (170852351 / 500000000)) (hi := (341704703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 355279) = 1/(355279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-341704703 / 1000000000) (-170852351 / 500000000) (Real.log (355279 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (413070861 / 500000000) ≤ -Real.log (50000000000 / 114224376481) ∧
    -Real.log (50000000000 / 114224376481) ≤ (206535431 / 250000000) := by
  have h := checkLog_sound (w := (14224376481 / 214224376481)) (n := 12)
    (lo := (66497271 / 500000000)) (hi := (132994543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114224376481 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114224376481 / 100000000000) = 1/(50000000000 / 114224376481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (413070861 / 500000000) (206535431 / 250000000) (Real.log (114224376481 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (114224376481 / 50000000000) = -Real.log (50000000000 / 114224376481) := by
    rw [show ((114224376481 / 50000000000) : ℝ) = ((50000000000 / 114224376481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51762147 / 62500000) ≤ -Real.log (250000000000 / 572295388239) ∧
    -Real.log (250000000000 / 572295388239) ≤ (414097177 / 500000000) := by
  have h := checkLog_sound (w := (72295388239 / 1072295388239)) (n := 12)
    (lo := (33761793 / 250000000)) (hi := (135047173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572295388239 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572295388239 / 500000000000) = 1/(250000000000 / 572295388239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51762147 / 62500000) (414097177 / 500000000) (Real.log (572295388239 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (572295388239 / 250000000000) = -Real.log (250000000000 / 572295388239) := by
    rw [show ((572295388239 / 250000000000) : ℝ) = ((250000000000 / 572295388239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (297195479 / 500000000) ≤ -Real.log (500000000000 / 905963534929) ∧
    -Real.log (500000000000 / 905963534929) ≤ (594390959 / 1000000000) := by
  have h := checkLog_sound (w := (405963534929 / 1405963534929)) (n := 12)
    (lo := (297195479 / 500000000)) (hi := (594390959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905963534929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905963534929 / 500000000000) = 1/(500000000000 / 905963534929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (297195479 / 500000000) (594390959 / 1000000000) (Real.log (905963534929 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (905963534929 / 500000000000) = -Real.log (500000000000 / 905963534929) := by
    rw [show ((905963534929 / 500000000000) : ℝ) = ((500000000000 / 905963534929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (148978567 / 250000000) ≤ -Real.log (500000000000 / 907344650261) ∧
    -Real.log (500000000000 / 907344650261) ≤ (595914269 / 1000000000) := by
  have h := checkLog_sound (w := (407344650261 / 1407344650261)) (n := 12)
    (lo := (148978567 / 250000000)) (hi := (595914269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((907344650261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(907344650261 / 500000000000) = 1/(500000000000 / 907344650261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (148978567 / 250000000) (595914269 / 1000000000) (Real.log (907344650261 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (907344650261 / 500000000000) = -Real.log (500000000000 / 907344650261) := by
    rw [show ((907344650261 / 500000000000) : ℝ) = ((500000000000 / 907344650261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0253
