import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0213
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

theorem reflection_log_1_neg : (25980691 / 100000000) ≤ -Real.log (5120 / 6639) ∧
    -Real.log (5120 / 6639) ≤ (259806911 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 11759)) (n := 12)
    (lo := (25980691 / 100000000)) (hi := (259806911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6639 / 5120) = 1/(5120 / 6639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25980691 / 100000000) (259806911 / 1000000000) (Real.log (6639 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6639 / 5120) = -Real.log (5120 / 6639) := by
    rw [show ((6639 / 5120) : ℝ) = ((5120 / 6639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (175971427 / 500000000) ≤ -Real.log (3601 / 5120) ∧
    -Real.log (3601 / 5120) ≤ (70388571 / 200000000) := by
  have h := checkLog_sound (w := (1519 / 8721)) (n := 12)
    (lo := (175971427 / 500000000)) (hi := (70388571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3601) = 1/(3601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-70388571 / 200000000) (-175971427 / 500000000) (Real.log (3601 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (259354933 / 1000000000) ≤ -Real.log (1280 / 1659) ∧
    -Real.log (1280 / 1659) ≤ (129677467 / 500000000) := by
  have h := checkLog_sound (w := (379 / 2939)) (n := 12)
    (lo := (259354933 / 1000000000)) (hi := (129677467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1280) = 1/(1280 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (259354933 / 1000000000) (129677467 / 500000000) (Real.log (1659 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1659 / 1280) = -Real.log (1280 / 1659) := by
    rw [show ((1659 / 1280) : ℝ) = ((1280 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (351110099 / 1000000000) ≤ -Real.log (901 / 1280) ∧
    -Real.log (901 / 1280) ≤ (3511101 / 10000000) := by
  have h := checkLog_sound (w := (379 / 2181)) (n := 12)
    (lo := (351110099 / 1000000000)) (hi := (3511101 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 901) = 1/(901 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3511101 / 10000000) (-351110099 / 1000000000) (Real.log (901 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (465844601 / 1000000000) ≤ -Real.log (2560 / 4079) ∧
    -Real.log (2560 / 4079) ≤ (232922301 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 6639)) (n := 12)
    (lo := (465844601 / 1000000000)) (hi := (232922301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4079 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4079 / 2560) = 1/(2560 / 4079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (465844601 / 1000000000) (232922301 / 500000000) (Real.log (4079 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4079 / 2560) = -Real.log (2560 / 4079) := by
    rw [show ((4079 / 2560) : ℝ) = ((2560 / 4079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (224956367 / 250000000) ≤ -Real.log (1041 / 2560) ∧
    -Real.log (1041 / 2560) ≤ (89982547 / 100000000) := by
  have h := checkLog_sound (w := (239 / 2321)) (n := 12)
    (lo := (12917393 / 62500000)) (hi := (206678289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1041) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1041) = 1/(1041 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-89982547 / 100000000) (-224956367 / 250000000) (Real.log (1041 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (58138607 / 125000000) ≤ -Real.log (640 / 1019) ∧
    -Real.log (640 / 1019) ≤ (465108857 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1659)) (n := 12)
    (lo := (58138607 / 125000000)) (hi := (465108857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1019 / 640) = 1/(640 / 1019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (58138607 / 125000000) (465108857 / 1000000000) (Real.log (1019 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1019 / 640) = -Real.log (640 / 1019) := by
    rw [show ((1019 / 640) : ℝ) = ((640 / 1019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (112118471 / 125000000) ≤ -Real.log (261 / 640) ∧
    -Real.log (261 / 640) ≤ (89694777 / 100000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 261) = 1/(261 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-89694777 / 100000000) (-112118471 / 125000000) (Real.log (261 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177424739 / 500000000) ≤ -Real.log (500000 / 712983) ∧
    -Real.log (500000 / 712983) ≤ (354849479 / 1000000000) := by
  have h := checkLog_sound (w := (212983 / 1212983)) (n := 12)
    (lo := (177424739 / 500000000)) (hi := (354849479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712983 / 500000) = 1/(500000 / 712983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177424739 / 500000000) (354849479 / 1000000000) (Real.log (712983 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (712983 / 500000) = -Real.log (500000 / 712983) := by
    rw [show ((712983 / 500000) : ℝ) = ((500000 / 712983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11101333 / 20000000) ≤ -Real.log (287017 / 500000) ∧
    -Real.log (287017 / 500000) ≤ (555066651 / 1000000000) := by
  have h := checkLog_sound (w := (212983 / 787017)) (n := 12)
    (lo := (11101333 / 20000000)) (hi := (555066651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287017) = 1/(287017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-555066651 / 1000000000) (-11101333 / 20000000) (Real.log (287017 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (355465713 / 1000000000) ≤ -Real.log (200000 / 285369) ∧
    -Real.log (200000 / 285369) ≤ (177732857 / 500000000) := by
  have h := checkLog_sound (w := (85369 / 485369)) (n := 12)
    (lo := (355465713 / 1000000000)) (hi := (177732857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285369 / 200000) = 1/(200000 / 285369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (355465713 / 1000000000) (177732857 / 500000000) (Real.log (285369 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (285369 / 200000) = -Real.log (200000 / 285369) := by
    rw [show ((285369 / 200000) : ℝ) = ((200000 / 285369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (139149773 / 250000000) ≤ -Real.log (114631 / 200000) ∧
    -Real.log (114631 / 200000) ≤ (556599093 / 1000000000) := by
  have h := checkLog_sound (w := (85369 / 314631)) (n := 12)
    (lo := (139149773 / 250000000)) (hi := (556599093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 114631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 114631) = 1/(114631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-556599093 / 1000000000) (-139149773 / 250000000) (Real.log (114631 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68858467 / 250000000) ≤ -Real.log (500000 / 658551) ∧
    -Real.log (500000 / 658551) ≤ (275433869 / 1000000000) := by
  have h := checkLog_sound (w := (158551 / 1158551)) (n := 12)
    (lo := (68858467 / 250000000)) (hi := (275433869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658551 / 500000) = 1/(500000 / 658551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68858467 / 250000000) (275433869 / 1000000000) (Real.log (658551 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (658551 / 500000) = -Real.log (500000 / 658551) := by
    rw [show ((658551 / 500000) : ℝ) = ((500000 / 658551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (381409771 / 1000000000) ≤ -Real.log (341449 / 500000) ∧
    -Real.log (341449 / 500000) ≤ (95352443 / 250000000) := by
  have h := checkLog_sound (w := (158551 / 841449)) (n := 12)
    (lo := (381409771 / 1000000000)) (hi := (95352443 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341449) = 1/(341449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-95352443 / 250000000) (-381409771 / 1000000000) (Real.log (341449 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5519653 / 20000000) ≤ -Real.log (40000 / 52713) ∧
    -Real.log (40000 / 52713) ≤ (275982651 / 1000000000) := by
  have h := checkLog_sound (w := (12713 / 92713)) (n := 12)
    (lo := (5519653 / 20000000)) (hi := (275982651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52713 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52713 / 40000) = 1/(40000 / 52713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5519653 / 20000000) (275982651 / 1000000000) (Real.log (52713 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (52713 / 40000) = -Real.log (40000 / 52713) := by
    rw [show ((52713 / 40000) : ℝ) = ((40000 / 52713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76493811 / 200000000) ≤ -Real.log (27287 / 40000) ∧
    -Real.log (27287 / 40000) ≤ (5976079 / 15625000) := by
  have h := checkLog_sound (w := (12713 / 67287)) (n := 12)
    (lo := (76493811 / 200000000)) (hi := (5976079 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27287) = 1/(27287 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5976079 / 15625000) (-76493811 / 200000000) (Real.log (27287 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (909916129 / 1000000000) ≤ -Real.log (250000000000 / 621028545347) ∧
    -Real.log (250000000000 / 621028545347) ≤ (909916131 / 1000000000) := by
  have h := checkLog_sound (w := (121028545347 / 1121028545347)) (n := 12)
    (lo := (216768949 / 1000000000)) (hi := (4335379 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621028545347 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(621028545347 / 500000000000) = 1/(250000000000 / 621028545347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (909916129 / 1000000000) (909916131 / 1000000000) (Real.log (621028545347 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (621028545347 / 250000000000) = -Real.log (250000000000 / 621028545347) := by
    rw [show ((621028545347 / 250000000000) : ℝ) = ((250000000000 / 621028545347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182412961 / 200000000) ≤ -Real.log (5000000000 / 12447287383) ∧
    -Real.log (5000000000 / 12447287383) ≤ (912064807 / 1000000000) := by
  have h := checkLog_sound (w := (2447287383 / 22447287383)) (n := 12)
    (lo := (1751341 / 8000000)) (hi := (109458813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447287383 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12447287383 / 10000000000) = 1/(5000000000 / 12447287383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182412961 / 200000000) (912064807 / 1000000000) (Real.log (12447287383 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12447287383 / 5000000000) = -Real.log (5000000000 / 12447287383) := by
    rw [show ((12447287383 / 5000000000) : ℝ) = ((5000000000 / 12447287383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16421091 / 25000000) ≤ -Real.log (50000000000 / 96434753067) ∧
    -Real.log (50000000000 / 96434753067) ≤ (656843641 / 1000000000) := by
  have h := checkLog_sound (w := (46434753067 / 146434753067)) (n := 12)
    (lo := (16421091 / 25000000)) (hi := (656843641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96434753067 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96434753067 / 50000000000) = 1/(50000000000 / 96434753067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16421091 / 25000000) (656843641 / 1000000000) (Real.log (96434753067 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96434753067 / 50000000000) = -Real.log (50000000000 / 96434753067) := by
    rw [show ((96434753067 / 50000000000) : ℝ) = ((50000000000 / 96434753067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (329225853 / 500000000) ≤ -Real.log (500000000000 / 965899512589) ∧
    -Real.log (500000000000 / 965899512589) ≤ (658451707 / 1000000000) := by
  have h := checkLog_sound (w := (465899512589 / 1465899512589)) (n := 12)
    (lo := (329225853 / 500000000)) (hi := (658451707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965899512589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965899512589 / 500000000000) = 1/(500000000000 / 965899512589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (329225853 / 500000000) (658451707 / 1000000000) (Real.log (965899512589 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (965899512589 / 500000000000) = -Real.log (500000000000 / 965899512589) := by
    rw [show ((965899512589 / 500000000000) : ℝ) = ((500000000000 / 965899512589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0213
