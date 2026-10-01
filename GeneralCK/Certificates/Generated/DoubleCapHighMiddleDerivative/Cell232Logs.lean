import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell232
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (32679949 / 100000000) ≤ -Real.log (5120 / 7099) ∧
    -Real.log (5120 / 7099) ≤ (326799491 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 12219)) (n := 12)
    (lo := (32679949 / 100000000)) (hi := (326799491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7099 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7099 / 5120) = 1/(5120 / 7099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32679949 / 100000000) (326799491 / 1000000000) (Real.log (7099 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7099 / 5120) = -Real.log (5120 / 7099) := by
    rw [show ((7099 / 5120) : ℝ) = ((5120 / 7099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (244306609 / 500000000) ≤ -Real.log (3141 / 5120) ∧
    -Real.log (3141 / 5120) ≤ (488613219 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 8261)) (n := 12)
    (lo := (244306609 / 500000000)) (hi := (488613219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3141) = 1/(3141 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-488613219 / 1000000000) (-244306609 / 500000000) (Real.log (3141 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65275361 / 200000000) ≤ -Real.log (640 / 887) ∧
    -Real.log (640 / 887) ≤ (163188403 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1527)) (n := 12)
    (lo := (65275361 / 200000000)) (hi := (163188403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887 / 640) = 1/(640 / 887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65275361 / 200000000) (163188403 / 500000000) (Real.log (887 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (887 / 640) = -Real.log (640 / 887) := by
    rw [show ((887 / 640) : ℝ) = ((640 / 887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121914641 / 250000000) ≤ -Real.log (393 / 640) ∧
    -Real.log (393 / 640) ≤ (97531713 / 200000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 393) = 1/(393 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-97531713 / 200000000) (-121914641 / 250000000) (Real.log (393 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242715563 / 1000000000) ≤ -Real.log (500000 / 637353) ∧
    -Real.log (500000 / 637353) ≤ (60678891 / 250000000) := by
  have h := checkLog_sound (w := (137353 / 1137353)) (n := 12)
    (lo := (242715563 / 1000000000)) (hi := (60678891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637353 / 500000) = 1/(500000 / 637353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242715563 / 1000000000) (60678891 / 250000000) (Real.log (637353 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (637353 / 500000) = -Real.log (500000 / 637353) := by
    rw [show ((637353 / 500000) : ℝ) = ((500000 / 637353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (321178189 / 1000000000) ≤ -Real.log (362647 / 500000) ∧
    -Real.log (362647 / 500000) ≤ (32117819 / 100000000) := by
  have h := checkLog_sound (w := (137353 / 862647)) (n := 12)
    (lo := (321178189 / 1000000000)) (hi := (32117819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362647) = 1/(362647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32117819 / 100000000) (-321178189 / 1000000000) (Real.log (362647 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121524067 / 500000000) ≤ -Real.log (100000 / 127513) ∧
    -Real.log (100000 / 127513) ≤ (48609627 / 200000000) := by
  have h := checkLog_sound (w := (27513 / 227513)) (n := 12)
    (lo := (121524067 / 500000000)) (hi := (48609627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127513 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127513 / 100000) = 1/(100000 / 127513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121524067 / 500000000) (48609627 / 200000000) (Real.log (127513 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127513 / 100000) = -Real.log (100000 / 127513) := by
    rw [show ((127513 / 100000) : ℝ) = ((100000 / 127513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6435259 / 20000000) ≤ -Real.log (72487 / 100000) ∧
    -Real.log (72487 / 100000) ≤ (321762951 / 1000000000) := by
  have h := checkLog_sound (w := (27513 / 172487)) (n := 12)
    (lo := (6435259 / 20000000)) (hi := (321762951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72487) = 1/(72487 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-321762951 / 1000000000) (-6435259 / 20000000) (Real.log (72487 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45245373 / 250000000) ≤ -Real.log (1000000 / 1198393) ∧
    -Real.log (1000000 / 1198393) ≤ (180981493 / 1000000000) := by
  have h := checkLog_sound (w := (198393 / 2198393)) (n := 12)
    (lo := (45245373 / 250000000)) (hi := (180981493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198393 / 1000000) = 1/(1000000 / 1198393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45245373 / 250000000) (180981493 / 1000000000) (Real.log (1198393 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1198393 / 1000000) = -Real.log (1000000 / 1198393) := by
    rw [show ((1198393 / 1000000) : ℝ) = ((1000000 / 1198393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13821051 / 62500000) ≤ -Real.log (801607 / 1000000) ∧
    -Real.log (801607 / 1000000) ≤ (221136817 / 1000000000) := by
  have h := checkLog_sound (w := (198393 / 1801607)) (n := 12)
    (lo := (13821051 / 62500000)) (hi := (221136817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801607) = 1/(801607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-221136817 / 1000000000) (-13821051 / 62500000) (Real.log (801607 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (181247647 / 1000000000) ≤ -Real.log (125000 / 149839) ∧
    -Real.log (125000 / 149839) ≤ (5663989 / 31250000) := by
  have h := checkLog_sound (w := (24839 / 274839)) (n := 12)
    (lo := (181247647 / 1000000000)) (hi := (5663989 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149839 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149839 / 125000) = 1/(125000 / 149839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (181247647 / 1000000000) (5663989 / 31250000) (Real.log (149839 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (149839 / 125000) = -Real.log (125000 / 149839) := by
    rw [show ((149839 / 125000) : ℝ) = ((125000 / 149839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (44306969 / 200000000) ≤ -Real.log (100161 / 125000) ∧
    -Real.log (100161 / 125000) ≤ (110767423 / 500000000) := by
  have h := checkLog_sound (w := (24839 / 225161)) (n := 12)
    (lo := (44306969 / 200000000)) (hi := (110767423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100161) = 1/(100161 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-110767423 / 500000000) (-44306969 / 200000000) (Real.log (100161 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (814035369 / 1000000000) ≤ -Real.log (100000000000 / 225699745547) ∧
    -Real.log (100000000000 / 225699745547) ≤ (814035371 / 1000000000) := by
  have h := checkLog_sound (w := (25699745547 / 425699745547)) (n := 12)
    (lo := (120888189 / 1000000000)) (hi := (12088819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225699745547 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225699745547 / 200000000000) = 1/(100000000000 / 225699745547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (814035369 / 1000000000) (814035371 / 1000000000) (Real.log (225699745547 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (225699745547 / 100000000000) = -Real.log (100000000000 / 225699745547) := by
    rw [show ((225699745547 / 100000000000) : ℝ) = ((100000000000 / 225699745547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (815412707 / 1000000000) ≤ -Real.log (500000000000 / 1130054122891) ∧
    -Real.log (500000000000 / 1130054122891) ≤ (815412709 / 1000000000) := by
  have h := checkLog_sound (w := (130054122891 / 2130054122891)) (n := 12)
    (lo := (122265527 / 1000000000)) (hi := (15283191 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130054122891 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1130054122891 / 1000000000000) = 1/(500000000000 / 1130054122891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (815412707 / 1000000000) (815412709 / 1000000000) (Real.log (1130054122891 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1130054122891 / 500000000000) = -Real.log (500000000000 / 1130054122891) := by
    rw [show ((1130054122891 / 500000000000) : ℝ) = ((500000000000 / 1130054122891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (70486719 / 125000000) ≤ -Real.log (500000000000 / 878751237429) ∧
    -Real.log (500000000000 / 878751237429) ≤ (563893753 / 1000000000) := by
  have h := checkLog_sound (w := (378751237429 / 1378751237429)) (n := 12)
    (lo := (70486719 / 125000000)) (hi := (563893753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878751237429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878751237429 / 500000000000) = 1/(500000000000 / 878751237429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (70486719 / 125000000) (563893753 / 1000000000) (Real.log (878751237429 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (878751237429 / 500000000000) = -Real.log (500000000000 / 878751237429) := by
    rw [show ((878751237429 / 500000000000) : ℝ) = ((500000000000 / 878751237429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (141202771 / 250000000) ≤ -Real.log (500000000000 / 879557713797) ∧
    -Real.log (500000000000 / 879557713797) ≤ (112962217 / 200000000) := by
  have h := checkLog_sound (w := (379557713797 / 1379557713797)) (n := 12)
    (lo := (141202771 / 250000000)) (hi := (112962217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879557713797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879557713797 / 500000000000) = 1/(500000000000 / 879557713797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (141202771 / 250000000) (112962217 / 200000000) (Real.log (879557713797 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (879557713797 / 500000000000) = -Real.log (500000000000 / 879557713797) := by
    rw [show ((879557713797 / 500000000000) : ℝ) = ((500000000000 / 879557713797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100529577 / 250000000) ≤ -Real.log (250000000000 / 373747048117) ∧
    -Real.log (250000000000 / 373747048117) ≤ (402118309 / 1000000000) := by
  have h := checkLog_sound (w := (123747048117 / 623747048117)) (n := 12)
    (lo := (100529577 / 250000000)) (hi := (402118309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373747048117 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373747048117 / 250000000000) = 1/(250000000000 / 373747048117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100529577 / 250000000) (402118309 / 1000000000) (Real.log (373747048117 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (373747048117 / 250000000000) = -Real.log (250000000000 / 373747048117) := by
    rw [show ((373747048117 / 250000000000) : ℝ) = ((250000000000 / 373747048117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (402782493 / 1000000000) ≤ -Real.log (500000000000 / 747990734917) ∧
    -Real.log (500000000000 / 747990734917) ≤ (201391247 / 500000000) := by
  have h := checkLog_sound (w := (247990734917 / 1247990734917)) (n := 12)
    (lo := (402782493 / 1000000000)) (hi := (201391247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747990734917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747990734917 / 500000000000) = 1/(500000000000 / 747990734917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (402782493 / 1000000000) (201391247 / 500000000) (Real.log (747990734917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (747990734917 / 500000000000) = -Real.log (500000000000 / 747990734917) := by
    rw [show ((747990734917 / 500000000000) : ℝ) = ((500000000000 / 747990734917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20143599 / 500000000) ≤ -Real.log (15008024079 / 15625000000) ∧
    -Real.log (15008024079 / 15625000000) ≤ (40287199 / 1000000000) := by
  have h := checkLog_sound (w := (616975921 / 30633024079)) (n := 12)
    (lo := (20143599 / 500000000)) (hi := (40287199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15008024079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15008024079) = 1/(15008024079 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40287199 / 1000000000) (-20143599 / 500000000) (Real.log (15008024079 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40155323 / 1000000000) ≤ -Real.log (960640217551 / 1000000000000) ∧
    -Real.log (960640217551 / 1000000000000) ≤ (10038831 / 250000000) := by
  have h := checkLog_sound (w := (39359782449 / 1960640217551)) (n := 12)
    (lo := (40155323 / 1000000000)) (hi := (10038831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960640217551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960640217551) = 1/(960640217551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10038831 / 250000000) (-40155323 / 1000000000) (Real.log (960640217551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell232
