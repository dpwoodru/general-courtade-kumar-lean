import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0185
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

theorem reflection_log_1_neg : (68095011 / 250000000) ≤ -Real.log (5120 / 6723) ∧
    -Real.log (5120 / 6723) ≤ (54476009 / 200000000) := by
  have h := checkLog_sound (w := (1603 / 11843)) (n := 12)
    (lo := (68095011 / 250000000)) (hi := (54476009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6723 / 5120) = 1/(5120 / 6723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68095011 / 250000000) (54476009 / 200000000) (Real.log (6723 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6723 / 5120) = -Real.log (5120 / 6723) := by
    rw [show ((6723 / 5120) : ℝ) = ((5120 / 6723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75109217 / 200000000) ≤ -Real.log (3517 / 5120) ∧
    -Real.log (3517 / 5120) ≤ (187773043 / 500000000) := by
  have h := checkLog_sound (w := (1603 / 8637)) (n := 12)
    (lo := (75109217 / 200000000)) (hi := (187773043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3517) = 1/(3517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-187773043 / 500000000) (-75109217 / 200000000) (Real.log (3517 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54386743 / 200000000) ≤ -Real.log (16 / 21) ∧
    -Real.log (16 / 21) ≤ (67983429 / 250000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 16) = 1/(16 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (54386743 / 200000000) (67983429 / 250000000) (Real.log (21 / 16)) := by
  have h := reflection_log_3_neg
  have he : Real.log (21 / 16) = -Real.log (16 / 21) := by
    rw [show ((21 / 16) : ℝ) = ((16 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (374693449 / 1000000000) ≤ -Real.log (11 / 16) ∧
    -Real.log (11 / 16) ≤ (7493869 / 20000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 11) = 1/(11 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7493869 / 20000000) (-374693449 / 1000000000) (Real.log (11 / 16)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (486228709 / 1000000000) ≤ -Real.log (2560 / 4163) ∧
    -Real.log (2560 / 4163) ≤ (48622871 / 100000000) := by
  have h := checkLog_sound (w := (1603 / 6723)) (n := 12)
    (lo := (486228709 / 1000000000)) (hi := (48622871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4163 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4163 / 2560) = 1/(2560 / 4163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (486228709 / 1000000000) (48622871 / 100000000) (Real.log (4163 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4163 / 2560) = -Real.log (2560 / 4163) := by
    rw [show ((4163 / 2560) : ℝ) = ((2560 / 4163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (196791829 / 200000000) ≤ -Real.log (957 / 2560) ∧
    -Real.log (957 / 2560) ≤ (983959147 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 957) = 1/(957 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-983959147 / 1000000000) (-196791829 / 200000000) (Real.log (957 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97101563 / 200000000) ≤ -Real.log (8 / 13) ∧
    -Real.log (8 / 13) ≤ (60688477 / 125000000) := by
  have h := checkLog_sound (w := (5 / 21)) (n := 12)
    (lo := (97101563 / 200000000)) (hi := (60688477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 8) = 1/(8 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97101563 / 200000000) (60688477 / 125000000) (Real.log (13 / 8)) := by
  have h := reflection_log_7_neg
  have he : Real.log (13 / 8) = -Real.log (8 / 13) := by
    rw [show ((13 / 8) : ℝ) = ((8 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245207313 / 250000000) ≤ -Real.log (3 / 8) ∧
    -Real.log (3 / 8) ≤ (490414627 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4 / 3) = 1/(3 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-490414627 / 500000000) (-245207313 / 250000000) (Real.log (3 / 8)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (185999317 / 500000000) ≤ -Real.log (1000000 / 1450631) ∧
    -Real.log (1000000 / 1450631) ≤ (74399727 / 200000000) := by
  have h := checkLog_sound (w := (450631 / 2450631)) (n := 12)
    (lo := (185999317 / 500000000)) (hi := (74399727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1450631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1450631 / 1000000) = 1/(1000000 / 1450631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (185999317 / 500000000) (74399727 / 200000000) (Real.log (1450631 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1450631 / 1000000) = -Real.log (1000000 / 1450631) := by
    rw [show ((1450631 / 1000000) : ℝ) = ((1000000 / 1450631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149746233 / 250000000) ≤ -Real.log (549369 / 1000000) ∧
    -Real.log (549369 / 1000000) ≤ (598984933 / 1000000000) := by
  have h := checkLog_sound (w := (450631 / 1549369)) (n := 12)
    (lo := (149746233 / 250000000)) (hi := (598984933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 549369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 549369) = 1/(549369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-598984933 / 1000000000) (-149746233 / 250000000) (Real.log (549369 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5822019 / 15625000) ≤ -Real.log (1000000 / 1451517) ∧
    -Real.log (1000000 / 1451517) ≤ (372609217 / 1000000000) := by
  have h := checkLog_sound (w := (451517 / 2451517)) (n := 12)
    (lo := (5822019 / 15625000)) (hi := (372609217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451517 / 1000000) = 1/(1000000 / 1451517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5822019 / 15625000) (372609217 / 1000000000) (Real.log (1451517 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1451517 / 1000000) = -Real.log (1000000 / 1451517) := by
    rw [show ((1451517 / 1000000) : ℝ) = ((1000000 / 1451517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (600598993 / 1000000000) ≤ -Real.log (548483 / 1000000) ∧
    -Real.log (548483 / 1000000) ≤ (300299497 / 500000000) := by
  have h := checkLog_sound (w := (451517 / 1548483)) (n := 12)
    (lo := (600598993 / 1000000000)) (hi := (300299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 548483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 548483) = 1/(548483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-300299497 / 500000000) (-600598993 / 1000000000) (Real.log (548483 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9089321 / 31250000) ≤ -Real.log (40000 / 53503) ∧
    -Real.log (40000 / 53503) ≤ (290858273 / 1000000000) := by
  have h := checkLog_sound (w := (13503 / 93503)) (n := 12)
    (lo := (9089321 / 31250000)) (hi := (290858273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53503 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53503 / 40000) = 1/(40000 / 53503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9089321 / 31250000) (290858273 / 1000000000) (Real.log (53503 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53503 / 40000) = -Real.log (40000 / 53503) := by
    rw [show ((53503 / 40000) : ℝ) = ((40000 / 53503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (82369587 / 200000000) ≤ -Real.log (26497 / 40000) ∧
    -Real.log (26497 / 40000) ≤ (1608781 / 3906250) := by
  have h := checkLog_sound (w := (13503 / 66497)) (n := 12)
    (lo := (82369587 / 200000000)) (hi := (1608781 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26497) = 1/(26497 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1608781 / 3906250) (-82369587 / 200000000) (Real.log (26497 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (291413601 / 1000000000) ≤ -Real.log (500000 / 669159) ∧
    -Real.log (500000 / 669159) ≤ (145706801 / 500000000) := by
  have h := checkLog_sound (w := (169159 / 1169159)) (n := 12)
    (lo := (291413601 / 1000000000)) (hi := (145706801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669159 / 500000) = 1/(500000 / 669159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (291413601 / 1000000000) (145706801 / 500000000) (Real.log (669159 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (669159 / 500000) = -Real.log (500000 / 669159) := by
    rw [show ((669159 / 500000) : ℝ) = ((500000 / 669159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2064851 / 5000000) ≤ -Real.log (330841 / 500000) ∧
    -Real.log (330841 / 500000) ≤ (412970201 / 1000000000) := by
  have h := checkLog_sound (w := (169159 / 830841)) (n := 12)
    (lo := (2064851 / 5000000)) (hi := (412970201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330841) = 1/(330841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-412970201 / 1000000000) (-2064851 / 5000000) (Real.log (330841 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194196713 / 200000000) ≤ -Real.log (500000000000 / 1320270164497) ∧
    -Real.log (500000000000 / 1320270164497) ≤ (970983567 / 1000000000) := by
  have h := checkLog_sound (w := (320270164497 / 2320270164497)) (n := 12)
    (lo := (55567277 / 200000000)) (hi := (138918193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320270164497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1320270164497 / 1000000000000) = 1/(500000000000 / 1320270164497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194196713 / 200000000) (970983567 / 1000000000) (Real.log (1320270164497 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1320270164497 / 500000000000) = -Real.log (500000000000 / 1320270164497) := by
    rw [show ((1320270164497 / 500000000000) : ℝ) = ((500000000000 / 1320270164497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (973208209 / 1000000000) ≤ -Real.log (125000000000 / 330802641103) ∧
    -Real.log (125000000000 / 330802641103) ≤ (973208211 / 1000000000) := by
  have h := checkLog_sound (w := (80802641103 / 580802641103)) (n := 12)
    (lo := (280061029 / 1000000000)) (hi := (28006103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330802641103 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330802641103 / 250000000000) = 1/(125000000000 / 330802641103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (973208209 / 1000000000) (973208211 / 1000000000) (Real.log (330802641103 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330802641103 / 125000000000) = -Real.log (125000000000 / 330802641103) := by
    rw [show ((330802641103 / 125000000000) : ℝ) = ((125000000000 / 330802641103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (702706207 / 1000000000) ≤ -Real.log (500000000000 / 1009604860927) ∧
    -Real.log (500000000000 / 1009604860927) ≤ (702706209 / 1000000000) := by
  have h := checkLog_sound (w := (9604860927 / 2009604860927)) (n := 12)
    (lo := (9559027 / 1000000000)) (hi := (2389757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009604860927 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1009604860927 / 1000000000000) = 1/(500000000000 / 1009604860927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (702706207 / 1000000000) (702706209 / 1000000000) (Real.log (1009604860927 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1009604860927 / 500000000000) = -Real.log (500000000000 / 1009604860927) := by
    rw [show ((1009604860927 / 500000000000) : ℝ) = ((500000000000 / 1009604860927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (352191901 / 500000000) ≤ -Real.log (250000000000 / 505649995013) ∧
    -Real.log (250000000000 / 505649995013) ≤ (176095951 / 250000000) := by
  have h := checkLog_sound (w := (5649995013 / 1005649995013)) (n := 12)
    (lo := (5618311 / 500000000)) (hi := (11236623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505649995013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(505649995013 / 500000000000) = 1/(250000000000 / 505649995013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (352191901 / 500000000) (176095951 / 250000000) (Real.log (505649995013 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (505649995013 / 250000000000) = -Real.log (250000000000 / 505649995013) := by
    rw [show ((505649995013 / 250000000000) : ℝ) = ((250000000000 / 505649995013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0185
