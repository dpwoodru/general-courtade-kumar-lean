import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0070
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

theorem reflection_log_1_neg : (21158791 / 31250000) ≤ -Real.log (1600 / 3149) ∧
    -Real.log (1600 / 3149) ≤ (677081313 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4749)) (n := 12)
    (lo := (21158791 / 31250000)) (hi := (677081313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3149 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3149 / 1600) = 1/(1600 / 3149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21158791 / 31250000) (677081313 / 1000000000) (Real.log (3149 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3149 / 1600) = -Real.log (1600 / 3149) := by
    rw [show ((3149 / 1600) : ℝ) = ((1600 / 3149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3445933273 / 1000000000) ≤ -Real.log (51 / 1600) ∧
    -Real.log (51 / 1600) ≤ (1722966639 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 51) = 1/(51 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1722966639 / 500000000) (-3445933273 / 1000000000) (Real.log (51 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676892743 / 1000000000) ≤ -Real.log (51200 / 100749) ∧
    -Real.log (51200 / 100749) ≤ (84611593 / 125000000) := by
  have h := checkLog_sound (w := (49549 / 151949)) (n := 12)
    (lo := (676892743 / 1000000000)) (hi := (84611593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100749 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100749 / 51200) = 1/(51200 / 100749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676892743 / 1000000000) (84611593 / 125000000) (Real.log (100749 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100749 / 51200) = -Real.log (51200 / 100749) := by
    rw [show ((100749 / 51200) : ℝ) = ((51200 / 100749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (858589591 / 250000000) ≤ -Real.log (1651 / 51200) ∧
    -Real.log (1651 / 51200) ≤ (3434358369 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1651) = 1/(1651 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3434358369 / 1000000000) (-858589591 / 250000000) (Real.log (1651 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82594139 / 125000000) ≤ -Real.log (800 / 1549) ∧
    -Real.log (800 / 1549) ≤ (660753113 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2349)) (n := 12)
    (lo := (82594139 / 125000000)) (hi := (660753113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1549 / 800) = 1/(800 / 1549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82594139 / 125000000) (660753113 / 1000000000) (Real.log (1549 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1549 / 800) = -Real.log (800 / 1549) := by
    rw [show ((1549 / 800) : ℝ) = ((800 / 1549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2752786093 / 1000000000) ≤ -Real.log (51 / 800) ∧
    -Real.log (51 / 800) ≤ (2752786097 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 51) = 1/(51 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2752786097 / 1000000000) (-2752786093 / 1000000000) (Real.log (51 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (660369727 / 1000000000) ≤ -Real.log (25600 / 49549) ∧
    -Real.log (25600 / 49549) ≤ (10318277 / 15625000) := by
  have h := checkLog_sound (w := (23949 / 75149)) (n := 12)
    (lo := (660369727 / 1000000000)) (hi := (10318277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49549 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49549 / 25600) = 1/(25600 / 49549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (660369727 / 1000000000) (10318277 / 15625000) (Real.log (49549 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49549 / 25600) = -Real.log (25600 / 49549) := by
    rw [show ((49549 / 25600) : ℝ) = ((25600 / 49549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171325699 / 62500000) ≤ -Real.log (1651 / 25600) ∧
    -Real.log (1651 / 25600) ≤ (685302797 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1651) = 1/(1651 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-685302797 / 250000000) (-171325699 / 62500000) (Real.log (1651 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (339812331 / 500000000) ≤ -Real.log (1000000 / 1973137) ∧
    -Real.log (1000000 / 1973137) ≤ (679624663 / 1000000000) := by
  have h := checkLog_sound (w := (973137 / 2973137)) (n := 12)
    (lo := (339812331 / 500000000)) (hi := (679624663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973137 / 1000000) = 1/(1000000 / 1973137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (339812331 / 500000000) (679624663 / 1000000000) (Real.log (1973137 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1973137 / 1000000) = -Real.log (1000000 / 1973137) := by
    rw [show ((1973137 / 1000000) : ℝ) = ((1000000 / 1973137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3617005401 / 1000000000) ≤ -Real.log (26863 / 1000000) ∧
    -Real.log (26863 / 1000000) ≤ (3617005407 / 1000000000) := by
  have h := checkLog_sound (w := (4387 / 58113)) (n := 12)
    (lo := (151269501 / 1000000000)) (hi := (75634751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26863) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26863) = 1/(26863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3617005407 / 1000000000) (-3617005401 / 1000000000) (Real.log (26863 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169943413 / 250000000) ≤ -Real.log (1000000 / 1973431) ∧
    -Real.log (1000000 / 1973431) ≤ (679773653 / 1000000000) := by
  have h := checkLog_sound (w := (973431 / 2973431)) (n := 12)
    (lo := (169943413 / 250000000)) (hi := (679773653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973431 / 1000000) = 1/(1000000 / 1973431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169943413 / 250000000) (679773653 / 1000000000) (Real.log (1973431 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1973431 / 1000000) = -Real.log (1000000 / 1973431) := by
    rw [show ((1973431 / 1000000) : ℝ) = ((1000000 / 1973431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3628010153 / 1000000000) ≤ -Real.log (26569 / 1000000) ∧
    -Real.log (26569 / 1000000) ≤ (3628010159 / 1000000000) := by
  have h := checkLog_sound (w := (4681 / 57819)) (n := 12)
    (lo := (162274253 / 1000000000)) (hi := (81137127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26569) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26569) = 1/(26569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3628010159 / 1000000000) (-3628010153 / 1000000000) (Real.log (26569 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679533939 / 1000000000) ≤ -Real.log (500000 / 986479) ∧
    -Real.log (500000 / 986479) ≤ (33976697 / 50000000) := by
  have h := checkLog_sound (w := (486479 / 1486479)) (n := 12)
    (lo := (679533939 / 1000000000)) (hi := (33976697 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986479 / 500000) = 1/(500000 / 986479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679533939 / 1000000000) (33976697 / 50000000) (Real.log (986479 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986479 / 500000) = -Real.log (500000 / 986479) := by
    rw [show ((986479 / 500000) : ℝ) = ((500000 / 986479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3610364063 / 1000000000) ≤ -Real.log (13521 / 500000) ∧
    -Real.log (13521 / 500000) ≤ (3610364069 / 1000000000) := by
  have h := checkLog_sound (w := (1052 / 14573)) (n := 12)
    (lo := (144628163 / 1000000000)) (hi := (36157041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13521) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13521) = 1/(13521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3610364069 / 1000000000) (-3610364063 / 1000000000) (Real.log (13521 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679685983 / 1000000000) ≤ -Real.log (500000 / 986629) ∧
    -Real.log (500000 / 986629) ≤ (21240187 / 31250000) := by
  have h := checkLog_sound (w := (486629 / 1486629)) (n := 12)
    (lo := (679685983 / 1000000000)) (hi := (21240187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986629 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986629 / 500000) = 1/(500000 / 986629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679685983 / 1000000000) (21240187 / 31250000) (Real.log (986629 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (986629 / 500000) = -Real.log (500000 / 986629) := by
    rw [show ((986629 / 500000) : ℝ) = ((500000 / 986629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (452689989 / 125000000) ≤ -Real.log (13371 / 500000) ∧
    -Real.log (13371 / 500000) ≤ (1810759959 / 500000000) := by
  have h := checkLog_sound (w := (1127 / 14498)) (n := 12)
    (lo := (38946003 / 250000000)) (hi := (155784013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13371) = 1/(13371 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1810759959 / 500000000) (-452689989 / 125000000) (Real.log (13371 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2148315031 / 500000000) ≤ -Real.log (250000000000 / 18362962066783) ∧
    -Real.log (250000000000 / 18362962066783) ≤ (4296630069 / 1000000000) := by
  have h := checkLog_sound (w := (2362962066783 / 34362962066783)) (n := 12)
    (lo := (68873491 / 500000000)) (hi := (137746983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18362962066783 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18362962066783 / 16000000000000) = 1/(250000000000 / 18362962066783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2148315031 / 500000000) (4296630069 / 1000000000) (Real.log (18362962066783 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18362962066783 / 250000000000) = -Real.log (250000000000 / 18362962066783) := by
    rw [show ((18362962066783 / 250000000000) : ℝ) = ((250000000000 / 18362962066783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (861556761 / 200000000) ≤ -Real.log (500000000000 / 37137848620573) ∧
    -Real.log (500000000000 / 37137848620573) ≤ (1076945953 / 250000000) := by
  have h := checkLog_sound (w := (5137848620573 / 69137848620573)) (n := 12)
    (lo := (5956029 / 40000000)) (hi := (74450363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37137848620573 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37137848620573 / 32000000000000) = 1/(500000000000 / 37137848620573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (861556761 / 200000000) (1076945953 / 250000000) (Real.log (37137848620573 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37137848620573 / 500000000000) = -Real.log (500000000000 / 37137848620573) := by
    rw [show ((37137848620573 / 500000000000) : ℝ) = ((500000000000 / 37137848620573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2144949001 / 500000000) ≤ -Real.log (125000000000 / 9119878337401) ∧
    -Real.log (125000000000 / 9119878337401) ≤ (4289898009 / 1000000000) := by
  have h := checkLog_sound (w := (1119878337401 / 17119878337401)) (n := 12)
    (lo := (65507461 / 500000000)) (hi := (131014923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9119878337401 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9119878337401 / 8000000000000) = 1/(125000000000 / 9119878337401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2144949001 / 500000000) (4289898009 / 1000000000) (Real.log (9119878337401 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9119878337401 / 125000000000) = -Real.log (125000000000 / 9119878337401) := by
    rw [show ((9119878337401 / 125000000000) : ℝ) = ((125000000000 / 9119878337401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (537650737 / 125000000) ≤ -Real.log (125000000000 / 9223590232593) ∧
    -Real.log (125000000000 / 9223590232593) ≤ (4301205903 / 1000000000) := by
  have h := checkLog_sound (w := (1223590232593 / 17223590232593)) (n := 12)
    (lo := (1111897 / 7812500)) (hi := (142322817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9223590232593 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9223590232593 / 8000000000000) = 1/(125000000000 / 9223590232593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (537650737 / 125000000) (4301205903 / 1000000000) (Real.log (9223590232593 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9223590232593 / 125000000000) = -Real.log (125000000000 / 9223590232593) := by
    rw [show ((9223590232593 / 125000000000) : ℝ) = ((125000000000 / 9223590232593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0070
