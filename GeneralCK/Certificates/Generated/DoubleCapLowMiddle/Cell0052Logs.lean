import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052
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

theorem reflection_log_1_neg : (678870953 / 1000000000) ≤ -Real.log (102400 / 201897) ∧
    -Real.log (102400 / 201897) ≤ (339435477 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 304297)) (n := 12)
    (lo := (678870953 / 1000000000)) (hi := (339435477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201897 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201897 / 102400) = 1/(102400 / 201897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678870953 / 1000000000) (339435477 / 500000000) (Real.log (201897 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201897 / 102400) = -Real.log (102400 / 201897) := by
    rw [show ((201897 / 102400) : ℝ) = ((102400 / 201897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445392753 / 125000000) ≤ -Real.log (2903 / 102400) ∧
    -Real.log (2903 / 102400) ≤ (356314203 / 100000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2903) = 1/(2903 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-356314203 / 100000000) (-445392753 / 125000000) (Real.log (2903 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678776841 / 1000000000) ≤ -Real.log (51200 / 100939) ∧
    -Real.log (51200 / 100939) ≤ (339388421 / 500000000) := by
  have h := checkLog_sound (w := (49739 / 152139)) (n := 12)
    (lo := (678776841 / 1000000000)) (hi := (339388421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100939 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100939 / 51200) = 1/(51200 / 100939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678776841 / 1000000000) (339388421 / 500000000) (Real.log (100939 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100939 / 51200) = -Real.log (51200 / 100939) := by
    rw [show ((100939 / 51200) : ℝ) = ((51200 / 100939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (889154599 / 250000000) ≤ -Real.log (1461 / 51200) ∧
    -Real.log (1461 / 51200) ≤ (1778309201 / 500000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1461) = 1/(1461 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1778309201 / 500000000) (-889154599 / 250000000) (Real.log (1461 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16609699 / 25000000) ≤ -Real.log (51200 / 99497) ∧
    -Real.log (51200 / 99497) ≤ (664387961 / 1000000000) := by
  have h := checkLog_sound (w := (48297 / 150697)) (n := 12)
    (lo := (16609699 / 25000000)) (hi := (664387961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99497 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99497 / 51200) = 1/(51200 / 99497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16609699 / 25000000) (664387961 / 1000000000) (Real.log (99497 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99497 / 51200) = -Real.log (51200 / 99497) := by
    rw [show ((99497 / 51200) : ℝ) = ((51200 / 99497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (717498711 / 250000000) ≤ -Real.log (2903 / 51200) ∧
    -Real.log (2903 / 51200) ≤ (2869994849 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2903) = 1/(2903 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2869994849 / 1000000000) (-717498711 / 250000000) (Real.log (2903 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332098491 / 500000000) ≤ -Real.log (25600 / 49739) ∧
    -Real.log (25600 / 49739) ≤ (664196983 / 1000000000) := by
  have h := checkLog_sound (w := (24139 / 75339)) (n := 12)
    (lo := (332098491 / 500000000)) (hi := (664196983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49739 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49739 / 25600) = 1/(25600 / 49739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (332098491 / 500000000) (664196983 / 1000000000) (Real.log (49739 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49739 / 25600) = -Real.log (25600 / 49739) := by
    rw [show ((49739 / 25600) : ℝ) = ((25600 / 49739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (178966951 / 62500000) ≤ -Real.log (1461 / 25600) ∧
    -Real.log (1461 / 25600) ≤ (2863471221 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 3061)) (n := 12)
    (lo := (1420039 / 15625000)) (hi := (90882497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1461) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1461) = 1/(1461 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2863471221 / 1000000000) (-178966951 / 62500000) (Real.log (1461 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170279783 / 250000000) ≤ -Real.log (125000 / 247011) ∧
    -Real.log (125000 / 247011) ≤ (681119133 / 1000000000) := by
  have h := checkLog_sound (w := (122011 / 372011)) (n := 12)
    (lo := (170279783 / 250000000)) (hi := (681119133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247011 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247011 / 125000) = 1/(125000 / 247011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170279783 / 250000000) (681119133 / 1000000000) (Real.log (247011 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247011 / 125000) = -Real.log (125000 / 247011) := by
    rw [show ((247011 / 125000) : ℝ) = ((125000 / 247011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3733374851 / 1000000000) ≤ -Real.log (2989 / 125000) ∧
    -Real.log (2989 / 125000) ≤ (3733374857 / 1000000000) := by
  have h := checkLog_sound (w := (3669 / 27581)) (n := 12)
    (lo := (267638951 / 1000000000)) (hi := (33454869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11956) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11956) = 1/(2989 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3733374857 / 1000000000) (-3733374851 / 1000000000) (Real.log (2989 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681194531 / 1000000000) ≤ -Real.log (1000000 / 1976237) ∧
    -Real.log (1000000 / 1976237) ≤ (170298633 / 250000000) := by
  have h := checkLog_sound (w := (976237 / 2976237)) (n := 12)
    (lo := (681194531 / 1000000000)) (hi := (170298633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976237 / 1000000) = 1/(1000000 / 1976237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681194531 / 1000000000) (170298633 / 250000000) (Real.log (1976237 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976237 / 1000000) = -Real.log (1000000 / 1976237) := by
    rw [show ((1976237 / 1000000) : ℝ) = ((1000000 / 1976237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3739625527 / 1000000000) ≤ -Real.log (23763 / 1000000) ∧
    -Real.log (23763 / 1000000) ≤ (3739625533 / 1000000000) := by
  have h := checkLog_sound (w := (7487 / 55013)) (n := 12)
    (lo := (273889627 / 1000000000)) (hi := (68472407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23763) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23763) = 1/(23763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3739625533 / 1000000000) (-3739625527 / 1000000000) (Real.log (23763 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681050307 / 1000000000) ≤ -Real.log (62500 / 123497) ∧
    -Real.log (62500 / 123497) ≤ (170262577 / 250000000) := by
  have h := checkLog_sound (w := (60997 / 185997)) (n := 12)
    (lo := (681050307 / 1000000000)) (hi := (170262577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123497 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123497 / 62500) = 1/(62500 / 123497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681050307 / 1000000000) (170262577 / 250000000) (Real.log (123497 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123497 / 62500) = -Real.log (62500 / 123497) := by
    rw [show ((123497 / 62500) : ℝ) = ((62500 / 123497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3727703443 / 1000000000) ≤ -Real.log (1503 / 62500) ∧
    -Real.log (1503 / 62500) ≤ (3727703449 / 1000000000) := by
  have h := checkLog_sound (w := (3601 / 27649)) (n := 12)
    (lo := (261967543 / 1000000000)) (hi := (32745943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12024) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12024) = 1/(1503 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3727703449 / 1000000000) (-3727703443 / 1000000000) (Real.log (1503 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681127229 / 1000000000) ≤ -Real.log (125000 / 247013) ∧
    -Real.log (125000 / 247013) ≤ (68112723 / 100000000) := by
  have h := checkLog_sound (w := (122013 / 372013)) (n := 12)
    (lo := (681127229 / 1000000000)) (hi := (68112723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247013 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247013 / 125000) = 1/(125000 / 247013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681127229 / 1000000000) (68112723 / 100000000) (Real.log (247013 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247013 / 125000) = -Real.log (125000 / 247013) := by
    rw [show ((247013 / 125000) : ℝ) = ((125000 / 247013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (746808839 / 200000000) ≤ -Real.log (2987 / 125000) ∧
    -Real.log (2987 / 125000) ≤ (3734044201 / 1000000000) := by
  have h := checkLog_sound (w := (3677 / 27573)) (n := 12)
    (lo := (53661659 / 200000000)) (hi := (33538537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11948) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11948) = 1/(2987 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3734044201 / 1000000000) (-746808839 / 200000000) (Real.log (2987 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4414493983 / 1000000000) ≤ -Real.log (500000000000 / 41320006691201) ∧
    -Real.log (500000000000 / 41320006691201) ≤ (441449399 / 100000000) := by
  have h := checkLog_sound (w := (9320006691201 / 73320006691201)) (n := 12)
    (lo := (255610903 / 1000000000)) (hi := (31951363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41320006691201 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41320006691201 / 32000000000000) = 1/(500000000000 / 41320006691201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4414493983 / 1000000000) (441449399 / 100000000) (Real.log (41320006691201 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (41320006691201 / 500000000000) = -Real.log (500000000000 / 41320006691201) := by
    rw [show ((41320006691201 / 500000000000) : ℝ) = ((500000000000 / 41320006691201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4420820057 / 1000000000) ≤ -Real.log (500000000000 / 41582228674831) ∧
    -Real.log (500000000000 / 41582228674831) ≤ (138150627 / 31250000) := by
  have h := checkLog_sound (w := (9582228674831 / 73582228674831)) (n := 12)
    (lo := (261936977 / 1000000000)) (hi := (130968489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41582228674831 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41582228674831 / 32000000000000) = 1/(500000000000 / 41582228674831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4420820057 / 1000000000) (138150627 / 31250000) (Real.log (41582228674831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (41582228674831 / 500000000000) = -Real.log (500000000000 / 41582228674831) := by
    rw [show ((41582228674831 / 500000000000) : ℝ) = ((500000000000 / 41582228674831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3527003 / 800000) ≤ -Real.log (125000000000 / 10270874916833) ∧
    -Real.log (125000000000 / 10270874916833) ≤ (4408753757 / 1000000000) := by
  have h := checkLog_sound (w := (2270874916833 / 18270874916833)) (n := 12)
    (lo := (24987067 / 100000000)) (hi := (249870671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10270874916833 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10270874916833 / 8000000000000) = 1/(125000000000 / 10270874916833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3527003 / 800000) (4408753757 / 1000000000) (Real.log (10270874916833 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10270874916833 / 125000000000) = -Real.log (125000000000 / 10270874916833) := by
    rw [show ((10270874916833 / 125000000000) : ℝ) = ((125000000000 / 10270874916833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (137974107 / 31250000) ≤ -Real.log (250000000000 / 20674004017409) ∧
    -Real.log (250000000000 / 20674004017409) ≤ (4415171431 / 1000000000) := by
  have h := checkLog_sound (w := (4674004017409 / 36674004017409)) (n := 12)
    (lo := (32036043 / 125000000)) (hi := (51257669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20674004017409 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20674004017409 / 16000000000000) = 1/(250000000000 / 20674004017409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (137974107 / 31250000) (4415171431 / 1000000000) (Real.log (20674004017409 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20674004017409 / 250000000000) = -Real.log (250000000000 / 20674004017409) := by
    rw [show ((20674004017409 / 250000000000) : ℝ) = ((250000000000 / 20674004017409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052
