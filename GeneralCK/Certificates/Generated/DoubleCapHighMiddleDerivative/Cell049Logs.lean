import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell049
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

theorem reflection_log_1_neg : (24631061 / 100000000) ≤ -Real.log (512 / 655) ∧
    -Real.log (512 / 655) ≤ (246310611 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1167)) (n := 12)
    (lo := (24631061 / 100000000)) (hi := (246310611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655 / 512) = 1/(512 / 655) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (24631061 / 100000000) (246310611 / 1000000000) (Real.log (655 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (655 / 512) = -Real.log (512 / 655) := by
    rw [show ((655 / 512) : ℝ) = ((512 / 655) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16376399 / 50000000) ≤ -Real.log (369 / 512) ∧
    -Real.log (369 / 512) ≤ (327527981 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 881)) (n := 12)
    (lo := (16376399 / 50000000)) (hi := (327527981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 369) = 1/(369 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-327527981 / 1000000000) (-16376399 / 50000000) (Real.log (369 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24585249 / 100000000) ≤ -Real.log (5120 / 6547) ∧
    -Real.log (5120 / 6547) ≤ (245852491 / 1000000000) := by
  have h := checkLog_sound (w := (1427 / 11667)) (n := 12)
    (lo := (24585249 / 100000000)) (hi := (245852491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6547 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6547 / 5120) = 1/(5120 / 6547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24585249 / 100000000) (245852491 / 1000000000) (Real.log (6547 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6547 / 5120) = -Real.log (5120 / 6547) := by
    rw [show ((6547 / 5120) : ℝ) = ((5120 / 6547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (326715303 / 1000000000) ≤ -Real.log (3693 / 5120) ∧
    -Real.log (3693 / 5120) ≤ (40839413 / 125000000) := by
  have h := checkLog_sound (w := (1427 / 8813)) (n := 12)
    (lo := (326715303 / 1000000000)) (hi := (40839413 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3693) = 1/(3693 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40839413 / 125000000) (-326715303 / 1000000000) (Real.log (3693 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180433943 / 1000000000) ≤ -Real.log (1000000 / 1197737) ∧
    -Real.log (1000000 / 1197737) ≤ (22554243 / 125000000) := by
  have h := checkLog_sound (w := (197737 / 2197737)) (n := 12)
    (lo := (180433943 / 1000000000)) (hi := (22554243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197737 / 1000000) = 1/(1000000 / 1197737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180433943 / 1000000000) (22554243 / 125000000) (Real.log (1197737 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1197737 / 1000000) = -Real.log (1000000 / 1197737) := by
    rw [show ((1197737 / 1000000) : ℝ) = ((1000000 / 1197737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110159397 / 500000000) ≤ -Real.log (802263 / 1000000) ∧
    -Real.log (802263 / 1000000) ≤ (44063759 / 200000000) := by
  have h := checkLog_sound (w := (197737 / 1802263)) (n := 12)
    (lo := (110159397 / 500000000)) (hi := (44063759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802263) = 1/(802263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-44063759 / 200000000) (-110159397 / 500000000) (Real.log (802263 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (90392271 / 500000000) ≤ -Real.log (1000000 / 1198157) ∧
    -Real.log (1000000 / 1198157) ≤ (180784543 / 1000000000) := by
  have h := checkLog_sound (w := (198157 / 2198157)) (n := 12)
    (lo := (90392271 / 500000000)) (hi := (180784543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198157 / 1000000) = 1/(1000000 / 1198157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (90392271 / 500000000) (180784543 / 1000000000) (Real.log (1198157 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1198157 / 1000000) = -Real.log (1000000 / 1198157) := by
    rw [show ((1198157 / 1000000) : ℝ) = ((1000000 / 1198157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4416849 / 20000000) ≤ -Real.log (801843 / 1000000) ∧
    -Real.log (801843 / 1000000) ≤ (220842451 / 1000000000) := by
  have h := checkLog_sound (w := (198157 / 1801843)) (n := 12)
    (lo := (4416849 / 20000000)) (hi := (220842451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801843) = 1/(801843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-220842451 / 1000000000) (-4416849 / 20000000) (Real.log (801843 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41317 / 312500) ≤ -Real.log (1000000 / 1141353) ∧
    -Real.log (1000000 / 1141353) ≤ (132214401 / 1000000000) := by
  have h := checkLog_sound (w := (141353 / 2141353)) (n := 12)
    (lo := (41317 / 312500)) (hi := (132214401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141353 / 1000000) = 1/(1000000 / 1141353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41317 / 312500) (132214401 / 1000000000) (Real.log (1141353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141353 / 1000000) = -Real.log (1000000 / 1141353) := by
    rw [show ((1141353 / 1000000) : ℝ) = ((1000000 / 1141353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19049673 / 125000000) ≤ -Real.log (858647 / 1000000) ∧
    -Real.log (858647 / 1000000) ≤ (30479477 / 200000000) := by
  have h := checkLog_sound (w := (141353 / 1858647)) (n := 12)
    (lo := (19049673 / 125000000)) (hi := (30479477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858647) = 1/(858647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30479477 / 200000000) (-19049673 / 125000000) (Real.log (858647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132483343 / 1000000000) ≤ -Real.log (50000 / 57083) ∧
    -Real.log (50000 / 57083) ≤ (8280209 / 62500000) := by
  have h := checkLog_sound (w := (7083 / 107083)) (n := 12)
    (lo := (132483343 / 1000000000)) (hi := (8280209 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57083 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57083 / 50000) = 1/(50000 / 57083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132483343 / 1000000000) (8280209 / 62500000) (Real.log (57083 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57083 / 50000) = -Real.log (50000 / 57083) := by
    rw [show ((57083 / 50000) : ℝ) = ((50000 / 57083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (152754987 / 1000000000) ≤ -Real.log (42917 / 50000) ∧
    -Real.log (42917 / 50000) ≤ (38188747 / 250000000) := by
  have h := checkLog_sound (w := (7083 / 92917)) (n := 12)
    (lo := (152754987 / 1000000000)) (hi := (38188747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42917) = 1/(42917 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38188747 / 250000000) (-152754987 / 1000000000) (Real.log (42917 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (572567793 / 1000000000) ≤ -Real.log (500000000000 / 886406715407) ∧
    -Real.log (500000000000 / 886406715407) ≤ (286283897 / 500000000) := by
  have h := checkLog_sound (w := (386406715407 / 1386406715407)) (n := 12)
    (lo := (572567793 / 1000000000)) (hi := (286283897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886406715407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886406715407 / 500000000000) = 1/(500000000000 / 886406715407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (572567793 / 1000000000) (286283897 / 500000000) (Real.log (886406715407 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (886406715407 / 500000000000) = -Real.log (500000000000 / 886406715407) := by
    rw [show ((886406715407 / 500000000000) : ℝ) = ((500000000000 / 886406715407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (573838591 / 1000000000) ≤ -Real.log (500000000000 / 887533875339) ∧
    -Real.log (500000000000 / 887533875339) ≤ (2241557 / 3906250) := by
  have h := checkLog_sound (w := (387533875339 / 1387533875339)) (n := 12)
    (lo := (573838591 / 1000000000)) (hi := (2241557 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887533875339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887533875339 / 500000000000) = 1/(500000000000 / 887533875339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (573838591 / 1000000000) (2241557 / 3906250) (Real.log (887533875339 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (887533875339 / 500000000000) = -Real.log (500000000000 / 887533875339) := by
    rw [show ((887533875339 / 500000000000) : ℝ) = ((500000000000 / 887533875339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (400752737 / 1000000000) ≤ -Real.log (500000000000 / 746474036569) ∧
    -Real.log (500000000000 / 746474036569) ≤ (200376369 / 500000000) := by
  have h := checkLog_sound (w := (246474036569 / 1246474036569)) (n := 12)
    (lo := (400752737 / 1000000000)) (hi := (200376369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746474036569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746474036569 / 500000000000) = 1/(500000000000 / 746474036569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (400752737 / 1000000000) (200376369 / 500000000) (Real.log (746474036569 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (746474036569 / 500000000000) = -Real.log (500000000000 / 746474036569) := by
    rw [show ((746474036569 / 500000000000) : ℝ) = ((500000000000 / 746474036569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (401626993 / 1000000000) ≤ -Real.log (125000000000 / 186781732833) ∧
    -Real.log (125000000000 / 186781732833) ≤ (200813497 / 500000000) := by
  have h := checkLog_sound (w := (61781732833 / 311781732833)) (n := 12)
    (lo := (401626993 / 1000000000)) (hi := (200813497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186781732833 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186781732833 / 125000000000) = 1/(125000000000 / 186781732833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (401626993 / 1000000000) (200813497 / 500000000) (Real.log (186781732833 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (186781732833 / 125000000000) = -Real.log (125000000000 / 186781732833) := by
    rw [show ((186781732833 / 125000000000) : ℝ) = ((125000000000 / 186781732833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (56922357 / 200000000) ≤ -Real.log (500000000000 / 664622947497) ∧
    -Real.log (500000000000 / 664622947497) ≤ (142305893 / 500000000) := by
  have h := checkLog_sound (w := (164622947497 / 1164622947497)) (n := 12)
    (lo := (56922357 / 200000000)) (hi := (142305893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664622947497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664622947497 / 500000000000) = 1/(500000000000 / 664622947497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56922357 / 200000000) (142305893 / 500000000) (Real.log (664622947497 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (664622947497 / 500000000000) = -Real.log (500000000000 / 664622947497) := by
    rw [show ((664622947497 / 500000000000) : ℝ) = ((500000000000 / 664622947497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (285238331 / 1000000000) ≤ -Real.log (500000000000 / 665039494839) ∧
    -Real.log (500000000000 / 665039494839) ≤ (71309583 / 250000000) := by
  have h := checkLog_sound (w := (165039494839 / 1165039494839)) (n := 12)
    (lo := (285238331 / 1000000000)) (hi := (71309583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665039494839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665039494839 / 500000000000) = 1/(500000000000 / 665039494839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (285238331 / 1000000000) (71309583 / 250000000) (Real.log (665039494839 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (665039494839 / 500000000000) = -Real.log (500000000000 / 665039494839) := by
    rw [show ((665039494839 / 500000000000) : ℝ) = ((500000000000 / 665039494839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20271643 / 1000000000) ≤ -Real.log (2449831111 / 2500000000) ∧
    -Real.log (2449831111 / 2500000000) ≤ (5067911 / 250000000) := by
  have h := checkLog_sound (w := (50168889 / 4949831111)) (n := 12)
    (lo := (20271643 / 1000000000)) (hi := (5067911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2449831111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2449831111) = 1/(2449831111 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5067911 / 250000000) (-20271643 / 1000000000) (Real.log (2449831111 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20182983 / 1000000000) ≤ -Real.log (980019329391 / 1000000000000) ∧
    -Real.log (980019329391 / 1000000000000) ≤ (2522873 / 125000000) := by
  have h := checkLog_sound (w := (19980670609 / 1980019329391)) (n := 12)
    (lo := (20182983 / 1000000000)) (hi := (2522873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980019329391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980019329391) = 1/(980019329391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2522873 / 125000000) (-20182983 / 1000000000) (Real.log (980019329391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell049
