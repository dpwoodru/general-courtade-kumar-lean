import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell131
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

theorem reflection_log_1_neg : (70794941 / 250000000) ≤ -Real.log (1280 / 1699) ∧
    -Real.log (1280 / 1699) ≤ (56635953 / 200000000) := by
  have h := checkLog_sound (w := (419 / 2979)) (n := 12)
    (lo := (70794941 / 250000000)) (hi := (56635953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1699 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1699 / 1280) = 1/(1280 / 1699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (70794941 / 250000000) (56635953 / 200000000) (Real.log (1699 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1699 / 1280) = -Real.log (1280 / 1699) := by
    rw [show ((1699 / 1280) : ℝ) = ((1280 / 1699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99130213 / 250000000) ≤ -Real.log (861 / 1280) ∧
    -Real.log (861 / 1280) ≤ (396520853 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 861) = 1/(861 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-396520853 / 1000000000) (-99130213 / 250000000) (Real.log (861 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (282738231 / 1000000000) ≤ -Real.log (5120 / 6793) ∧
    -Real.log (5120 / 6793) ≤ (35342279 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 11913)) (n := 12)
    (lo := (282738231 / 1000000000)) (hi := (35342279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6793 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6793 / 5120) = 1/(5120 / 6793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (282738231 / 1000000000) (35342279 / 125000000) (Real.log (6793 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6793 / 5120) = -Real.log (5120 / 6793) := by
    rw [show ((6793 / 5120) : ℝ) = ((5120 / 6793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (395650151 / 1000000000) ≤ -Real.log (3447 / 5120) ∧
    -Real.log (3447 / 5120) ≤ (49456269 / 125000000) := by
  have h := checkLog_sound (w := (1673 / 8567)) (n := 12)
    (lo := (395650151 / 1000000000)) (hi := (49456269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3447) = 1/(3447 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49456269 / 125000000) (-395650151 / 1000000000) (Real.log (3447 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41748551 / 200000000) ≤ -Real.log (15625 / 19252) ∧
    -Real.log (15625 / 19252) ≤ (52185689 / 250000000) := by
  have h := checkLog_sound (w := (3627 / 34877)) (n := 12)
    (lo := (41748551 / 200000000)) (hi := (52185689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19252 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19252 / 15625) = 1/(15625 / 19252) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41748551 / 200000000) (52185689 / 250000000) (Real.log (19252 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19252 / 15625) = -Real.log (15625 / 19252) := by
    rw [show ((19252 / 15625) : ℝ) = ((15625 / 19252) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (132066113 / 500000000) ≤ -Real.log (11998 / 15625) ∧
    -Real.log (11998 / 15625) ≤ (264132227 / 1000000000) := by
  have h := checkLog_sound (w := (3627 / 27623)) (n := 12)
    (lo := (132066113 / 500000000)) (hi := (264132227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11998) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11998) = 1/(11998 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-264132227 / 1000000000) (-132066113 / 500000000) (Real.log (11998 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (104542597 / 500000000) ≤ -Real.log (20000 / 24651) ∧
    -Real.log (20000 / 24651) ≤ (41817039 / 200000000) := by
  have h := checkLog_sound (w := (4651 / 44651)) (n := 12)
    (lo := (104542597 / 500000000)) (hi := (41817039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 20000) = 1/(20000 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (104542597 / 500000000) (41817039 / 200000000) (Real.log (24651 / 20000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24651 / 20000) = -Real.log (20000 / 24651) := by
    rw [show ((24651 / 20000) : ℝ) = ((20000 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66170487 / 250000000) ≤ -Real.log (15349 / 20000) ∧
    -Real.log (15349 / 20000) ≤ (264681949 / 1000000000) := by
  have h := checkLog_sound (w := (4651 / 35349)) (n := 12)
    (lo := (66170487 / 250000000)) (hi := (264681949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15349) = 1/(15349 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-264681949 / 1000000000) (-66170487 / 250000000) (Real.log (15349 / 20000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (154116679 / 1000000000) ≤ -Real.log (1000000 / 1166627) ∧
    -Real.log (1000000 / 1166627) ≤ (3852917 / 25000000) := by
  have h := checkLog_sound (w := (166627 / 2166627)) (n := 12)
    (lo := (154116679 / 1000000000)) (hi := (3852917 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166627 / 1000000) = 1/(1000000 / 1166627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (154116679 / 1000000000) (3852917 / 25000000) (Real.log (1166627 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1166627 / 1000000) = -Real.log (1000000 / 1166627) := by
    rw [show ((1166627 / 1000000) : ℝ) = ((1000000 / 1166627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182273957 / 1000000000) ≤ -Real.log (833373 / 1000000) ∧
    -Real.log (833373 / 1000000) ≤ (91136979 / 500000000) := by
  have h := checkLog_sound (w := (166627 / 1833373)) (n := 12)
    (lo := (182273957 / 1000000000)) (hi := (91136979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833373) = 1/(833373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91136979 / 500000000) (-182273957 / 1000000000) (Real.log (833373 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154384081 / 1000000000) ≤ -Real.log (1000000 / 1166939) ∧
    -Real.log (1000000 / 1166939) ≤ (77192041 / 500000000) := by
  have h := checkLog_sound (w := (166939 / 2166939)) (n := 12)
    (lo := (154384081 / 1000000000)) (hi := (77192041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166939 / 1000000) = 1/(1000000 / 1166939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154384081 / 1000000000) (77192041 / 500000000) (Real.log (1166939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1166939 / 1000000) = -Real.log (1000000 / 1166939) := by
    rw [show ((1166939 / 1000000) : ℝ) = ((1000000 / 1166939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18264841 / 100000000) ≤ -Real.log (833061 / 1000000) ∧
    -Real.log (833061 / 1000000) ≤ (182648411 / 1000000000) := by
  have h := checkLog_sound (w := (166939 / 1833061)) (n := 12)
    (lo := (18264841 / 100000000)) (hi := (182648411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833061) = 1/(833061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-182648411 / 1000000000) (-18264841 / 100000000) (Real.log (833061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (339194191 / 500000000) ≤ -Real.log (31250000000 / 61584348709) ∧
    -Real.log (31250000000 / 61584348709) ≤ (678388383 / 1000000000) := by
  have h := checkLog_sound (w := (30334348709 / 92834348709)) (n := 12)
    (lo := (339194191 / 500000000)) (hi := (678388383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61584348709 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61584348709 / 31250000000) = 1/(31250000000 / 61584348709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (339194191 / 500000000) (678388383 / 1000000000) (Real.log (61584348709 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61584348709 / 31250000000) = -Real.log (31250000000 / 61584348709) := by
    rw [show ((61584348709 / 31250000000) : ℝ) = ((31250000000 / 61584348709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (679700617 / 1000000000) ≤ -Real.log (500000000000 / 986643437863) ∧
    -Real.log (500000000000 / 986643437863) ≤ (339850309 / 500000000) := by
  have h := checkLog_sound (w := (486643437863 / 1486643437863)) (n := 12)
    (lo := (679700617 / 1000000000)) (hi := (339850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986643437863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986643437863 / 500000000000) = 1/(500000000000 / 986643437863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (679700617 / 1000000000) (339850309 / 500000000) (Real.log (986643437863 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (986643437863 / 500000000000) = -Real.log (500000000000 / 986643437863) := by
    rw [show ((986643437863 / 500000000000) : ℝ) = ((500000000000 / 986643437863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (236437491 / 500000000) ≤ -Real.log (500000000000 / 802300383397) ∧
    -Real.log (500000000000 / 802300383397) ≤ (472874983 / 1000000000) := by
  have h := checkLog_sound (w := (302300383397 / 1302300383397)) (n := 12)
    (lo := (236437491 / 500000000)) (hi := (472874983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802300383397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802300383397 / 500000000000) = 1/(500000000000 / 802300383397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (236437491 / 500000000) (472874983 / 1000000000) (Real.log (802300383397 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (802300383397 / 500000000000) = -Real.log (500000000000 / 802300383397) := by
    rw [show ((802300383397 / 500000000000) : ℝ) = ((500000000000 / 802300383397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236883571 / 500000000) ≤ -Real.log (500000000000 / 803016483159) ∧
    -Real.log (500000000000 / 803016483159) ≤ (473767143 / 1000000000) := by
  have h := checkLog_sound (w := (303016483159 / 1303016483159)) (n := 12)
    (lo := (236883571 / 500000000)) (hi := (473767143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803016483159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803016483159 / 500000000000) = 1/(500000000000 / 803016483159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (236883571 / 500000000) (473767143 / 1000000000) (Real.log (803016483159 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (803016483159 / 500000000000) = -Real.log (500000000000 / 803016483159) := by
    rw [show ((803016483159 / 500000000000) : ℝ) = ((500000000000 / 803016483159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (336390637 / 1000000000) ≤ -Real.log (250000000000 / 349971441359) ∧
    -Real.log (250000000000 / 349971441359) ≤ (168195319 / 500000000) := by
  have h := checkLog_sound (w := (99971441359 / 599971441359)) (n := 12)
    (lo := (336390637 / 1000000000)) (hi := (168195319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349971441359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349971441359 / 250000000000) = 1/(250000000000 / 349971441359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (336390637 / 1000000000) (168195319 / 500000000) (Real.log (349971441359 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349971441359 / 250000000000) = -Real.log (250000000000 / 349971441359) := by
    rw [show ((349971441359 / 250000000000) : ℝ) = ((250000000000 / 349971441359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (337032491 / 1000000000) ≤ -Real.log (2500000000 / 3501961441) ∧
    -Real.log (2500000000 / 3501961441) ≤ (84258123 / 250000000) := by
  have h := checkLog_sound (w := (1001961441 / 6001961441)) (n := 12)
    (lo := (337032491 / 1000000000)) (hi := (84258123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501961441 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501961441 / 2500000000) = 1/(2500000000 / 3501961441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (337032491 / 1000000000) (84258123 / 250000000) (Real.log (3501961441 / 2500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3501961441 / 2500000000) = -Real.log (2500000000 / 3501961441) := by
    rw [show ((3501961441 / 2500000000) : ℝ) = ((2500000000 / 3501961441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28264329 / 1000000000) ≤ -Real.log (972131370279 / 1000000000000) ∧
    -Real.log (972131370279 / 1000000000000) ≤ (2826433 / 100000000) := by
  have h := checkLog_sound (w := (27868629721 / 1972131370279)) (n := 12)
    (lo := (28264329 / 1000000000)) (hi := (2826433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972131370279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972131370279) = 1/(972131370279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2826433 / 100000000) (-28264329 / 1000000000) (Real.log (972131370279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14078639 / 500000000) ≤ -Real.log (972235442871 / 1000000000000) ∧
    -Real.log (972235442871 / 1000000000000) ≤ (28157279 / 1000000000) := by
  have h := checkLog_sound (w := (27764557129 / 1972235442871)) (n := 12)
    (lo := (14078639 / 500000000)) (hi := (28157279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972235442871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972235442871) = 1/(972235442871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-28157279 / 1000000000) (-14078639 / 500000000) (Real.log (972235442871 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell131
