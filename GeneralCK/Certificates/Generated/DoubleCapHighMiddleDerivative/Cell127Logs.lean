import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell127
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

theorem reflection_log_1_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8780317 / 31250000) ≤ -Real.log (5120 / 6781) ∧
    -Real.log (5120 / 6781) ≤ (56194029 / 200000000) := by
  have h := checkLog_sound (w := (1661 / 11901)) (n := 12)
    (lo := (8780317 / 31250000)) (hi := (56194029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6781 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6781 / 5120) = 1/(5120 / 6781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8780317 / 31250000) (56194029 / 200000000) (Real.log (6781 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6781 / 5120) = -Real.log (5120 / 6781) := by
    rw [show ((6781 / 5120) : ℝ) = ((5120 / 6781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (392174909 / 1000000000) ≤ -Real.log (3459 / 5120) ∧
    -Real.log (3459 / 5120) ≤ (39217491 / 100000000) := by
  have h := checkLog_sound (w := (1661 / 8579)) (n := 12)
    (lo := (392174909 / 1000000000)) (hi := (39217491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3459) = 1/(3459 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-39217491 / 100000000) (-392174909 / 1000000000) (Real.log (3459 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207377517 / 1000000000) ≤ -Real.log (1000000 / 1230447) ∧
    -Real.log (1000000 / 1230447) ≤ (103688759 / 500000000) := by
  have h := checkLog_sound (w := (230447 / 2230447)) (n := 12)
    (lo := (207377517 / 1000000000)) (hi := (103688759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230447 / 1000000) = 1/(1000000 / 1230447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207377517 / 1000000000) (103688759 / 500000000) (Real.log (1230447 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230447 / 1000000) = -Real.log (1000000 / 1230447) := by
    rw [show ((1230447 / 1000000) : ℝ) = ((1000000 / 1230447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65486363 / 250000000) ≤ -Real.log (769553 / 1000000) ∧
    -Real.log (769553 / 1000000) ≤ (261945453 / 1000000000) := by
  have h := checkLog_sound (w := (230447 / 1769553)) (n := 12)
    (lo := (65486363 / 250000000)) (hi := (261945453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769553) = 1/(769553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-261945453 / 1000000000) (-65486363 / 250000000) (Real.log (769553 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207719611 / 1000000000) ≤ -Real.log (250000 / 307717) ∧
    -Real.log (250000 / 307717) ≤ (51929903 / 250000000) := by
  have h := checkLog_sound (w := (57717 / 557717)) (n := 12)
    (lo := (207719611 / 1000000000)) (hi := (51929903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307717 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307717 / 250000) = 1/(250000 / 307717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207719611 / 1000000000) (51929903 / 250000000) (Real.log (307717 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307717 / 250000) = -Real.log (250000 / 307717) := by
    rw [show ((307717 / 250000) : ℝ) = ((250000 / 307717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512681 / 1953125) ≤ -Real.log (192283 / 250000) ∧
    -Real.log (192283 / 250000) ≤ (262492673 / 1000000000) := by
  have h := checkLog_sound (w := (57717 / 442283)) (n := 12)
    (lo := (512681 / 1953125)) (hi := (262492673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192283) = 1/(192283 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-262492673 / 1000000000) (-512681 / 1953125) (Real.log (192283 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76525323 / 500000000) ≤ -Real.log (125000 / 145673) ∧
    -Real.log (125000 / 145673) ≤ (153050647 / 1000000000) := by
  have h := checkLog_sound (w := (20673 / 270673)) (n := 12)
    (lo := (76525323 / 500000000)) (hi := (153050647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145673 / 125000) = 1/(125000 / 145673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76525323 / 500000000) (153050647 / 1000000000) (Real.log (145673 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (145673 / 125000) = -Real.log (125000 / 145673) := by
    rw [show ((145673 / 125000) : ℝ) = ((125000 / 145673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9039177 / 50000000) ≤ -Real.log (104327 / 125000) ∧
    -Real.log (104327 / 125000) ≤ (180783541 / 1000000000) := by
  have h := checkLog_sound (w := (20673 / 229327)) (n := 12)
    (lo := (9039177 / 50000000)) (hi := (180783541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104327) = 1/(104327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180783541 / 1000000000) (-9039177 / 50000000) (Real.log (104327 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153318333 / 1000000000) ≤ -Real.log (15625 / 18214) ∧
    -Real.log (15625 / 18214) ≤ (76659167 / 500000000) := by
  have h := checkLog_sound (w := (2589 / 33839)) (n := 12)
    (lo := (153318333 / 1000000000)) (hi := (76659167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18214 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18214 / 15625) = 1/(15625 / 18214) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153318333 / 1000000000) (76659167 / 500000000) (Real.log (18214 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18214 / 15625) = -Real.log (15625 / 18214) := by
    rw [show ((18214 / 15625) : ℝ) = ((15625 / 18214) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90578717 / 500000000) ≤ -Real.log (13036 / 15625) ∧
    -Real.log (13036 / 15625) ≤ (36231487 / 200000000) := by
  have h := checkLog_sound (w := (2589 / 28661)) (n := 12)
    (lo := (90578717 / 500000000)) (hi := (36231487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13036) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13036) = 1/(13036 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36231487 / 200000000) (-90578717 / 500000000) (Real.log (13036 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673145053 / 1000000000) ≤ -Real.log (500000000000 / 980196588609) ∧
    -Real.log (500000000000 / 980196588609) ≤ (336572527 / 500000000) := by
  have h := checkLog_sound (w := (480196588609 / 1480196588609)) (n := 12)
    (lo := (673145053 / 1000000000)) (hi := (336572527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980196588609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980196588609 / 500000000000) = 1/(500000000000 / 980196588609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673145053 / 1000000000) (336572527 / 500000000) (Real.log (980196588609 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980196588609 / 500000000000) = -Real.log (500000000000 / 980196588609) := by
    rw [show ((980196588609 / 500000000000) : ℝ) = ((500000000000 / 980196588609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (674455047 / 1000000000) ≤ -Real.log (250000000000 / 490740740741) ∧
    -Real.log (250000000000 / 490740740741) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (240740740741 / 740740740741)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490740740741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490740740741 / 250000000000) = 1/(250000000000 / 490740740741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (490740740741 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (490740740741 / 250000000000) = -Real.log (250000000000 / 490740740741) := by
    rw [show ((490740740741 / 250000000000) : ℝ) = ((250000000000 / 490740740741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (46932297 / 100000000) ≤ -Real.log (62500000000 / 99931957253) ∧
    -Real.log (62500000000 / 99931957253) ≤ (469322971 / 1000000000) := by
  have h := checkLog_sound (w := (37431957253 / 162431957253)) (n := 12)
    (lo := (46932297 / 100000000)) (hi := (469322971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99931957253 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99931957253 / 62500000000) = 1/(62500000000 / 99931957253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46932297 / 100000000) (469322971 / 1000000000) (Real.log (99931957253 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (99931957253 / 62500000000) = -Real.log (62500000000 / 99931957253) := by
    rw [show ((99931957253 / 62500000000) : ℝ) = ((62500000000 / 99931957253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117553071 / 250000000) ≤ -Real.log (125000000000 / 200041735359) ∧
    -Real.log (125000000000 / 200041735359) ≤ (94042457 / 200000000) := by
  have h := checkLog_sound (w := (75041735359 / 325041735359)) (n := 12)
    (lo := (117553071 / 250000000)) (hi := (94042457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200041735359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200041735359 / 125000000000) = 1/(125000000000 / 200041735359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (117553071 / 250000000) (94042457 / 200000000) (Real.log (200041735359 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (200041735359 / 125000000000) = -Real.log (125000000000 / 200041735359) := by
    rw [show ((200041735359 / 125000000000) : ℝ) = ((125000000000 / 200041735359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (166917093 / 500000000) ≤ -Real.log (250000000000 / 349077899297) ∧
    -Real.log (250000000000 / 349077899297) ≤ (333834187 / 1000000000) := by
  have h := checkLog_sound (w := (99077899297 / 599077899297)) (n := 12)
    (lo := (166917093 / 500000000)) (hi := (333834187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349077899297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349077899297 / 250000000000) = 1/(250000000000 / 349077899297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166917093 / 500000000) (333834187 / 1000000000) (Real.log (349077899297 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349077899297 / 250000000000) = -Real.log (250000000000 / 349077899297) := by
    rw [show ((349077899297 / 250000000000) : ℝ) = ((250000000000 / 349077899297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41809471 / 125000000) ≤ -Real.log (500000000000 / 698603866217) ∧
    -Real.log (500000000000 / 698603866217) ≤ (334475769 / 1000000000) := by
  have h := checkLog_sound (w := (198603866217 / 1198603866217)) (n := 12)
    (lo := (41809471 / 125000000)) (hi := (334475769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698603866217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698603866217 / 500000000000) = 1/(500000000000 / 698603866217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41809471 / 125000000) (334475769 / 1000000000) (Real.log (698603866217 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (698603866217 / 500000000000) = -Real.log (500000000000 / 698603866217) := by
    rw [show ((698603866217 / 500000000000) : ℝ) = ((500000000000 / 698603866217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27839101 / 1000000000) ≤ -Real.log (237437704 / 244140625) ∧
    -Real.log (237437704 / 244140625) ≤ (13919551 / 500000000) := by
  have h := checkLog_sound (w := (6702921 / 481578329)) (n := 12)
    (lo := (27839101 / 1000000000)) (hi := (13919551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 237437704) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 237437704) = 1/(237437704 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13919551 / 500000000) (-27839101 / 1000000000) (Real.log (237437704 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27732893 / 1000000000) ≤ -Real.log (15197627071 / 15625000000) ∧
    -Real.log (15197627071 / 15625000000) ≤ (13866447 / 500000000) := by
  have h := checkLog_sound (w := (427372929 / 30822627071)) (n := 12)
    (lo := (27732893 / 1000000000)) (hi := (13866447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15197627071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15197627071) = 1/(15197627071 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13866447 / 500000000) (-27732893 / 1000000000) (Real.log (15197627071 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell127
