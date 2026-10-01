import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0073
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

theorem reflection_log_1_neg : (676515497 / 1000000000) ≤ -Real.log (51200 / 100711) ∧
    -Real.log (51200 / 100711) ≤ (338257749 / 500000000) := by
  have h := checkLog_sound (w := (49511 / 151911)) (n := 12)
    (lo := (676515497 / 1000000000)) (hi := (338257749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100711 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100711 / 51200) = 1/(51200 / 100711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676515497 / 1000000000) (338257749 / 500000000) (Real.log (100711 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100711 / 51200) = -Real.log (51200 / 100711) := by
    rw [show ((100711 / 51200) : ℝ) = ((51200 / 100711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3411602891 / 1000000000) ≤ -Real.log (1689 / 51200) ∧
    -Real.log (1689 / 51200) ≤ (213225181 / 62500000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1689) = 1/(1689 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-213225181 / 62500000) (-3411602891 / 1000000000) (Real.log (1689 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33816341 / 50000000) ≤ -Real.log (12800 / 25173) ∧
    -Real.log (12800 / 25173) ≤ (676326821 / 1000000000) := by
  have h := checkLog_sound (w := (12373 / 37973)) (n := 12)
    (lo := (33816341 / 50000000)) (hi := (676326821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25173 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25173 / 12800) = 1/(12800 / 25173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33816341 / 50000000) (676326821 / 1000000000) (Real.log (25173 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25173 / 12800) = -Real.log (12800 / 25173) := by
    rw [show ((25173 / 12800) : ℝ) = ((12800 / 25173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1700208217 / 500000000) ≤ -Real.log (427 / 12800) ∧
    -Real.log (427 / 12800) ≤ (3400416439 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 427) = 1/(427 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3400416439 / 1000000000) (-1700208217 / 500000000) (Real.log (427 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (131920503 / 200000000) ≤ -Real.log (25600 / 49511) ∧
    -Real.log (25600 / 49511) ≤ (164900629 / 250000000) := by
  have h := checkLog_sound (w := (23911 / 75111)) (n := 12)
    (lo := (131920503 / 200000000)) (hi := (164900629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49511 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49511 / 25600) = 1/(25600 / 49511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (131920503 / 200000000) (164900629 / 250000000) (Real.log (49511 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49511 / 25600) = -Real.log (25600 / 49511) := by
    rw [show ((49511 / 25600) : ℝ) = ((25600 / 49511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2718455711 / 1000000000) ≤ -Real.log (1689 / 25600) ∧
    -Real.log (1689 / 25600) ≤ (543691143 / 200000000) := by
  have h := checkLog_sound (w := (1511 / 4889)) (n := 12)
    (lo := (639014171 / 1000000000)) (hi := (159753543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1689) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1689) = 1/(1689 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-543691143 / 200000000) (-2718455711 / 1000000000) (Real.log (1689 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2575073 / 3906250) ≤ -Real.log (6400 / 12373) ∧
    -Real.log (6400 / 12373) ≤ (659218689 / 1000000000) := by
  have h := checkLog_sound (w := (5973 / 18773)) (n := 12)
    (lo := (2575073 / 3906250)) (hi := (659218689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12373 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12373 / 6400) = 1/(6400 / 12373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2575073 / 3906250) (659218689 / 1000000000) (Real.log (12373 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12373 / 6400) = -Real.log (6400 / 12373) := by
    rw [show ((12373 / 6400) : ℝ) = ((6400 / 12373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1353634627 / 500000000) ≤ -Real.log (427 / 6400) ∧
    -Real.log (427 / 6400) ≤ (1353634629 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1227)) (n := 12)
    (lo := (313913857 / 500000000)) (hi := (125565543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 427) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 427) = 1/(427 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1353634629 / 500000000) (-1353634627 / 500000000) (Real.log (427 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135835613 / 200000000) ≤ -Real.log (31250 / 61633) ∧
    -Real.log (31250 / 61633) ≤ (339589033 / 500000000) := by
  have h := checkLog_sound (w := (30383 / 92883)) (n := 12)
    (lo := (135835613 / 200000000)) (hi := (339589033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61633 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61633 / 31250) = 1/(31250 / 61633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135835613 / 200000000) (339589033 / 500000000) (Real.log (61633 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61633 / 31250) = -Real.log (31250 / 61633) := by
    rw [show ((61633 / 31250) : ℝ) = ((31250 / 61633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (143389427 / 40000000) ≤ -Real.log (867 / 31250) ∧
    -Real.log (867 / 31250) ≤ (3584735681 / 1000000000) := by
  have h := checkLog_sound (w := (1753 / 29497)) (n := 12)
    (lo := (4759991 / 40000000)) (hi := (3718743 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13872) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13872) = 1/(867 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3584735681 / 1000000000) (-143389427 / 40000000) (Real.log (867 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169831907 / 250000000) ≤ -Real.log (1000000 / 1972551) ∧
    -Real.log (1000000 / 1972551) ≤ (679327629 / 1000000000) := by
  have h := checkLog_sound (w := (972551 / 2972551)) (n := 12)
    (lo := (169831907 / 250000000)) (hi := (679327629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972551 / 1000000) = 1/(1000000 / 1972551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169831907 / 250000000) (679327629 / 1000000000) (Real.log (1972551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1972551 / 1000000) = -Real.log (1000000 / 1972551) := by
    rw [show ((1972551 / 1000000) : ℝ) = ((1000000 / 1972551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1797712769 / 500000000) ≤ -Real.log (27449 / 1000000) ∧
    -Real.log (27449 / 1000000) ≤ (449428193 / 125000000) := by
  have h := checkLog_sound (w := (3801 / 58699)) (n := 12)
    (lo := (64844819 / 500000000)) (hi := (129689639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27449) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27449) = 1/(27449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-449428193 / 125000000) (-1797712769 / 500000000) (Real.log (27449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67908071 / 100000000) ≤ -Real.log (31250 / 61627) ∧
    -Real.log (31250 / 61627) ≤ (679080711 / 1000000000) := by
  have h := checkLog_sound (w := (30377 / 92877)) (n := 12)
    (lo := (67908071 / 100000000)) (hi := (679080711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61627 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61627 / 31250) = 1/(31250 / 61627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67908071 / 100000000) (679080711 / 1000000000) (Real.log (61627 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61627 / 31250) = -Real.log (31250 / 61627) := by
    rw [show ((61627 / 31250) : ℝ) = ((31250 / 61627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (447229887 / 125000000) ≤ -Real.log (873 / 31250) ∧
    -Real.log (873 / 31250) ≤ (1788919551 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 29593)) (n := 12)
    (lo := (28025799 / 250000000)) (hi := (112103197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13968) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13968) = 1/(873 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1788919551 / 500000000) (-447229887 / 125000000) (Real.log (873 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (169808079 / 250000000) ≤ -Real.log (1000000 / 1972363) ∧
    -Real.log (1000000 / 1972363) ≤ (679232317 / 1000000000) := by
  have h := checkLog_sound (w := (972363 / 2972363)) (n := 12)
    (lo := (169808079 / 250000000)) (hi := (679232317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972363 / 1000000) = 1/(1000000 / 1972363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (169808079 / 250000000) (679232317 / 1000000000) (Real.log (1972363 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972363 / 1000000) = -Real.log (1000000 / 1972363) := by
    rw [show ((1972363 / 1000000) : ℝ) = ((1000000 / 1972363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3588599821 / 1000000000) ≤ -Real.log (27637 / 1000000) ∧
    -Real.log (27637 / 1000000) ≤ (3588599827 / 1000000000) := by
  have h := checkLog_sound (w := (3613 / 58887)) (n := 12)
    (lo := (122863921 / 1000000000)) (hi := (61431961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27637) = 1/(27637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3588599827 / 1000000000) (-3588599821 / 1000000000) (Real.log (27637 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (213195687 / 50000000) ≤ -Real.log (62500000000 / 4442978662053) ∧
    -Real.log (62500000000 / 4442978662053) ≤ (4263913747 / 1000000000) := by
  have h := checkLog_sound (w := (442978662053 / 8442978662053)) (n := 12)
    (lo := (5251533 / 50000000)) (hi := (105030661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4442978662053 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4442978662053 / 4000000000000) = 1/(62500000000 / 4442978662053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (213195687 / 50000000) (4263913747 / 1000000000) (Real.log (4442978662053 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4442978662053 / 62500000000) = -Real.log (62500000000 / 4442978662053) := by
    rw [show ((4442978662053 / 62500000000) : ℝ) = ((62500000000 / 4442978662053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4274753167 / 1000000000) ≤ -Real.log (250000000000 / 17965599839703) ∧
    -Real.log (250000000000 / 17965599839703) ≤ (2137376587 / 500000000) := by
  have h := checkLog_sound (w := (1965599839703 / 33965599839703)) (n := 12)
    (lo := (115870087 / 1000000000)) (hi := (14483761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17965599839703 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17965599839703 / 16000000000000) = 1/(250000000000 / 17965599839703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4274753167 / 1000000000) (2137376587 / 500000000) (Real.log (17965599839703 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17965599839703 / 250000000000) = -Real.log (250000000000 / 17965599839703) := by
    rw [show ((17965599839703 / 250000000000) : ℝ) = ((250000000000 / 17965599839703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (851383961 / 200000000) ≤ -Real.log (250000000000 / 17648052691867) ∧
    -Real.log (250000000000 / 17648052691867) ≤ (1064229953 / 250000000) := by
  have h := checkLog_sound (w := (1648052691867 / 33648052691867)) (n := 12)
    (lo := (3921469 / 40000000)) (hi := (49018363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17648052691867 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(17648052691867 / 16000000000000) = 1/(250000000000 / 17648052691867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (851383961 / 200000000) (1064229953 / 250000000) (Real.log (17648052691867 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17648052691867 / 250000000000) = -Real.log (250000000000 / 17648052691867) := by
    rw [show ((17648052691867 / 250000000000) : ℝ) = ((250000000000 / 17648052691867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4267832137 / 1000000000) ≤ -Real.log (500000000000 / 35683377356443) ∧
    -Real.log (500000000000 / 35683377356443) ≤ (266739509 / 62500000) := by
  have h := checkLog_sound (w := (3683377356443 / 67683377356443)) (n := 12)
    (lo := (108949057 / 1000000000)) (hi := (54474529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35683377356443 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(35683377356443 / 32000000000000) = 1/(500000000000 / 35683377356443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4267832137 / 1000000000) (266739509 / 62500000) (Real.log (35683377356443 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (35683377356443 / 500000000000) = -Real.log (500000000000 / 35683377356443) := by
    rw [show ((35683377356443 / 500000000000) : ℝ) = ((500000000000 / 35683377356443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0073
