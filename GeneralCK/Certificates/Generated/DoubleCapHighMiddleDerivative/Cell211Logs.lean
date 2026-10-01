import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell211
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

theorem reflection_log_1_neg : (317885387 / 1000000000) ≤ -Real.log (1280 / 1759) ∧
    -Real.log (1280 / 1759) ≤ (79471347 / 250000000) := by
  have h := checkLog_sound (w := (479 / 3039)) (n := 12)
    (lo := (317885387 / 1000000000)) (hi := (79471347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759 / 1280) = 1/(1280 / 1759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (317885387 / 1000000000) (79471347 / 250000000) (Real.log (1759 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1759 / 1280) = -Real.log (1280 / 1759) := by
    rw [show ((1759 / 1280) : ℝ) = ((1280 / 1759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (468754409 / 1000000000) ≤ -Real.log (801 / 1280) ∧
    -Real.log (801 / 1280) ≤ (46875441 / 100000000) := by
  have h := checkLog_sound (w := (479 / 2081)) (n := 12)
    (lo := (468754409 / 1000000000)) (hi := (46875441 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 801) = 1/(801 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46875441 / 100000000) (-468754409 / 1000000000) (Real.log (801 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158729459 / 500000000) ≤ -Real.log (5120 / 7033) ∧
    -Real.log (5120 / 7033) ≤ (317458919 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 12153)) (n := 12)
    (lo := (158729459 / 500000000)) (hi := (317458919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7033 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7033 / 5120) = 1/(5120 / 7033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158729459 / 500000000) (317458919 / 1000000000) (Real.log (7033 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7033 / 5120) = -Real.log (5120 / 7033) := by
    rw [show ((7033 / 5120) : ℝ) = ((5120 / 7033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (233909259 / 500000000) ≤ -Real.log (3207 / 5120) ∧
    -Real.log (3207 / 5120) ≤ (467818519 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 8327)) (n := 12)
    (lo := (233909259 / 500000000)) (hi := (467818519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3207) = 1/(3207 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-467818519 / 1000000000) (-233909259 / 500000000) (Real.log (3207 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235728823 / 1000000000) ≤ -Real.log (1000000 / 1265831) ∧
    -Real.log (1000000 / 1265831) ≤ (29466103 / 125000000) := by
  have h := checkLog_sound (w := (265831 / 2265831)) (n := 12)
    (lo := (235728823 / 1000000000)) (hi := (29466103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265831 / 1000000) = 1/(1000000 / 1265831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235728823 / 1000000000) (29466103 / 125000000) (Real.log (1265831 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1265831 / 1000000) = -Real.log (1000000 / 1265831) := by
    rw [show ((1265831 / 1000000) : ℝ) = ((1000000 / 1265831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (309016031 / 1000000000) ≤ -Real.log (734169 / 1000000) ∧
    -Real.log (734169 / 1000000) ≤ (9656751 / 31250000) := by
  have h := checkLog_sound (w := (265831 / 1734169)) (n := 12)
    (lo := (309016031 / 1000000000)) (hi := (9656751 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734169) = 1/(734169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9656751 / 31250000) (-309016031 / 1000000000) (Real.log (734169 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47212587 / 200000000) ≤ -Real.log (500000 / 633127) ∧
    -Real.log (500000 / 633127) ≤ (29507867 / 125000000) := by
  have h := checkLog_sound (w := (133127 / 1133127)) (n := 12)
    (lo := (47212587 / 200000000)) (hi := (29507867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633127 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633127 / 500000) = 1/(500000 / 633127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47212587 / 200000000) (29507867 / 125000000) (Real.log (633127 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (633127 / 500000) = -Real.log (500000 / 633127) := by
    rw [show ((633127 / 500000) : ℝ) = ((500000 / 633127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (309592359 / 1000000000) ≤ -Real.log (366873 / 500000) ∧
    -Real.log (366873 / 500000) ≤ (7739809 / 25000000) := by
  have h := checkLog_sound (w := (133127 / 866873)) (n := 12)
    (lo := (309592359 / 1000000000)) (hi := (7739809 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 366873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 366873) = 1/(366873 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-7739809 / 25000000) (-309592359 / 1000000000) (Real.log (366873 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175400159 / 1000000000) ≤ -Real.log (1000000 / 1191723) ∧
    -Real.log (1000000 / 1191723) ≤ (1096251 / 6250000) := by
  have h := checkLog_sound (w := (191723 / 2191723)) (n := 12)
    (lo := (175400159 / 1000000000)) (hi := (1096251 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191723 / 1000000) = 1/(1000000 / 1191723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175400159 / 1000000000) (1096251 / 6250000) (Real.log (1191723 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1191723 / 1000000) = -Real.log (1000000 / 1191723) := by
    rw [show ((1191723 / 1000000) : ℝ) = ((1000000 / 1191723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (212850457 / 1000000000) ≤ -Real.log (808277 / 1000000) ∧
    -Real.log (808277 / 1000000) ≤ (106425229 / 500000000) := by
  have h := checkLog_sound (w := (191723 / 1808277)) (n := 12)
    (lo := (212850457 / 1000000000)) (hi := (106425229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808277) = 1/(808277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106425229 / 500000000) (-212850457 / 1000000000) (Real.log (808277 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43916741 / 250000000) ≤ -Real.log (1000000 / 1192041) ∧
    -Real.log (1000000 / 1192041) ≤ (35133393 / 200000000) := by
  have h := checkLog_sound (w := (192041 / 2192041)) (n := 12)
    (lo := (43916741 / 250000000)) (hi := (35133393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192041 / 1000000) = 1/(1000000 / 1192041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43916741 / 250000000) (35133393 / 200000000) (Real.log (1192041 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1192041 / 1000000) = -Real.log (1000000 / 1192041) := by
    rw [show ((1192041 / 1000000) : ℝ) = ((1000000 / 1192041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53310991 / 250000000) ≤ -Real.log (807959 / 1000000) ∧
    -Real.log (807959 / 1000000) ≤ (42648793 / 200000000) := by
  have h := checkLog_sound (w := (192041 / 1807959)) (n := 12)
    (lo := (53310991 / 250000000)) (hi := (42648793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807959) = 1/(807959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42648793 / 200000000) (-53310991 / 250000000) (Real.log (807959 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (196319359 / 250000000) ≤ -Real.log (250000000000 / 548253819769) ∧
    -Real.log (250000000000 / 548253819769) ≤ (392638719 / 500000000) := by
  have h := checkLog_sound (w := (48253819769 / 1048253819769)) (n := 12)
    (lo := (5758141 / 62500000)) (hi := (92130257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548253819769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(548253819769 / 500000000000) = 1/(250000000000 / 548253819769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (196319359 / 250000000) (392638719 / 500000000) (Real.log (548253819769 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (548253819769 / 250000000000) = -Real.log (250000000000 / 548253819769) := by
    rw [show ((548253819769 / 250000000000) : ℝ) = ((250000000000 / 548253819769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (786639797 / 1000000000) ≤ -Real.log (500000000000 / 1098002496879) ∧
    -Real.log (500000000000 / 1098002496879) ≤ (786639799 / 1000000000) := by
  have h := checkLog_sound (w := (98002496879 / 2098002496879)) (n := 12)
    (lo := (93492617 / 1000000000)) (hi := (46746309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098002496879 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1098002496879 / 1000000000000) = 1/(500000000000 / 1098002496879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (786639797 / 1000000000) (786639799 / 1000000000) (Real.log (1098002496879 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1098002496879 / 500000000000) = -Real.log (500000000000 / 1098002496879) := by
    rw [show ((1098002496879 / 500000000000) : ℝ) = ((500000000000 / 1098002496879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108948971 / 200000000) ≤ -Real.log (500000000000 / 862084206769) ∧
    -Real.log (500000000000 / 862084206769) ≤ (68093107 / 125000000) := by
  have h := checkLog_sound (w := (362084206769 / 1362084206769)) (n := 12)
    (lo := (108948971 / 200000000)) (hi := (68093107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862084206769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862084206769 / 500000000000) = 1/(500000000000 / 862084206769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108948971 / 200000000) (68093107 / 125000000) (Real.log (862084206769 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (862084206769 / 500000000000) = -Real.log (500000000000 / 862084206769) := by
    rw [show ((862084206769 / 500000000000) : ℝ) = ((500000000000 / 862084206769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272827647 / 500000000) ≤ -Real.log (250000000000 / 431434719917) ∧
    -Real.log (250000000000 / 431434719917) ≤ (109131059 / 200000000) := by
  have h := checkLog_sound (w := (181434719917 / 681434719917)) (n := 12)
    (lo := (272827647 / 500000000)) (hi := (109131059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431434719917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431434719917 / 250000000000) = 1/(250000000000 / 431434719917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (272827647 / 500000000) (109131059 / 200000000) (Real.log (431434719917 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (431434719917 / 250000000000) = -Real.log (250000000000 / 431434719917) := by
    rw [show ((431434719917 / 250000000000) : ℝ) = ((250000000000 / 431434719917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (48531327 / 125000000) ≤ -Real.log (125000000000 / 184299905849) ∧
    -Real.log (125000000000 / 184299905849) ≤ (388250617 / 1000000000) := by
  have h := checkLog_sound (w := (59299905849 / 309299905849)) (n := 12)
    (lo := (48531327 / 125000000)) (hi := (388250617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184299905849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184299905849 / 125000000000) = 1/(125000000000 / 184299905849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (48531327 / 125000000) (388250617 / 1000000000) (Real.log (184299905849 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (184299905849 / 125000000000) = -Real.log (125000000000 / 184299905849) := by
    rw [show ((184299905849 / 125000000000) : ℝ) = ((125000000000 / 184299905849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (24306933 / 62500000) ≤ -Real.log (500000000000 / 737686565779) ∧
    -Real.log (500000000000 / 737686565779) ≤ (388910929 / 1000000000) := by
  have h := checkLog_sound (w := (237686565779 / 1237686565779)) (n := 12)
    (lo := (24306933 / 62500000)) (hi := (388910929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737686565779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737686565779 / 500000000000) = 1/(500000000000 / 737686565779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (24306933 / 62500000) (388910929 / 1000000000) (Real.log (737686565779 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (737686565779 / 500000000000) = -Real.log (500000000000 / 737686565779) := by
    rw [show ((737686565779 / 500000000000) : ℝ) = ((500000000000 / 737686565779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37577 / 1000000) ≤ -Real.log (963120254319 / 1000000000000) ∧
    -Real.log (963120254319 / 1000000000000) ≤ (37577001 / 1000000000) := by
  have h := checkLog_sound (w := (36879745681 / 1963120254319)) (n := 12)
    (lo := (37577 / 1000000)) (hi := (37577001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963120254319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963120254319) = 1/(963120254319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37577001 / 1000000000) (-37577 / 1000000) (Real.log (963120254319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18725149 / 500000000) ≤ -Real.log (963242291271 / 1000000000000) ∧
    -Real.log (963242291271 / 1000000000000) ≤ (37450299 / 1000000000) := by
  have h := checkLog_sound (w := (36757708729 / 1963242291271)) (n := 12)
    (lo := (18725149 / 500000000)) (hi := (37450299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963242291271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963242291271) = 1/(963242291271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-37450299 / 1000000000) (-18725149 / 500000000) (Real.log (963242291271 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell211
