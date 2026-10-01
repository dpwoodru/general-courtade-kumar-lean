import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell210
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

theorem reflection_log_1_neg : (158729459 / 500000000) ≤ -Real.log (5120 / 7033) ∧
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


theorem reflection_log_1 : Bounds (158729459 / 500000000) (317458919 / 1000000000) (Real.log (7033 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7033 / 5120) = -Real.log (5120 / 7033) := by
    rw [show ((7033 / 5120) : ℝ) = ((5120 / 7033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (233909259 / 500000000) ≤ -Real.log (3207 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-467818519 / 1000000000) (-233909259 / 500000000) (Real.log (3207 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (158516133 / 500000000) ≤ -Real.log (512 / 703) ∧
    -Real.log (512 / 703) ≤ (317032267 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1215)) (n := 12)
    (lo := (158516133 / 500000000)) (hi := (317032267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 512) = 1/(512 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (158516133 / 500000000) (317032267 / 1000000000) (Real.log (703 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (703 / 512) = -Real.log (512 / 703) := by
    rw [show ((703 / 512) : ℝ) = ((512 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (466883501 / 1000000000) ≤ -Real.log (321 / 512) ∧
    -Real.log (321 / 512) ≤ (233441751 / 500000000) := by
  have h := checkLog_sound (w := (191 / 833)) (n := 12)
    (lo := (466883501 / 1000000000)) (hi := (233441751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 321) = 1/(321 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-233441751 / 500000000) (-466883501 / 1000000000) (Real.log (321 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235394599 / 1000000000) ≤ -Real.log (15625 / 19772) ∧
    -Real.log (15625 / 19772) ≤ (1176973 / 5000000) := by
  have h := checkLog_sound (w := (4147 / 35397)) (n := 12)
    (lo := (235394599 / 1000000000)) (hi := (1176973 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19772 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19772 / 15625) = 1/(15625 / 19772) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235394599 / 1000000000) (1176973 / 5000000) (Real.log (19772 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19772 / 15625) = -Real.log (15625 / 19772) := by
    rw [show ((19772 / 15625) : ℝ) = ((15625 / 19772) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (61688007 / 200000000) ≤ -Real.log (11478 / 15625) ∧
    -Real.log (11478 / 15625) ≤ (77110009 / 250000000) := by
  have h := checkLog_sound (w := (4147 / 27103)) (n := 12)
    (lo := (61688007 / 200000000)) (hi := (77110009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11478) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11478) = 1/(11478 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77110009 / 250000000) (-61688007 / 200000000) (Real.log (11478 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (235729613 / 1000000000) ≤ -Real.log (125000 / 158229) ∧
    -Real.log (125000 / 158229) ≤ (117864807 / 500000000) := by
  have h := checkLog_sound (w := (33229 / 283229)) (n := 12)
    (lo := (235729613 / 1000000000)) (hi := (117864807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158229 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158229 / 125000) = 1/(125000 / 158229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (235729613 / 1000000000) (117864807 / 500000000) (Real.log (158229 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158229 / 125000) = -Real.log (125000 / 158229) := by
    rw [show ((158229 / 125000) : ℝ) = ((125000 / 158229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (309017393 / 1000000000) ≤ -Real.log (91771 / 125000) ∧
    -Real.log (91771 / 125000) ≤ (154508697 / 500000000) := by
  have h := checkLog_sound (w := (33229 / 216771)) (n := 12)
    (lo := (309017393 / 1000000000)) (hi := (154508697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91771) = 1/(91771 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154508697 / 500000000) (-309017393 / 1000000000) (Real.log (91771 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (87567061 / 500000000) ≤ -Real.log (500000 / 595703) ∧
    -Real.log (500000 / 595703) ≤ (175134123 / 1000000000) := by
  have h := checkLog_sound (w := (95703 / 1095703)) (n := 12)
    (lo := (87567061 / 500000000)) (hi := (175134123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595703 / 500000) = 1/(500000 / 595703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (87567061 / 500000000) (175134123 / 1000000000) (Real.log (595703 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (595703 / 500000) = -Real.log (500000 / 595703) := by
    rw [show ((595703 / 500000) : ℝ) = ((500000 / 595703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (106229171 / 500000000) ≤ -Real.log (404297 / 500000) ∧
    -Real.log (404297 / 500000) ≤ (212458343 / 1000000000) := by
  have h := checkLog_sound (w := (95703 / 904297)) (n := 12)
    (lo := (106229171 / 500000000)) (hi := (212458343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404297) = 1/(404297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-212458343 / 1000000000) (-106229171 / 500000000) (Real.log (404297 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (87700499 / 500000000) ≤ -Real.log (250000 / 297931) ∧
    -Real.log (250000 / 297931) ≤ (175400999 / 1000000000) := by
  have h := checkLog_sound (w := (47931 / 547931)) (n := 12)
    (lo := (87700499 / 500000000)) (hi := (175400999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297931 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297931 / 250000) = 1/(250000 / 297931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (87700499 / 500000000) (175400999 / 1000000000) (Real.log (297931 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (297931 / 250000) = -Real.log (250000 / 297931) := by
    rw [show ((297931 / 250000) : ℝ) = ((250000 / 297931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106425847 / 500000000) ≤ -Real.log (202069 / 250000) ∧
    -Real.log (202069 / 250000) ≤ (42570339 / 200000000) := by
  have h := checkLog_sound (w := (47931 / 452069)) (n := 12)
    (lo := (106425847 / 500000000)) (hi := (42570339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202069) = 1/(202069 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42570339 / 200000000) (-106425847 / 500000000) (Real.log (202069 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97989471 / 125000000) ≤ -Real.log (500000000000 / 1095015576323) ∧
    -Real.log (500000000000 / 1095015576323) ≤ (78391577 / 100000000) := by
  have h := checkLog_sound (w := (95015576323 / 2095015576323)) (n := 12)
    (lo := (22692147 / 250000000)) (hi := (90768589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095015576323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1095015576323 / 1000000000000) = 1/(500000000000 / 1095015576323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97989471 / 125000000) (78391577 / 100000000) (Real.log (1095015576323 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1095015576323 / 500000000000) = -Real.log (500000000000 / 1095015576323) := by
    rw [show ((1095015576323 / 500000000000) : ℝ) = ((500000000000 / 1095015576323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (196319359 / 250000000) ≤ -Real.log (500000000000 / 1096507639539) ∧
    -Real.log (500000000000 / 1096507639539) ≤ (392638719 / 500000000) := by
  have h := checkLog_sound (w := (96507639539 / 2096507639539)) (n := 12)
    (lo := (5758141 / 62500000)) (hi := (92130257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096507639539 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096507639539 / 1000000000000) = 1/(500000000000 / 1096507639539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (196319359 / 250000000) (392638719 / 500000000) (Real.log (1096507639539 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1096507639539 / 500000000000) = -Real.log (500000000000 / 1096507639539) := by
    rw [show ((1096507639539 / 500000000000) : ℝ) = ((500000000000 / 1096507639539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108766927 / 200000000) ≤ -Real.log (500000000000 / 861299878027) ∧
    -Real.log (500000000000 / 861299878027) ≤ (135958659 / 250000000) := by
  have h := checkLog_sound (w := (361299878027 / 1361299878027)) (n := 12)
    (lo := (108766927 / 200000000)) (hi := (135958659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861299878027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861299878027 / 500000000000) = 1/(500000000000 / 861299878027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108766927 / 200000000) (135958659 / 250000000) (Real.log (861299878027 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (861299878027 / 500000000000) = -Real.log (500000000000 / 861299878027) := by
    rw [show ((861299878027 / 500000000000) : ℝ) = ((500000000000 / 861299878027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (544747007 / 1000000000) ≤ -Real.log (250000000000 / 431043031023) ∧
    -Real.log (250000000000 / 431043031023) ≤ (1063959 / 1953125) := by
  have h := checkLog_sound (w := (181043031023 / 681043031023)) (n := 12)
    (lo := (544747007 / 1000000000)) (hi := (1063959 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431043031023 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431043031023 / 250000000000) = 1/(250000000000 / 431043031023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (544747007 / 1000000000) (1063959 / 1953125) (Real.log (431043031023 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (431043031023 / 250000000000) = -Real.log (250000000000 / 431043031023) := by
    rw [show ((431043031023 / 250000000000) : ℝ) = ((250000000000 / 431043031023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (24224529 / 62500000) ≤ -Real.log (500000000000 / 736714593479) ∧
    -Real.log (500000000000 / 736714593479) ≤ (77518493 / 200000000) := by
  have h := checkLog_sound (w := (236714593479 / 1236714593479)) (n := 12)
    (lo := (24224529 / 62500000)) (hi := (77518493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736714593479 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736714593479 / 500000000000) = 1/(500000000000 / 736714593479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24224529 / 62500000) (77518493 / 200000000) (Real.log (736714593479 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (736714593479 / 500000000000) = -Real.log (500000000000 / 736714593479) := by
    rw [show ((736714593479 / 500000000000) : ℝ) = ((500000000000 / 736714593479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (97063173 / 250000000) ≤ -Real.log (250000000000 / 368600577031) ∧
    -Real.log (250000000000 / 368600577031) ≤ (388252693 / 1000000000) := by
  have h := checkLog_sound (w := (118600577031 / 618600577031)) (n := 12)
    (lo := (97063173 / 250000000)) (hi := (388252693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368600577031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368600577031 / 250000000000) = 1/(250000000000 / 368600577031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (97063173 / 250000000) (388252693 / 1000000000) (Real.log (368600577031 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (368600577031 / 250000000000) = -Real.log (250000000000 / 368600577031) := by
    rw [show ((368600577031 / 250000000000) : ℝ) = ((250000000000 / 368600577031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4681337 / 125000000) ≤ -Real.log (60202619239 / 62500000000) ∧
    -Real.log (60202619239 / 62500000000) ≤ (37450697 / 1000000000) := by
  have h := checkLog_sound (w := (2297380761 / 122702619239)) (n := 12)
    (lo := (4681337 / 125000000)) (hi := (37450697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60202619239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60202619239) = 1/(60202619239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37450697 / 1000000000) (-4681337 / 125000000) (Real.log (60202619239 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37324219 / 1000000000) ≤ -Real.log (240840935791 / 250000000000) ∧
    -Real.log (240840935791 / 250000000000) ≤ (1866211 / 50000000) := by
  have h := checkLog_sound (w := (9159064209 / 490840935791)) (n := 12)
    (lo := (37324219 / 1000000000)) (hi := (1866211 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240840935791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240840935791) = 1/(240840935791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1866211 / 50000000) (-37324219 / 1000000000) (Real.log (240840935791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell210
