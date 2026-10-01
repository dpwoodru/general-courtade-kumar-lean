import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0092
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

theorem reflection_log_1_neg : (170046453 / 500000000) ≤ -Real.log (2560 / 3597) ∧
    -Real.log (2560 / 3597) ≤ (340092907 / 1000000000) := by
  have h := checkLog_sound (w := (1037 / 6157)) (n := 12)
    (lo := (170046453 / 500000000)) (hi := (340092907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3597 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3597 / 2560) = 1/(2560 / 3597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170046453 / 500000000) (340092907 / 1000000000) (Real.log (3597 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3597 / 2560) = -Real.log (2560 / 3597) := by
    rw [show ((3597 / 2560) : ℝ) = ((2560 / 3597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1014307 / 1953125) ≤ -Real.log (1523 / 2560) ∧
    -Real.log (1523 / 2560) ≤ (103865037 / 200000000) := by
  have h := checkLog_sound (w := (1037 / 4083)) (n := 12)
    (lo := (1014307 / 1953125)) (hi := (103865037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1523) = 1/(1523 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-103865037 / 200000000) (-1014307 / 1953125) (Real.log (1523 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339258529 / 1000000000) ≤ -Real.log (1280 / 1797) ∧
    -Real.log (1280 / 1797) ≤ (33925853 / 100000000) := by
  have h := checkLog_sound (w := (517 / 3077)) (n := 12)
    (lo := (339258529 / 1000000000)) (hi := (33925853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1797 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1797 / 1280) = 1/(1280 / 1797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339258529 / 1000000000) (33925853 / 100000000) (Real.log (1797 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1797 / 1280) = -Real.log (1280 / 1797) := by
    rw [show ((1797 / 1280) : ℝ) = ((1280 / 1797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20694293 / 40000000) ≤ -Real.log (763 / 1280) ∧
    -Real.log (763 / 1280) ≤ (258678663 / 500000000) := by
  have h := checkLog_sound (w := (517 / 2043)) (n := 12)
    (lo := (20694293 / 40000000)) (hi := (258678663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 763) = 1/(763 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-258678663 / 500000000) (-20694293 / 40000000) (Real.log (763 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (593413167 / 1000000000) ≤ -Real.log (1280 / 2317) ∧
    -Real.log (1280 / 2317) ≤ (37088323 / 62500000) := by
  have h := checkLog_sound (w := (1037 / 3597)) (n := 12)
    (lo := (593413167 / 1000000000)) (hi := (37088323 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 1280) = 1/(1280 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (593413167 / 1000000000) (37088323 / 62500000) (Real.log (2317 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2317 / 1280) = -Real.log (1280 / 2317) := by
    rw [show ((2317 / 1280) : ℝ) = ((1280 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (207694239 / 125000000) ≤ -Real.log (243 / 1280) ∧
    -Real.log (243 / 1280) ≤ (332310783 / 200000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 243) = 1/(243 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-332310783 / 200000000) (-207694239 / 125000000) (Real.log (243 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18640753 / 40000000) ≤ -Real.log (1000000 / 1593637) ∧
    -Real.log (1000000 / 1593637) ≤ (233009413 / 500000000) := by
  have h := checkLog_sound (w := (593637 / 2593637)) (n := 12)
    (lo := (18640753 / 40000000)) (hi := (233009413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593637 / 1000000) = 1/(1000000 / 1593637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18640753 / 40000000) (233009413 / 500000000) (Real.log (1593637 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1593637 / 1000000) = -Real.log (1000000 / 1593637) := by
    rw [show ((1593637 / 1000000) : ℝ) = ((1000000 / 1593637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (900508429 / 1000000000) ≤ -Real.log (406363 / 1000000) ∧
    -Real.log (406363 / 1000000) ≤ (900508431 / 1000000000) := by
  have h := checkLog_sound (w := (93637 / 906363)) (n := 12)
    (lo := (207361249 / 1000000000)) (hi := (165889 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406363) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 406363) = 1/(406363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-900508431 / 1000000000) (-900508429 / 1000000000) (Real.log (406363 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18689041 / 40000000) ≤ -Real.log (500000 / 797781) ∧
    -Real.log (500000 / 797781) ≤ (233613013 / 500000000) := by
  have h := checkLog_sound (w := (297781 / 1297781)) (n := 12)
    (lo := (18689041 / 40000000)) (hi := (233613013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797781 / 500000) = 1/(500000 / 797781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18689041 / 40000000) (233613013 / 500000000) (Real.log (797781 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (797781 / 500000) = -Real.log (500000 / 797781) := by
    rw [show ((797781 / 500000) : ℝ) = ((500000 / 797781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (905256829 / 1000000000) ≤ -Real.log (202219 / 500000) ∧
    -Real.log (202219 / 500000) ≤ (905256831 / 1000000000) := by
  have h := checkLog_sound (w := (47781 / 452219)) (n := 12)
    (lo := (212109649 / 1000000000)) (hi := (4242193 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 202219) = 1/(202219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-905256831 / 1000000000) (-905256829 / 1000000000) (Real.log (202219 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190854237 / 500000000) ≤ -Real.log (200000 / 292957) ∧
    -Real.log (200000 / 292957) ≤ (15268339 / 40000000) := by
  have h := checkLog_sound (w := (92957 / 492957)) (n := 12)
    (lo := (190854237 / 500000000)) (hi := (15268339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292957 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292957 / 200000) = 1/(200000 / 292957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190854237 / 500000000) (15268339 / 40000000) (Real.log (292957 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (292957 / 200000) = -Real.log (200000 / 292957) := by
    rw [show ((292957 / 200000) : ℝ) = ((200000 / 292957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (625086743 / 1000000000) ≤ -Real.log (107043 / 200000) ∧
    -Real.log (107043 / 200000) ≤ (78135843 / 125000000) := by
  have h := checkLog_sound (w := (92957 / 307043)) (n := 12)
    (lo := (625086743 / 1000000000)) (hi := (78135843 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 107043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 107043) = 1/(107043 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78135843 / 125000000) (-625086743 / 1000000000) (Real.log (107043 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19147783 / 50000000) ≤ -Real.log (1000000 / 1466613) ∧
    -Real.log (1000000 / 1466613) ≤ (382955661 / 1000000000) := by
  have h := checkLog_sound (w := (466613 / 2466613)) (n := 12)
    (lo := (19147783 / 50000000)) (hi := (382955661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1466613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1466613 / 1000000) = 1/(1000000 / 1466613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19147783 / 50000000) (382955661 / 1000000000) (Real.log (1466613 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1466613 / 1000000) = -Real.log (1000000 / 1466613) := by
    rw [show ((1466613 / 1000000) : ℝ) = ((1000000 / 1466613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (628508039 / 1000000000) ≤ -Real.log (533387 / 1000000) ∧
    -Real.log (533387 / 1000000) ≤ (15712701 / 25000000) := by
  have h := checkLog_sound (w := (466613 / 1533387)) (n := 12)
    (lo := (628508039 / 1000000000)) (hi := (15712701 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 533387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 533387) = 1/(533387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15712701 / 25000000) (-628508039 / 1000000000) (Real.log (533387 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (273305451 / 200000000) ≤ -Real.log (500000000000 / 1960853965543) ∧
    -Real.log (500000000000 / 1960853965543) ≤ (1366527257 / 1000000000) := by
  have h := checkLog_sound (w := (960853965543 / 2960853965543)) (n := 12)
    (lo := (26935203 / 40000000)) (hi := (168345019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960853965543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960853965543 / 1000000000000) = 1/(500000000000 / 1960853965543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (273305451 / 200000000) (1366527257 / 1000000000) (Real.log (1960853965543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1960853965543 / 500000000000) = -Real.log (500000000000 / 1960853965543) := by
    rw [show ((1960853965543 / 500000000000) : ℝ) = ((500000000000 / 1960853965543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (686241427 / 500000000) ≤ -Real.log (125000000000 / 493141717643) ∧
    -Real.log (125000000000 / 493141717643) ≤ (171560357 / 125000000) := by
  have h := checkLog_sound (w := (243141717643 / 743141717643)) (n := 12)
    (lo := (339667837 / 500000000)) (hi := (27173427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493141717643 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(493141717643 / 250000000000) = 1/(125000000000 / 493141717643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (686241427 / 500000000) (171560357 / 125000000) (Real.log (493141717643 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (493141717643 / 125000000000) = -Real.log (125000000000 / 493141717643) := by
    rw [show ((493141717643 / 125000000000) : ℝ) = ((125000000000 / 493141717643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1006795217 / 1000000000) ≤ -Real.log (15625000000 / 42762750717) ∧
    -Real.log (15625000000 / 42762750717) ≤ (1006795219 / 1000000000) := by
  have h := checkLog_sound (w := (11512750717 / 74012750717)) (n := 12)
    (lo := (313648037 / 1000000000)) (hi := (156824019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42762750717 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42762750717 / 31250000000) = 1/(15625000000 / 42762750717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1006795217 / 1000000000) (1006795219 / 1000000000) (Real.log (42762750717 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42762750717 / 15625000000) = -Real.log (15625000000 / 42762750717) := by
    rw [show ((42762750717 / 15625000000) : ℝ) = ((15625000000 / 42762750717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1011463699 / 1000000000) ≤ -Real.log (500000000000 / 1374811347109) ∧
    -Real.log (500000000000 / 1374811347109) ≤ (1011463701 / 1000000000) := by
  have h := checkLog_sound (w := (374811347109 / 2374811347109)) (n := 12)
    (lo := (318316519 / 1000000000)) (hi := (7957913 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374811347109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1374811347109 / 1000000000000) = 1/(500000000000 / 1374811347109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1011463699 / 1000000000) (1011463701 / 1000000000) (Real.log (1374811347109 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1374811347109 / 500000000000) = -Real.log (500000000000 / 1374811347109) := by
    rw [show ((1374811347109 / 500000000000) : ℝ) = ((500000000000 / 1374811347109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0092
