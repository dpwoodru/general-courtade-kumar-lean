import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0184
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

theorem reflection_log_1_neg : (619652001 / 1000000000) ≤ -Real.log (6400 / 11893) ∧
    -Real.log (6400 / 11893) ≤ (309826001 / 500000000) := by
  have h := checkLog_sound (w := (5493 / 18293)) (n := 12)
    (lo := (619652001 / 1000000000)) (hi := (309826001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11893 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11893 / 6400) = 1/(6400 / 11893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (619652001 / 1000000000) (309826001 / 500000000) (Real.log (11893 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11893 / 6400) = -Real.log (6400 / 11893) := by
    rw [show ((11893 / 6400) : ℝ) = ((6400 / 11893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (976955409 / 500000000) ≤ -Real.log (907 / 6400) ∧
    -Real.log (907 / 6400) ≤ (1953910821 / 1000000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 907) = 1/(907 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1953910821 / 1000000000) (-976955409 / 500000000) (Real.log (907 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (123610629 / 200000000) ≤ -Real.log (3200 / 5937) ∧
    -Real.log (3200 / 5937) ≤ (309026573 / 500000000) := by
  have h := checkLog_sound (w := (2737 / 9137)) (n := 12)
    (lo := (123610629 / 200000000)) (hi := (309026573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 3200) = 1/(3200 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (123610629 / 200000000) (309026573 / 500000000) (Real.log (5937 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5937 / 3200) = -Real.log (3200 / 5937) := by
    rw [show ((5937 / 3200) : ℝ) = ((3200 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1933179033 / 1000000000) ≤ -Real.log (463 / 3200) ∧
    -Real.log (463 / 3200) ≤ (483294759 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 463) = 1/(463 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-483294759 / 250000000) (-1933179033 / 1000000000) (Real.log (463 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16885117 / 31250000) ≤ -Real.log (3200 / 5493) ∧
    -Real.log (3200 / 5493) ≤ (108064749 / 200000000) := by
  have h := checkLog_sound (w := (2293 / 8693)) (n := 12)
    (lo := (16885117 / 31250000)) (hi := (108064749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5493 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5493 / 3200) = 1/(3200 / 5493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16885117 / 31250000) (108064749 / 200000000) (Real.log (5493 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5493 / 3200) = -Real.log (3200 / 5493) := by
    rw [show ((5493 / 3200) : ℝ) = ((3200 / 5493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (630381819 / 500000000) ≤ -Real.log (907 / 3200) ∧
    -Real.log (907 / 3200) ≤ (31519091 / 25000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 907) = 1/(907 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31519091 / 25000000) (-630381819 / 500000000) (Real.log (907 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1342147 / 2500000) ≤ -Real.log (1600 / 2737) ∧
    -Real.log (1600 / 2737) ≤ (536858801 / 1000000000) := by
  have h := checkLog_sound (w := (1137 / 4337)) (n := 12)
    (lo := (1342147 / 2500000)) (hi := (536858801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2737 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2737 / 1600) = 1/(1600 / 2737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1342147 / 2500000) (536858801 / 1000000000) (Real.log (2737 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2737 / 1600) = -Real.log (1600 / 2737) := by
    rw [show ((2737 / 1600) : ℝ) = ((1600 / 2737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1240031853 / 1000000000) ≤ -Real.log (463 / 1600) ∧
    -Real.log (463 / 1600) ≤ (248006371 / 200000000) := by
  have h := checkLog_sound (w := (337 / 1263)) (n := 12)
    (lo := (546884673 / 1000000000)) (hi := (273442337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 463) = 1/(463 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248006371 / 200000000) (-1240031853 / 1000000000) (Real.log (463 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (319448707 / 500000000) ≤ -Real.log (1000000 / 1894391) ∧
    -Real.log (1000000 / 1894391) ≤ (127779483 / 200000000) := by
  have h := checkLog_sound (w := (894391 / 2894391)) (n := 12)
    (lo := (319448707 / 500000000)) (hi := (127779483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1894391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1894391 / 1000000) = 1/(1000000 / 1894391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (319448707 / 500000000) (127779483 / 200000000) (Real.log (1894391 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1894391 / 1000000) = -Real.log (1000000 / 1894391) := by
    rw [show ((1894391 / 1000000) : ℝ) = ((1000000 / 1894391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1124005841 / 500000000) ≤ -Real.log (105609 / 1000000) ∧
    -Real.log (105609 / 1000000) ≤ (1124005843 / 500000000) := by
  have h := checkLog_sound (w := (19391 / 230609)) (n := 12)
    (lo := (84285071 / 500000000)) (hi := (168570143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105609) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 105609) = 1/(105609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1124005843 / 500000000) (-1124005841 / 500000000) (Real.log (105609 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127973119 / 200000000) ≤ -Real.log (500000 / 948113) ∧
    -Real.log (500000 / 948113) ≤ (159966399 / 250000000) := by
  have h := checkLog_sound (w := (448113 / 1448113)) (n := 12)
    (lo := (127973119 / 200000000)) (hi := (159966399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948113 / 500000) = 1/(500000 / 948113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127973119 / 200000000) (159966399 / 250000000) (Real.log (948113 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (948113 / 500000) = -Real.log (500000 / 948113) := by
    rw [show ((948113 / 500000) : ℝ) = ((500000 / 948113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2265539819 / 1000000000) ≤ -Real.log (51887 / 500000) ∧
    -Real.log (51887 / 500000) ≤ (2265539823 / 1000000000) := by
  have h := checkLog_sound (w := (10613 / 114387)) (n := 12)
    (lo := (186098279 / 1000000000)) (hi := (4652457 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 51887) = 1/(51887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2265539823 / 1000000000) (-2265539819 / 1000000000) (Real.log (51887 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (31795497 / 50000000) ≤ -Real.log (50000 / 94437) ∧
    -Real.log (50000 / 94437) ≤ (635909941 / 1000000000) := by
  have h := checkLog_sound (w := (44437 / 144437)) (n := 12)
    (lo := (31795497 / 50000000)) (hi := (635909941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94437 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94437 / 50000) = 1/(50000 / 94437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (31795497 / 50000000) (635909941 / 1000000000) (Real.log (94437 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (94437 / 50000) = -Real.log (50000 / 94437) := by
    rw [show ((94437 / 50000) : ℝ) = ((50000 / 94437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (68621421 / 31250000) ≤ -Real.log (5563 / 50000) ∧
    -Real.log (5563 / 50000) ≤ (548971369 / 250000000) := by
  have h := checkLog_sound (w := (687 / 11813)) (n := 12)
    (lo := (29110983 / 250000000)) (hi := (116443933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5563) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 5563) = 1/(5563 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-548971369 / 250000000) (-68621421 / 31250000) (Real.log (5563 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (159256219 / 250000000) ≤ -Real.log (1000000 / 1890847) ∧
    -Real.log (1000000 / 1890847) ≤ (637024877 / 1000000000) := by
  have h := checkLog_sound (w := (890847 / 2890847)) (n := 12)
    (lo := (159256219 / 250000000)) (hi := (637024877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1890847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1890847 / 1000000) = 1/(1000000 / 1890847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (159256219 / 250000000) (637024877 / 1000000000) (Real.log (1890847 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1890847 / 1000000) = -Real.log (1000000 / 1890847) := by
    rw [show ((1890847 / 1000000) : ℝ) = ((1000000 / 1890847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2215004709 / 1000000000) ≤ -Real.log (109153 / 1000000) ∧
    -Real.log (109153 / 1000000) ≤ (2215004713 / 1000000000) := by
  have h := checkLog_sound (w := (15847 / 234153)) (n := 12)
    (lo := (135563169 / 1000000000)) (hi := (13556317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 109153) = 1/(109153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2215004713 / 1000000000) (-2215004709 / 1000000000) (Real.log (109153 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (360863637 / 125000000) ≤ -Real.log (500000000000 / 8968889962029) ∧
    -Real.log (500000000000 / 8968889962029) ≤ (2886909101 / 1000000000) := by
  have h := checkLog_sound (w := (968889962029 / 16968889962029)) (n := 12)
    (lo := (14290047 / 125000000)) (hi := (114320377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8968889962029 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8968889962029 / 8000000000000) = 1/(500000000000 / 8968889962029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (360863637 / 125000000) (2886909101 / 1000000000) (Real.log (8968889962029 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8968889962029 / 500000000000) = -Real.log (500000000000 / 8968889962029) := by
    rw [show ((8968889962029 / 500000000000) : ℝ) = ((500000000000 / 8968889962029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1452702707 / 500000000) ≤ -Real.log (62500000000 / 1142040636383) ∧
    -Real.log (62500000000 / 1142040636383) ≤ (2905405419 / 1000000000) := by
  have h := checkLog_sound (w := (142040636383 / 2142040636383)) (n := 12)
    (lo := (66408347 / 500000000)) (hi := (26563339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142040636383 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1142040636383 / 1000000000000) = 1/(62500000000 / 1142040636383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1452702707 / 500000000) (2905405419 / 1000000000) (Real.log (1142040636383 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1142040636383 / 62500000000) = -Real.log (62500000000 / 1142040636383) := by
    rw [show ((1142040636383 / 62500000000) : ℝ) = ((62500000000 / 1142040636383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (707948853 / 250000000) ≤ -Real.log (250000000000 / 4243978069387) ∧
    -Real.log (250000000000 / 4243978069387) ≤ (2831795417 / 1000000000) := by
  have h := checkLog_sound (w := (243978069387 / 8243978069387)) (n := 12)
    (lo := (14801673 / 250000000)) (hi := (59206693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4243978069387 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4243978069387 / 4000000000000) = 1/(250000000000 / 4243978069387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (707948853 / 250000000) (2831795417 / 1000000000) (Real.log (4243978069387 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4243978069387 / 250000000000) = -Real.log (250000000000 / 4243978069387) := by
    rw [show ((4243978069387 / 250000000000) : ℝ) = ((250000000000 / 4243978069387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (570405917 / 200000000) ≤ -Real.log (100000000000 / 1732290454683) ∧
    -Real.log (100000000000 / 1732290454683) ≤ (285202959 / 100000000) := by
  have h := checkLog_sound (w := (132290454683 / 3332290454683)) (n := 12)
    (lo := (15888173 / 200000000)) (hi := (39720433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1732290454683 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1732290454683 / 1600000000000) = 1/(100000000000 / 1732290454683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (570405917 / 200000000) (285202959 / 100000000) (Real.log (1732290454683 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1732290454683 / 100000000000) = -Real.log (100000000000 / 1732290454683) := by
    rw [show ((1732290454683 / 100000000000) : ℝ) = ((100000000000 / 1732290454683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0184
