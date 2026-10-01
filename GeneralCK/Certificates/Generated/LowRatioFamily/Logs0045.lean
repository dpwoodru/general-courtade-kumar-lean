import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2880_neg : (8615151 / 50000000) ≤ -Real.log (500000000000 / 594018889331) ∧
    -Real.log (500000000000 / 594018889331) ≤ (172303021 / 1000000000) := by
  have h := checkLog_sound (w := (94018889331 / 1094018889331)) (n := 12)
    (lo := (8615151 / 50000000)) (hi := (172303021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594018889331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594018889331 / 500000000000) = 1/(500000000000 / 594018889331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2880 : Bounds (8615151 / 50000000) (172303021 / 1000000000) (Real.log (594018889331 / 500000000000)) := by
  have h := reflection_log_2880_neg
  have he : Real.log (594018889331 / 500000000000) = -Real.log (500000000000 / 594018889331) := by
    rw [show ((594018889331 / 500000000000) : ℝ) = ((500000000000 / 594018889331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2881_neg : (673389 / 1953125) ≤ -Real.log (500000000000 / 705836247437) ∧
    -Real.log (500000000000 / 705836247437) ≤ (344775169 / 1000000000) := by
  have h := checkLog_sound (w := (205836247437 / 1205836247437)) (n := 12)
    (lo := (673389 / 1953125)) (hi := (344775169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705836247437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705836247437 / 500000000000) = 1/(500000000000 / 705836247437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2881 : Bounds (673389 / 1953125) (344775169 / 1000000000) (Real.log (705836247437 / 500000000000)) := by
  have h := reflection_log_2881_neg
  have he : Real.log (705836247437 / 500000000000) = -Real.log (500000000000 / 705836247437) := by
    rw [show ((705836247437 / 500000000000) : ℝ) = ((500000000000 / 705836247437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2882_neg : (172490587 / 500000000) ≤ -Real.log (500000000000 / 705981669079) ∧
    -Real.log (500000000000 / 705981669079) ≤ (13799247 / 40000000) := by
  have h := checkLog_sound (w := (205981669079 / 1205981669079)) (n := 12)
    (lo := (172490587 / 500000000)) (hi := (13799247 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705981669079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705981669079 / 500000000000) = 1/(500000000000 / 705981669079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2882 : Bounds (172490587 / 500000000) (13799247 / 40000000) (Real.log (705981669079 / 500000000000)) := by
  have h := reflection_log_2882_neg
  have he : Real.log (705981669079 / 500000000000) = -Real.log (500000000000 / 705981669079) := by
    rw [show ((705981669079 / 500000000000) : ℝ) = ((500000000000 / 705981669079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2883_neg : (157772683 / 1000000000) ≤ -Real.log (10000 / 11709) ∧
    -Real.log (10000 / 11709) ≤ (39443171 / 250000000) := by
  have h := checkLog_sound (w := (1709 / 21709)) (n := 12)
    (lo := (157772683 / 1000000000)) (hi := (39443171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11709 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11709 / 10000) = 1/(10000 / 11709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2883 : Bounds (157772683 / 1000000000) (39443171 / 250000000) (Real.log (11709 / 10000)) := by
  have h := reflection_log_2883_neg
  have he : Real.log (11709 / 10000) = -Real.log (10000 / 11709) := by
    rw [show ((11709 / 10000) : ℝ) = ((10000 / 11709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2884_neg : (187414503 / 1000000000) ≤ -Real.log (8291 / 10000) ∧
    -Real.log (8291 / 10000) ≤ (23426813 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 18291)) (n := 12)
    (lo := (187414503 / 1000000000)) (hi := (23426813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8291) = 1/(8291 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2884 : Bounds (-23426813 / 125000000) (-187414503 / 1000000000) (Real.log (8291 / 10000)) := by
  have h := reflection_log_2884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2885_neg : (34177 / 200000000) ≤ -Real.log (10000000 / 10001709) ∧
    -Real.log (10000000 / 10001709) ≤ (85443 / 500000000) := by
  have h := checkLog_sound (w := (1709 / 20001709)) (n := 12)
    (lo := (34177 / 200000000)) (hi := (85443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001709 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001709 / 10000000) = 1/(10000000 / 10001709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2885 : Bounds (34177 / 200000000) (85443 / 500000000) (Real.log (10001709 / 10000000)) := by
  have h := reflection_log_2885_neg
  have he : Real.log (10001709 / 10000000) = -Real.log (10000000 / 10001709) := by
    rw [show ((10001709 / 10000000) : ℝ) = ((10000000 / 10001709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2886_neg : (85457 / 500000000) ≤ -Real.log (9998291 / 10000000) ∧
    -Real.log (9998291 / 10000000) ≤ (34183 / 200000000) := by
  have h := checkLog_sound (w := (1709 / 19998291)) (n := 12)
    (lo := (85457 / 500000000)) (hi := (34183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998291) = 1/(9998291 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2886 : Bounds (-34183 / 200000000) (-85457 / 500000000) (Real.log (9998291 / 10000000)) := by
  have h := reflection_log_2886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2887_neg : (8228757 / 100000000) ≤ -Real.log (125000 / 135721) ∧
    -Real.log (125000 / 135721) ≤ (82287571 / 1000000000) := by
  have h := checkLog_sound (w := (10721 / 260721)) (n := 12)
    (lo := (8228757 / 100000000)) (hi := (82287571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135721 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135721 / 125000) = 1/(125000 / 135721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2887 : Bounds (8228757 / 100000000) (82287571 / 1000000000) (Real.log (135721 / 125000)) := by
  have h := reflection_log_2887_neg
  have he : Real.log (135721 / 125000) = -Real.log (125000 / 135721) := by
    rw [show ((135721 / 125000) : ℝ) = ((125000 / 135721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2888_neg : (8967091 / 100000000) ≤ -Real.log (114279 / 125000) ∧
    -Real.log (114279 / 125000) ≤ (89670911 / 1000000000) := by
  have h := checkLog_sound (w := (10721 / 239279)) (n := 12)
    (lo := (8967091 / 100000000)) (hi := (89670911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114279) = 1/(114279 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2888 : Bounds (-89670911 / 1000000000) (-8967091 / 100000000) (Real.log (114279 / 125000)) := by
  have h := reflection_log_2888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2889_neg : (20622773 / 250000000) ≤ -Real.log (1000000 / 1085989) ∧
    -Real.log (1000000 / 1085989) ≤ (82491093 / 1000000000) := by
  have h := checkLog_sound (w := (85989 / 2085989)) (n := 12)
    (lo := (20622773 / 250000000)) (hi := (82491093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085989 / 1000000) = 1/(1000000 / 1085989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2889 : Bounds (20622773 / 250000000) (82491093 / 1000000000) (Real.log (1085989 / 1000000)) := by
  have h := reflection_log_2889_neg
  have he : Real.log (1085989 / 1000000) = -Real.log (1000000 / 1085989) := by
    rw [show ((1085989 / 1000000) : ℝ) = ((1000000 / 1085989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2890_neg : (2809771 / 31250000) ≤ -Real.log (914011 / 1000000) ∧
    -Real.log (914011 / 1000000) ≤ (89912673 / 1000000000) := by
  have h := checkLog_sound (w := (85989 / 1914011)) (n := 12)
    (lo := (2809771 / 31250000)) (hi := (89912673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914011) = 1/(914011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2890 : Bounds (-89912673 / 1000000000) (-2809771 / 31250000) (Real.log (914011 / 1000000)) := by
  have h := reflection_log_2890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2891_neg : (371079 / 50000000) ≤ -Real.log (992605891879 / 1000000000000) ∧
    -Real.log (992605891879 / 1000000000000) ≤ (7421581 / 1000000000) := by
  have h := checkLog_sound (w := (7394108121 / 1992605891879)) (n := 12)
    (lo := (371079 / 50000000)) (hi := (7421581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992605891879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992605891879) = 1/(992605891879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2891 : Bounds (-7421581 / 1000000000) (-371079 / 50000000) (Real.log (992605891879 / 1000000000000)) := by
  have h := reflection_log_2891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2892_neg : (7383339 / 1000000000) ≤ -Real.log (15510060159 / 15625000000) ∧
    -Real.log (15510060159 / 15625000000) ≤ (369167 / 50000000) := by
  have h := checkLog_sound (w := (114939841 / 31135060159)) (n := 12)
    (lo := (7383339 / 1000000000)) (hi := (369167 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15510060159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15510060159) = 1/(15510060159 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2892 : Bounds (-369167 / 50000000) (-7383339 / 1000000000) (Real.log (15510060159 / 15625000000)) := by
  have h := reflection_log_2892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2893_neg : (171958481 / 1000000000) ≤ -Real.log (500000000000 / 593814261587) ∧
    -Real.log (500000000000 / 593814261587) ≤ (85979241 / 500000000) := by
  have h := checkLog_sound (w := (93814261587 / 1093814261587)) (n := 12)
    (lo := (171958481 / 1000000000)) (hi := (85979241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593814261587 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593814261587 / 500000000000) = 1/(500000000000 / 593814261587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2893 : Bounds (171958481 / 1000000000) (85979241 / 500000000) (Real.log (593814261587 / 500000000000)) := by
  have h := reflection_log_2893_neg
  have he : Real.log (593814261587 / 500000000000) = -Real.log (500000000000 / 593814261587) := by
    rw [show ((593814261587 / 500000000000) : ℝ) = ((500000000000 / 593814261587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2894_neg : (34480753 / 200000000) ≤ -Real.log (500000000000 / 594078736471) ∧
    -Real.log (500000000000 / 594078736471) ≤ (86201883 / 500000000) := by
  have h := checkLog_sound (w := (94078736471 / 1094078736471)) (n := 12)
    (lo := (34480753 / 200000000)) (hi := (86201883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594078736471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594078736471 / 500000000000) = 1/(500000000000 / 594078736471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2894 : Bounds (34480753 / 200000000) (86201883 / 500000000) (Real.log (594078736471 / 500000000000)) := by
  have h := reflection_log_2894_neg
  have he : Real.log (594078736471 / 500000000000) = -Real.log (500000000000 / 594078736471) := by
    rw [show ((594078736471 / 500000000000) : ℝ) = ((500000000000 / 594078736471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2895_neg : (172490587 / 500000000) ≤ -Real.log (250000000000 / 352990834539) ∧
    -Real.log (250000000000 / 352990834539) ≤ (13799247 / 40000000) := by
  have h := checkLog_sound (w := (102990834539 / 602990834539)) (n := 12)
    (lo := (172490587 / 500000000)) (hi := (13799247 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352990834539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352990834539 / 250000000000) = 1/(250000000000 / 352990834539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2895 : Bounds (172490587 / 500000000) (13799247 / 40000000) (Real.log (352990834539 / 250000000000)) := by
  have h := reflection_log_2895_neg
  have he : Real.log (352990834539 / 250000000000) = -Real.log (250000000000 / 352990834539) := by
    rw [show ((352990834539 / 250000000000) : ℝ) = ((250000000000 / 352990834539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2896_neg : (345187187 / 1000000000) ≤ -Real.log (2500000000 / 3530635629) ∧
    -Real.log (2500000000 / 3530635629) ≤ (86296797 / 250000000) := by
  have h := checkLog_sound (w := (1030635629 / 6030635629)) (n := 12)
    (lo := (345187187 / 1000000000)) (hi := (86296797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3530635629 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3530635629 / 2500000000) = 1/(2500000000 / 3530635629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2896 : Bounds (345187187 / 1000000000) (86296797 / 250000000) (Real.log (3530635629 / 2500000000)) := by
  have h := reflection_log_2896_neg
  have he : Real.log (3530635629 / 2500000000) = -Real.log (2500000000 / 3530635629) := by
    rw [show ((3530635629 / 2500000000) : ℝ) = ((2500000000 / 3530635629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2897_neg : (39464521 / 250000000) ≤ -Real.log (1000 / 1171) ∧
    -Real.log (1000 / 1171) ≤ (31571617 / 200000000) := by
  have h := checkLog_sound (w := (171 / 2171)) (n := 12)
    (lo := (39464521 / 250000000)) (hi := (31571617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171 / 1000) = 1/(1000 / 1171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2897 : Bounds (39464521 / 250000000) (31571617 / 200000000) (Real.log (1171 / 1000)) := by
  have h := reflection_log_2897_neg
  have he : Real.log (1171 / 1000) = -Real.log (1000 / 1171) := by
    rw [show ((1171 / 1000) : ℝ) = ((1000 / 1171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2898_neg : (187535123 / 1000000000) ≤ -Real.log (829 / 1000) ∧
    -Real.log (829 / 1000) ≤ (46883781 / 250000000) := by
  have h := checkLog_sound (w := (171 / 1829)) (n := 12)
    (lo := (187535123 / 1000000000)) (hi := (46883781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 829) = 1/(829 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2898 : Bounds (-46883781 / 250000000) (-187535123 / 1000000000) (Real.log (829 / 1000)) := by
  have h := reflection_log_2898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2899_neg : (34197 / 200000000) ≤ -Real.log (1000000 / 1000171) ∧
    -Real.log (1000000 / 1000171) ≤ (85493 / 500000000) := by
  have h := checkLog_sound (w := (171 / 2000171)) (n := 12)
    (lo := (34197 / 200000000)) (hi := (85493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000171 / 1000000) = 1/(1000000 / 1000171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2899 : Bounds (34197 / 200000000) (85493 / 500000000) (Real.log (1000171 / 1000000)) := by
  have h := reflection_log_2899_neg
  have he : Real.log (1000171 / 1000000) = -Real.log (1000000 / 1000171) := by
    rw [show ((1000171 / 1000000) : ℝ) = ((1000000 / 1000171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2900_neg : (85507 / 500000000) ≤ -Real.log (999829 / 1000000) ∧
    -Real.log (999829 / 1000000) ≤ (34203 / 200000000) := by
  have h := checkLog_sound (w := (171 / 1999829)) (n := 12)
    (lo := (85507 / 500000000)) (hi := (34203 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999829) = 1/(999829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2900 : Bounds (-34203 / 200000000) (-85507 / 500000000) (Real.log (999829 / 1000000)) := by
  have h := reflection_log_2900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2901_neg : (82333619 / 1000000000) ≤ -Real.log (500000 / 542909) ∧
    -Real.log (500000 / 542909) ≤ (4116681 / 50000000) := by
  have h := checkLog_sound (w := (42909 / 1042909)) (n := 12)
    (lo := (82333619 / 1000000000)) (hi := (4116681 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542909 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542909 / 500000) = 1/(500000 / 542909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2901 : Bounds (82333619 / 1000000000) (4116681 / 50000000) (Real.log (542909 / 500000)) := by
  have h := reflection_log_2901_neg
  have he : Real.log (542909 / 500000) = -Real.log (500000 / 542909) := by
    rw [show ((542909 / 500000) : ℝ) = ((500000 / 542909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2902_neg : (44862801 / 500000000) ≤ -Real.log (457091 / 500000) ∧
    -Real.log (457091 / 500000) ≤ (89725603 / 1000000000) := by
  have h := checkLog_sound (w := (42909 / 957091)) (n := 12)
    (lo := (44862801 / 500000000)) (hi := (89725603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457091) = 1/(457091 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2902 : Bounds (-89725603 / 1000000000) (-44862801 / 500000000) (Real.log (457091 / 500000)) := by
  have h := reflection_log_2902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2903_neg : (82538053 / 1000000000) ≤ -Real.log (25000 / 27151) ∧
    -Real.log (25000 / 27151) ≤ (41269027 / 500000000) := by
  have h := checkLog_sound (w := (2151 / 52151)) (n := 12)
    (lo := (82538053 / 1000000000)) (hi := (41269027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27151 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27151 / 25000) = 1/(25000 / 27151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2903 : Bounds (82538053 / 1000000000) (41269027 / 500000000) (Real.log (27151 / 25000)) := by
  have h := reflection_log_2903_neg
  have he : Real.log (27151 / 25000) = -Real.log (25000 / 27151) := by
    rw [show ((27151 / 25000) : ℝ) = ((25000 / 27151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2904_neg : (11246059 / 125000000) ≤ -Real.log (22849 / 25000) ∧
    -Real.log (22849 / 25000) ≤ (89968473 / 1000000000) := by
  have h := checkLog_sound (w := (2151 / 47849)) (n := 12)
    (lo := (11246059 / 125000000)) (hi := (89968473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22849) = 1/(22849 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2904 : Bounds (-89968473 / 1000000000) (-11246059 / 125000000) (Real.log (22849 / 25000)) := by
  have h := reflection_log_2904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2905_neg : (3715209 / 500000000) ≤ -Real.log (620373199 / 625000000) ∧
    -Real.log (620373199 / 625000000) ≤ (7430419 / 1000000000) := by
  have h := checkLog_sound (w := (4626801 / 1245373199)) (n := 12)
    (lo := (3715209 / 500000000)) (hi := (7430419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620373199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620373199) = 1/(620373199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2905 : Bounds (-7430419 / 1000000000) (-3715209 / 500000000) (Real.log (620373199 / 625000000)) := by
  have h := reflection_log_2905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2906_neg : (3695991 / 500000000) ≤ -Real.log (248158817719 / 250000000000) ∧
    -Real.log (248158817719 / 250000000000) ≤ (7391983 / 1000000000) := by
  have h := checkLog_sound (w := (1841182281 / 498158817719)) (n := 12)
    (lo := (3695991 / 500000000)) (hi := (7391983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248158817719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248158817719) = 1/(248158817719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2906 : Bounds (-7391983 / 1000000000) (-3695991 / 500000000) (Real.log (248158817719 / 250000000000)) := by
  have h := reflection_log_2906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2907_neg : (86029611 / 500000000) ≤ -Real.log (500000000000 / 593874086341) ∧
    -Real.log (500000000000 / 593874086341) ≤ (172059223 / 1000000000) := by
  have h := checkLog_sound (w := (93874086341 / 1093874086341)) (n := 12)
    (lo := (86029611 / 500000000)) (hi := (172059223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593874086341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593874086341 / 500000000000) = 1/(500000000000 / 593874086341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2907 : Bounds (86029611 / 500000000) (172059223 / 1000000000) (Real.log (593874086341 / 500000000000)) := by
  have h := reflection_log_2907_neg
  have he : Real.log (593874086341 / 500000000000) = -Real.log (500000000000 / 593874086341) := by
    rw [show ((593874086341 / 500000000000) : ℝ) = ((500000000000 / 593874086341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2908_neg : (6900261 / 40000000) ≤ -Real.log (5000000000 / 5941397873) ∧
    -Real.log (5000000000 / 5941397873) ≤ (86253263 / 500000000) := by
  have h := checkLog_sound (w := (941397873 / 10941397873)) (n := 12)
    (lo := (6900261 / 40000000)) (hi := (86253263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5941397873 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5941397873 / 5000000000) = 1/(5000000000 / 5941397873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2908 : Bounds (6900261 / 40000000) (86253263 / 500000000) (Real.log (5941397873 / 5000000000)) := by
  have h := reflection_log_2908_neg
  have he : Real.log (5941397873 / 5000000000) = -Real.log (5000000000 / 5941397873) := by
    rw [show ((5941397873 / 5000000000) : ℝ) = ((5000000000 / 5941397873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2909_neg : (345187187 / 1000000000) ≤ -Real.log (500000000000 / 706127125799) ∧
    -Real.log (500000000000 / 706127125799) ≤ (86296797 / 250000000) := by
  have h := checkLog_sound (w := (206127125799 / 1206127125799)) (n := 12)
    (lo := (345187187 / 1000000000)) (hi := (86296797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706127125799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706127125799 / 500000000000) = 1/(500000000000 / 706127125799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2909 : Bounds (345187187 / 1000000000) (86296797 / 250000000) (Real.log (706127125799 / 500000000000)) := by
  have h := reflection_log_2909_neg
  have he : Real.log (706127125799 / 500000000000) = -Real.log (500000000000 / 706127125799) := by
    rw [show ((706127125799 / 500000000000) : ℝ) = ((500000000000 / 706127125799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2910_neg : (43174151 / 125000000) ≤ -Real.log (125000000000 / 176568154403) ∧
    -Real.log (125000000000 / 176568154403) ≤ (345393209 / 1000000000) := by
  have h := checkLog_sound (w := (51568154403 / 301568154403)) (n := 12)
    (lo := (43174151 / 125000000)) (hi := (345393209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176568154403 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176568154403 / 125000000000) = 1/(125000000000 / 176568154403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2910 : Bounds (43174151 / 125000000) (345393209 / 1000000000) (Real.log (176568154403 / 125000000000)) := by
  have h := reflection_log_2910_neg
  have he : Real.log (176568154403 / 125000000000) = -Real.log (125000000000 / 176568154403) := by
    rw [show ((176568154403 / 125000000000) : ℝ) = ((125000000000 / 176568154403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2911_neg : (78971739 / 500000000) ≤ -Real.log (10000 / 11711) ∧
    -Real.log (10000 / 11711) ≤ (157943479 / 1000000000) := by
  have h := checkLog_sound (w := (1711 / 21711)) (n := 12)
    (lo := (78971739 / 500000000)) (hi := (157943479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11711 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11711 / 10000) = 1/(10000 / 11711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2911 : Bounds (78971739 / 500000000) (157943479 / 1000000000) (Real.log (11711 / 10000)) := by
  have h := reflection_log_2911_neg
  have he : Real.log (11711 / 10000) = -Real.log (10000 / 11711) := by
    rw [show ((11711 / 10000) : ℝ) = ((10000 / 11711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2912_neg : (93827879 / 500000000) ≤ -Real.log (8289 / 10000) ∧
    -Real.log (8289 / 10000) ≤ (187655759 / 1000000000) := by
  have h := checkLog_sound (w := (1711 / 18289)) (n := 12)
    (lo := (93827879 / 500000000)) (hi := (187655759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8289) = 1/(8289 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2912 : Bounds (-187655759 / 1000000000) (-93827879 / 500000000) (Real.log (8289 / 10000)) := by
  have h := reflection_log_2912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2913_neg : (34217 / 200000000) ≤ -Real.log (10000000 / 10001711) ∧
    -Real.log (10000000 / 10001711) ≤ (85543 / 500000000) := by
  have h := checkLog_sound (w := (1711 / 20001711)) (n := 12)
    (lo := (34217 / 200000000)) (hi := (85543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001711 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001711 / 10000000) = 1/(10000000 / 10001711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2913 : Bounds (34217 / 200000000) (85543 / 500000000) (Real.log (10001711 / 10000000)) := by
  have h := reflection_log_2913_neg
  have he : Real.log (10001711 / 10000000) = -Real.log (10000000 / 10001711) := by
    rw [show ((10001711 / 10000000) : ℝ) = ((10000000 / 10001711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2914_neg : (85557 / 500000000) ≤ -Real.log (9998289 / 10000000) ∧
    -Real.log (9998289 / 10000000) ≤ (34223 / 200000000) := by
  have h := checkLog_sound (w := (1711 / 19998289)) (n := 12)
    (lo := (85557 / 500000000)) (hi := (34223 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998289) = 1/(9998289 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2914 : Bounds (-34223 / 200000000) (-85557 / 500000000) (Real.log (9998289 / 10000000)) := by
  have h := reflection_log_2914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2915_neg : (20595147 / 250000000) ≤ -Real.log (1000000 / 1085869) ∧
    -Real.log (1000000 / 1085869) ≤ (82380589 / 1000000000) := by
  have h := checkLog_sound (w := (85869 / 2085869)) (n := 12)
    (lo := (20595147 / 250000000)) (hi := (82380589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085869 / 1000000) = 1/(1000000 / 1085869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2915 : Bounds (20595147 / 250000000) (82380589 / 1000000000) (Real.log (1085869 / 1000000)) := by
  have h := reflection_log_2915_neg
  have he : Real.log (1085869 / 1000000) = -Real.log (1000000 / 1085869) := by
    rw [show ((1085869 / 1000000) : ℝ) = ((1000000 / 1085869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2916_neg : (89781391 / 1000000000) ≤ -Real.log (914131 / 1000000) ∧
    -Real.log (914131 / 1000000) ≤ (5611337 / 62500000) := by
  have h := checkLog_sound (w := (85869 / 1914131)) (n := 12)
    (lo := (89781391 / 1000000000)) (hi := (5611337 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914131) = 1/(914131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2916 : Bounds (-5611337 / 62500000) (-89781391 / 1000000000) (Real.log (914131 / 1000000)) := by
  have h := reflection_log_2916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2917_neg : (82585011 / 1000000000) ≤ -Real.log (1000000 / 1086091) ∧
    -Real.log (1000000 / 1086091) ≤ (20646253 / 250000000) := by
  have h := checkLog_sound (w := (86091 / 2086091)) (n := 12)
    (lo := (82585011 / 1000000000)) (hi := (20646253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086091 / 1000000) = 1/(1000000 / 1086091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2917 : Bounds (82585011 / 1000000000) (20646253 / 250000000) (Real.log (1086091 / 1000000)) := by
  have h := reflection_log_2917_neg
  have he : Real.log (1086091 / 1000000) = -Real.log (1000000 / 1086091) := by
    rw [show ((1086091 / 1000000) : ℝ) = ((1000000 / 1086091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2918_neg : (45012137 / 500000000) ≤ -Real.log (913909 / 1000000) ∧
    -Real.log (913909 / 1000000) ≤ (3600971 / 40000000) := by
  have h := checkLog_sound (w := (86091 / 1913909)) (n := 12)
    (lo := (45012137 / 500000000)) (hi := (3600971 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913909) = 1/(913909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2918 : Bounds (-3600971 / 40000000) (-45012137 / 500000000) (Real.log (913909 / 1000000)) := by
  have h := reflection_log_2918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2919_neg : (7439263 / 1000000000) ≤ -Real.log (992588339719 / 1000000000000) ∧
    -Real.log (992588339719 / 1000000000000) ≤ (232477 / 31250000) := by
  have h := checkLog_sound (w := (7411660281 / 1992588339719)) (n := 12)
    (lo := (7439263 / 1000000000)) (hi := (232477 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992588339719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992588339719) = 1/(992588339719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2919 : Bounds (-232477 / 31250000) (-7439263 / 1000000000) (Real.log (992588339719 / 1000000000000)) := by
  have h := reflection_log_2919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2920_neg : (7400803 / 1000000000) ≤ -Real.log (992626514839 / 1000000000000) ∧
    -Real.log (992626514839 / 1000000000000) ≤ (1850201 / 250000000) := by
  have h := checkLog_sound (w := (7373485161 / 1992626514839)) (n := 12)
    (lo := (7400803 / 1000000000)) (hi := (1850201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992626514839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992626514839) = 1/(992626514839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2920 : Bounds (-1850201 / 250000000) (-7400803 / 1000000000) (Real.log (992626514839 / 1000000000000)) := by
  have h := reflection_log_2920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2921_neg : (172161979 / 1000000000) ≤ -Real.log (125000000000 / 148483778583) ∧
    -Real.log (125000000000 / 148483778583) ≤ (8608099 / 50000000) := by
  have h := checkLog_sound (w := (23483778583 / 273483778583)) (n := 12)
    (lo := (172161979 / 1000000000)) (hi := (8608099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148483778583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148483778583 / 125000000000) = 1/(125000000000 / 148483778583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2921 : Bounds (172161979 / 1000000000) (8608099 / 50000000) (Real.log (148483778583 / 125000000000)) := by
  have h := reflection_log_2921_neg
  have he : Real.log (148483778583 / 125000000000) = -Real.log (125000000000 / 148483778583) := by
    rw [show ((148483778583 / 125000000000) : ℝ) = ((125000000000 / 148483778583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2922_neg : (86304643 / 500000000) ≤ -Real.log (250000000000 / 297100422471) ∧
    -Real.log (250000000000 / 297100422471) ≤ (172609287 / 1000000000) := by
  have h := checkLog_sound (w := (47100422471 / 547100422471)) (n := 12)
    (lo := (86304643 / 500000000)) (hi := (172609287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297100422471 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297100422471 / 250000000000) = 1/(250000000000 / 297100422471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2922 : Bounds (86304643 / 500000000) (172609287 / 1000000000) (Real.log (297100422471 / 250000000000)) := by
  have h := reflection_log_2922_neg
  have he : Real.log (297100422471 / 250000000000) = -Real.log (250000000000 / 297100422471) := by
    rw [show ((297100422471 / 250000000000) : ℝ) = ((250000000000 / 297100422471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2923_neg : (43174151 / 125000000) ≤ -Real.log (500000000000 / 706272617611) ∧
    -Real.log (500000000000 / 706272617611) ≤ (345393209 / 1000000000) := by
  have h := checkLog_sound (w := (206272617611 / 1206272617611)) (n := 12)
    (lo := (43174151 / 125000000)) (hi := (345393209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706272617611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706272617611 / 500000000000) = 1/(500000000000 / 706272617611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2923 : Bounds (43174151 / 125000000) (345393209 / 1000000000) (Real.log (706272617611 / 500000000000)) := by
  have h := reflection_log_2923_neg
  have he : Real.log (706272617611 / 500000000000) = -Real.log (500000000000 / 706272617611) := by
    rw [show ((706272617611 / 500000000000) : ℝ) = ((500000000000 / 706272617611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2924_neg : (86399809 / 250000000) ≤ -Real.log (500000000000 / 706418144529) ∧
    -Real.log (500000000000 / 706418144529) ≤ (345599237 / 1000000000) := by
  have h := checkLog_sound (w := (206418144529 / 1206418144529)) (n := 12)
    (lo := (86399809 / 250000000)) (hi := (345599237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706418144529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706418144529 / 500000000000) = 1/(500000000000 / 706418144529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2924 : Bounds (86399809 / 250000000) (345599237 / 1000000000) (Real.log (706418144529 / 500000000000)) := by
  have h := reflection_log_2924_neg
  have he : Real.log (706418144529 / 500000000000) = -Real.log (500000000000 / 706418144529) := by
    rw [show ((706418144529 / 500000000000) : ℝ) = ((500000000000 / 706418144529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2925_neg : (2469201 / 15625000) ≤ -Real.log (625 / 732) ∧
    -Real.log (625 / 732) ≤ (31605773 / 200000000) := by
  have h := checkLog_sound (w := (107 / 1357)) (n := 12)
    (lo := (2469201 / 15625000)) (hi := (31605773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732 / 625) = 1/(625 / 732) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2925 : Bounds (2469201 / 15625000) (31605773 / 200000000) (Real.log (732 / 625)) := by
  have h := reflection_log_2925_neg
  have he : Real.log (732 / 625) = -Real.log (625 / 732) := by
    rw [show ((732 / 625) : ℝ) = ((625 / 732) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2926_neg : (187776407 / 1000000000) ≤ -Real.log (518 / 625) ∧
    -Real.log (518 / 625) ≤ (23472051 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1143)) (n := 12)
    (lo := (187776407 / 1000000000)) (hi := (23472051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 518) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 518) = 1/(518 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2926 : Bounds (-23472051 / 125000000) (-187776407 / 1000000000) (Real.log (518 / 625)) := by
  have h := reflection_log_2926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2927_neg : (34237 / 200000000) ≤ -Real.log (625000 / 625107) ∧
    -Real.log (625000 / 625107) ≤ (85593 / 500000000) := by
  have h := checkLog_sound (w := (107 / 1250107)) (n := 12)
    (lo := (34237 / 200000000)) (hi := (85593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625107 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625107 / 625000) = 1/(625000 / 625107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2927 : Bounds (34237 / 200000000) (85593 / 500000000) (Real.log (625107 / 625000)) := by
  have h := reflection_log_2927_neg
  have he : Real.log (625107 / 625000) = -Real.log (625000 / 625107) := by
    rw [show ((625107 / 625000) : ℝ) = ((625000 / 625107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2928_neg : (85607 / 500000000) ≤ -Real.log (624893 / 625000) ∧
    -Real.log (624893 / 625000) ≤ (34243 / 200000000) := by
  have h := checkLog_sound (w := (107 / 1249893)) (n := 12)
    (lo := (85607 / 500000000)) (hi := (34243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624893) = 1/(624893 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2928 : Bounds (-34243 / 200000000) (-85607 / 500000000) (Real.log (624893 / 625000)) := by
  have h := reflection_log_2928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2929_neg : (82427553 / 1000000000) ≤ -Real.log (6250 / 6787) ∧
    -Real.log (6250 / 6787) ≤ (41213777 / 500000000) := by
  have h := checkLog_sound (w := (537 / 13037)) (n := 12)
    (lo := (82427553 / 1000000000)) (hi := (41213777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 6250) = 1/(6250 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2929 : Bounds (82427553 / 1000000000) (41213777 / 500000000) (Real.log (6787 / 6250)) := by
  have h := reflection_log_2929_neg
  have he : Real.log (6787 / 6250) = -Real.log (6250 / 6787) := by
    rw [show ((6787 / 6250) : ℝ) = ((6250 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2930_neg : (701853 / 7812500) ≤ -Real.log (5713 / 6250) ∧
    -Real.log (5713 / 6250) ≤ (17967437 / 200000000) := by
  have h := checkLog_sound (w := (537 / 11963)) (n := 12)
    (lo := (701853 / 7812500)) (hi := (17967437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5713) = 1/(5713 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2930 : Bounds (-17967437 / 200000000) (-701853 / 7812500) (Real.log (5713 / 6250)) := by
  have h := reflection_log_2930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2931_neg : (2582249 / 31250000) ≤ -Real.log (500000 / 543071) ∧
    -Real.log (500000 / 543071) ≤ (82631969 / 1000000000) := by
  have h := checkLog_sound (w := (43071 / 1043071)) (n := 12)
    (lo := (2582249 / 31250000)) (hi := (82631969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543071 / 500000) = 1/(500000 / 543071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2931 : Bounds (2582249 / 31250000) (82631969 / 1000000000) (Real.log (543071 / 500000)) := by
  have h := reflection_log_2931_neg
  have he : Real.log (543071 / 500000) = -Real.log (500000 / 543071) := by
    rw [show ((543071 / 500000) : ℝ) = ((500000 / 543071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2932_neg : (1126001 / 12500000) ≤ -Real.log (456929 / 500000) ∧
    -Real.log (456929 / 500000) ≤ (90080081 / 1000000000) := by
  have h := checkLog_sound (w := (43071 / 956929)) (n := 12)
    (lo := (1126001 / 12500000)) (hi := (90080081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456929) = 1/(456929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2932 : Bounds (-90080081 / 1000000000) (-1126001 / 12500000) (Real.log (456929 / 500000)) := by
  have h := reflection_log_2932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2933_neg : (465507 / 62500000) ≤ -Real.log (248144888959 / 250000000000) ∧
    -Real.log (248144888959 / 250000000000) ≤ (7448113 / 1000000000) := by
  have h := checkLog_sound (w := (1855111041 / 498144888959)) (n := 12)
    (lo := (465507 / 62500000)) (hi := (7448113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248144888959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248144888959) = 1/(248144888959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2933 : Bounds (-7448113 / 1000000000) (-465507 / 62500000) (Real.log (248144888959 / 250000000000)) := by
  have h := reflection_log_2933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2934_neg : (740963 / 100000000) ≤ -Real.log (38774131 / 39062500) ∧
    -Real.log (38774131 / 39062500) ≤ (7409631 / 1000000000) := by
  have h := checkLog_sound (w := (288369 / 77836631)) (n := 12)
    (lo := (740963 / 100000000)) (hi := (7409631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38774131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38774131) = 1/(38774131 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2934 : Bounds (-7409631 / 1000000000) (-740963 / 100000000) (Real.log (38774131 / 39062500)) := by
  have h := reflection_log_2934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2935_neg : (172264737 / 1000000000) ≤ -Real.log (500000000000 / 593996149133) ∧
    -Real.log (500000000000 / 593996149133) ≤ (86132369 / 500000000) := by
  have h := checkLog_sound (w := (93996149133 / 1093996149133)) (n := 12)
    (lo := (172264737 / 1000000000)) (hi := (86132369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593996149133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593996149133 / 500000000000) = 1/(500000000000 / 593996149133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2935 : Bounds (172264737 / 1000000000) (86132369 / 500000000) (Real.log (593996149133 / 500000000000)) := by
  have h := reflection_log_2935_neg
  have he : Real.log (593996149133 / 500000000000) = -Real.log (500000000000 / 593996149133) := by
    rw [show ((593996149133 / 500000000000) : ℝ) = ((500000000000 / 593996149133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2936_neg : (10794503 / 62500000) ≤ -Real.log (2500000000 / 2971309547) ∧
    -Real.log (2500000000 / 2971309547) ≤ (172712049 / 1000000000) := by
  have h := checkLog_sound (w := (471309547 / 5471309547)) (n := 12)
    (lo := (10794503 / 62500000)) (hi := (172712049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2971309547 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2971309547 / 2500000000) = 1/(2500000000 / 2971309547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2936 : Bounds (10794503 / 62500000) (172712049 / 1000000000) (Real.log (2971309547 / 2500000000)) := by
  have h := reflection_log_2936_neg
  have he : Real.log (2971309547 / 2500000000) = -Real.log (2500000000 / 2971309547) := by
    rw [show ((2971309547 / 2500000000) : ℝ) = ((2500000000 / 2971309547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2937_neg : (86399809 / 250000000) ≤ -Real.log (31250000000 / 44151134033) ∧
    -Real.log (31250000000 / 44151134033) ≤ (345599237 / 1000000000) := by
  have h := checkLog_sound (w := (12901134033 / 75401134033)) (n := 12)
    (lo := (86399809 / 250000000)) (hi := (345599237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44151134033 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44151134033 / 31250000000) = 1/(31250000000 / 44151134033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2937 : Bounds (86399809 / 250000000) (345599237 / 1000000000) (Real.log (44151134033 / 31250000000)) := by
  have h := reflection_log_2937_neg
  have he : Real.log (44151134033 / 31250000000) = -Real.log (31250000000 / 44151134033) := by
    rw [show ((44151134033 / 31250000000) : ℝ) = ((31250000000 / 44151134033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2938_neg : (345805271 / 1000000000) ≤ -Real.log (125000000000 / 176640926641) ∧
    -Real.log (125000000000 / 176640926641) ≤ (43225659 / 125000000) := by
  have h := checkLog_sound (w := (51640926641 / 301640926641)) (n := 12)
    (lo := (345805271 / 1000000000)) (hi := (43225659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176640926641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176640926641 / 125000000000) = 1/(125000000000 / 176640926641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2938 : Bounds (345805271 / 1000000000) (43225659 / 125000000) (Real.log (176640926641 / 125000000000)) := by
  have h := reflection_log_2938_neg
  have he : Real.log (176640926641 / 125000000000) = -Real.log (125000000000 / 176640926641) := by
    rw [show ((176640926641 / 125000000000) : ℝ) = ((125000000000 / 176640926641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2939_neg : (158114243 / 1000000000) ≤ -Real.log (10000 / 11713) ∧
    -Real.log (10000 / 11713) ≤ (39528561 / 250000000) := by
  have h := checkLog_sound (w := (1713 / 21713)) (n := 12)
    (lo := (158114243 / 1000000000)) (hi := (39528561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11713 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11713 / 10000) = 1/(10000 / 11713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2939 : Bounds (158114243 / 1000000000) (39528561 / 250000000) (Real.log (11713 / 10000)) := by
  have h := reflection_log_2939_neg
  have he : Real.log (11713 / 10000) = -Real.log (10000 / 11713) := by
    rw [show ((11713 / 10000) : ℝ) = ((10000 / 11713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2940_neg : (187897071 / 1000000000) ≤ -Real.log (8287 / 10000) ∧
    -Real.log (8287 / 10000) ≤ (11743567 / 62500000) := by
  have h := checkLog_sound (w := (1713 / 18287)) (n := 12)
    (lo := (187897071 / 1000000000)) (hi := (11743567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8287) = 1/(8287 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2940 : Bounds (-11743567 / 62500000) (-187897071 / 1000000000) (Real.log (8287 / 10000)) := by
  have h := reflection_log_2940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2941_neg : (34257 / 200000000) ≤ -Real.log (10000000 / 10001713) ∧
    -Real.log (10000000 / 10001713) ≤ (85643 / 500000000) := by
  have h := checkLog_sound (w := (1713 / 20001713)) (n := 12)
    (lo := (34257 / 200000000)) (hi := (85643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001713 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001713 / 10000000) = 1/(10000000 / 10001713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2941 : Bounds (34257 / 200000000) (85643 / 500000000) (Real.log (10001713 / 10000000)) := by
  have h := reflection_log_2941_neg
  have he : Real.log (10001713 / 10000000) = -Real.log (10000000 / 10001713) := by
    rw [show ((10001713 / 10000000) : ℝ) = ((10000000 / 10001713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2942_neg : (85657 / 500000000) ≤ -Real.log (9998287 / 10000000) ∧
    -Real.log (9998287 / 10000000) ≤ (34263 / 200000000) := by
  have h := checkLog_sound (w := (1713 / 19998287)) (n := 12)
    (lo := (85657 / 500000000)) (hi := (34263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998287) = 1/(9998287 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2942 : Bounds (-34263 / 200000000) (-85657 / 500000000) (Real.log (9998287 / 10000000)) := by
  have h := reflection_log_2942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2943_neg : (82474517 / 1000000000) ≤ -Real.log (1000000 / 1085971) ∧
    -Real.log (1000000 / 1085971) ≤ (41237259 / 500000000) := by
  have h := checkLog_sound (w := (85971 / 2085971)) (n := 12)
    (lo := (82474517 / 1000000000)) (hi := (41237259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085971 / 1000000) = 1/(1000000 / 1085971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2943 : Bounds (82474517 / 1000000000) (41237259 / 500000000) (Real.log (1085971 / 1000000)) := by
  have h := reflection_log_2943_neg
  have he : Real.log (1085971 / 1000000) = -Real.log (1000000 / 1085971) := by
    rw [show ((1085971 / 1000000) : ℝ) = ((1000000 / 1085971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
