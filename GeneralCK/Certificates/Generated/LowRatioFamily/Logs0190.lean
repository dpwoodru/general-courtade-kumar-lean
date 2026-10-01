import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12160_neg : (503135917 / 1000000000) ≤ -Real.log (250000000000 / 413474910033) ∧
    -Real.log (250000000000 / 413474910033) ≤ (251567959 / 500000000) := by
  have h := checkLog_sound (w := (163474910033 / 663474910033)) (n := 12)
    (lo := (503135917 / 1000000000)) (hi := (251567959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413474910033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413474910033 / 250000000000) = 1/(250000000000 / 413474910033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12160 : Bounds (503135917 / 1000000000) (251567959 / 500000000) (Real.log (413474910033 / 250000000000)) := by
  have h := reflection_log_12160_neg
  have he : Real.log (413474910033 / 250000000000) = -Real.log (250000000000 / 413474910033) := by
    rw [show ((413474910033 / 250000000000) : ℝ) = ((250000000000 / 413474910033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12161_neg : (127838661 / 125000000) ≤ -Real.log (500000000000 / 1390359168241) ∧
    -Real.log (500000000000 / 1390359168241) ≤ (102270929 / 100000000) := by
  have h := checkLog_sound (w := (390359168241 / 2390359168241)) (n := 12)
    (lo := (82390527 / 250000000)) (hi := (329562109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390359168241 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1390359168241 / 1000000000000) = 1/(500000000000 / 1390359168241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12161 : Bounds (127838661 / 125000000) (102270929 / 100000000) (Real.log (1390359168241 / 500000000000)) := by
  have h := reflection_log_12161_neg
  have he : Real.log (1390359168241 / 500000000000) = -Real.log (500000000000 / 1390359168241) := by
    rw [show ((1390359168241 / 500000000000) : ℝ) = ((500000000000 / 1390359168241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12162_neg : (205056203 / 200000000) ≤ -Real.log (25000000000 / 69696969697) ∧
    -Real.log (25000000000 / 69696969697) ≤ (1025281017 / 1000000000) := by
  have h := checkLog_sound (w := (19696969697 / 119696969697)) (n := 12)
    (lo := (66426767 / 200000000)) (hi := (83033459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69696969697 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69696969697 / 50000000000) = 1/(25000000000 / 69696969697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12162 : Bounds (205056203 / 200000000) (1025281017 / 1000000000) (Real.log (69696969697 / 25000000000)) := by
  have h := reflection_log_12162_neg
  have he : Real.log (69696969697 / 25000000000) = -Real.log (25000000000 / 69696969697) := by
    rw [show ((69696969697 / 25000000000) : ℝ) = ((25000000000 / 69696969697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12163_neg : (387301137 / 1000000000) ≤ -Real.log (1000 / 1473) ∧
    -Real.log (1000 / 1473) ≤ (193650569 / 500000000) := by
  have h := checkLog_sound (w := (473 / 2473)) (n := 12)
    (lo := (387301137 / 1000000000)) (hi := (193650569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 1000) = 1/(1000 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12163 : Bounds (387301137 / 1000000000) (193650569 / 500000000) (Real.log (1473 / 1000)) := by
  have h := reflection_log_12163_neg
  have he : Real.log (1473 / 1000) = -Real.log (1000 / 1473) := by
    rw [show ((1473 / 1000) : ℝ) = ((1000 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12164_neg : (64055473 / 100000000) ≤ -Real.log (527 / 1000) ∧
    -Real.log (527 / 1000) ≤ (640554731 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 1527)) (n := 12)
    (lo := (64055473 / 100000000)) (hi := (640554731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 527) = 1/(527 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12164 : Bounds (-640554731 / 1000000000) (-64055473 / 100000000) (Real.log (527 / 1000)) := by
  have h := reflection_log_12164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12165_neg : (59111 / 125000000) ≤ -Real.log (1000000 / 1000473) ∧
    -Real.log (1000000 / 1000473) ≤ (472889 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2000473)) (n := 12)
    (lo := (59111 / 125000000)) (hi := (472889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000473 / 1000000) = 1/(1000000 / 1000473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12165 : Bounds (59111 / 125000000) (472889 / 1000000000) (Real.log (1000473 / 1000000)) := by
  have h := reflection_log_12165_neg
  have he : Real.log (1000473 / 1000000) = -Real.log (1000000 / 1000473) := by
    rw [show ((1000473 / 1000000) : ℝ) = ((1000000 / 1000473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12166_neg : (473111 / 1000000000) ≤ -Real.log (999527 / 1000000) ∧
    -Real.log (999527 / 1000000) ≤ (59139 / 125000000) := by
  have h := checkLog_sound (w := (473 / 1999527)) (n := 12)
    (lo := (473111 / 1000000000)) (hi := (59139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999527) = 1/(999527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12166 : Bounds (-59139 / 125000000) (-473111 / 1000000000) (Real.log (999527 / 1000000)) := by
  have h := reflection_log_12166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12167_neg : (43978053 / 200000000) ≤ -Real.log (50000 / 62297) ∧
    -Real.log (50000 / 62297) ≤ (109945133 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 112297)) (n := 12)
    (lo := (43978053 / 200000000)) (hi := (109945133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62297 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62297 / 50000) = 1/(50000 / 62297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12167 : Bounds (43978053 / 200000000) (109945133 / 500000000) (Real.log (62297 / 50000)) := by
  have h := reflection_log_12167_neg
  have he : Real.log (62297 / 50000) = -Real.log (50000 / 62297) := by
    rw [show ((62297 / 50000) : ℝ) = ((50000 / 62297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12168_neg : (141141669 / 500000000) ≤ -Real.log (37703 / 50000) ∧
    -Real.log (37703 / 50000) ≤ (282283339 / 1000000000) := by
  have h := checkLog_sound (w := (12297 / 87703)) (n := 12)
    (lo := (141141669 / 500000000)) (hi := (282283339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37703) = 1/(37703 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12168 : Bounds (-282283339 / 1000000000) (-141141669 / 500000000) (Real.log (37703 / 50000)) := by
  have h := reflection_log_12168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12169_neg : (220708589 / 1000000000) ≤ -Real.log (12500 / 15587) ∧
    -Real.log (12500 / 15587) ≤ (22070859 / 100000000) := by
  have h := checkLog_sound (w := (3087 / 28087)) (n := 12)
    (lo := (220708589 / 1000000000)) (hi := (22070859 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15587 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15587 / 12500) = 1/(12500 / 15587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12169 : Bounds (220708589 / 1000000000) (22070859 / 100000000) (Real.log (15587 / 12500)) := by
  have h := reflection_log_12169_neg
  have he : Real.log (15587 / 12500) = -Real.log (12500 / 15587) := by
    rw [show ((15587 / 12500) : ℝ) = ((12500 / 15587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12170_neg : (283636931 / 1000000000) ≤ -Real.log (9413 / 12500) ∧
    -Real.log (9413 / 12500) ≤ (70909233 / 250000000) := by
  have h := checkLog_sound (w := (3087 / 21913)) (n := 12)
    (lo := (283636931 / 1000000000)) (hi := (70909233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9413) = 1/(9413 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12170 : Bounds (-70909233 / 250000000) (-283636931 / 1000000000) (Real.log (9413 / 12500)) := by
  have h := reflection_log_12170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12171_neg : (31464171 / 500000000) ≤ -Real.log (146720431 / 156250000) ∧
    -Real.log (146720431 / 156250000) ≤ (62928343 / 1000000000) := by
  have h := checkLog_sound (w := (9529569 / 302970431)) (n := 12)
    (lo := (31464171 / 500000000)) (hi := (62928343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 146720431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 146720431) = 1/(146720431 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12171 : Bounds (-62928343 / 1000000000) (-31464171 / 500000000) (Real.log (146720431 / 156250000)) := by
  have h := reflection_log_12171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12172_neg : (62393073 / 1000000000) ≤ -Real.log (2348783791 / 2500000000) ∧
    -Real.log (2348783791 / 2500000000) ≤ (31196537 / 500000000) := by
  have h := checkLog_sound (w := (151216209 / 4848783791)) (n := 12)
    (lo := (62393073 / 1000000000)) (hi := (31196537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2348783791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2348783791) = 1/(2348783791 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12172 : Bounds (-31196537 / 500000000) (-62393073 / 1000000000) (Real.log (2348783791 / 2500000000)) := by
  have h := reflection_log_12172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12173_neg : (502173603 / 1000000000) ≤ -Real.log (25000000000 / 41307720871) ∧
    -Real.log (25000000000 / 41307720871) ≤ (125543401 / 250000000) := by
  have h := checkLog_sound (w := (16307720871 / 66307720871)) (n := 12)
    (lo := (502173603 / 1000000000)) (hi := (125543401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41307720871 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41307720871 / 25000000000) = 1/(25000000000 / 41307720871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12173 : Bounds (502173603 / 1000000000) (125543401 / 250000000) (Real.log (41307720871 / 25000000000)) := by
  have h := reflection_log_12173_neg
  have he : Real.log (41307720871 / 25000000000) = -Real.log (25000000000 / 41307720871) := by
    rw [show ((41307720871 / 25000000000) : ℝ) = ((25000000000 / 41307720871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12174_neg : (6304319 / 12500000) ≤ -Real.log (50000000000 / 82795070647) ∧
    -Real.log (50000000000 / 82795070647) ≤ (504345521 / 1000000000) := by
  have h := checkLog_sound (w := (32795070647 / 132795070647)) (n := 12)
    (lo := (6304319 / 12500000)) (hi := (504345521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82795070647 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82795070647 / 50000000000) = 1/(50000000000 / 82795070647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12174 : Bounds (6304319 / 12500000) (504345521 / 1000000000) (Real.log (82795070647 / 50000000000)) := by
  have h := reflection_log_12174_neg
  have he : Real.log (82795070647 / 50000000000) = -Real.log (50000000000 / 82795070647) := by
    rw [show ((82795070647 / 50000000000) : ℝ) = ((50000000000 / 82795070647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12175_neg : (205056203 / 200000000) ≤ -Real.log (500000000000 / 1393939393939) ∧
    -Real.log (500000000000 / 1393939393939) ≤ (1025281017 / 1000000000) := by
  have h := checkLog_sound (w := (393939393939 / 2393939393939)) (n := 12)
    (lo := (66426767 / 200000000)) (hi := (83033459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393939393939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393939393939 / 1000000000000) = 1/(500000000000 / 1393939393939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12175 : Bounds (205056203 / 200000000) (1025281017 / 1000000000) (Real.log (1393939393939 / 500000000000)) := by
  have h := reflection_log_12175_neg
  have he : Real.log (1393939393939 / 500000000000) = -Real.log (500000000000 / 1393939393939) := by
    rw [show ((1393939393939 / 500000000000) : ℝ) = ((500000000000 / 1393939393939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12176_neg : (1027855867 / 1000000000) ≤ -Real.log (31250000000 / 87345825427) ∧
    -Real.log (31250000000 / 87345825427) ≤ (1027855869 / 1000000000) := by
  have h := checkLog_sound (w := (24845825427 / 149845825427)) (n := 12)
    (lo := (334708687 / 1000000000)) (hi := (20919293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87345825427 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(87345825427 / 62500000000) = 1/(31250000000 / 87345825427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12176 : Bounds (1027855867 / 1000000000) (1027855869 / 1000000000) (Real.log (87345825427 / 31250000000)) := by
  have h := reflection_log_12176_neg
  have he : Real.log (87345825427 / 31250000000) = -Real.log (31250000000 / 87345825427) := by
    rw [show ((87345825427 / 31250000000) : ℝ) = ((31250000000 / 87345825427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12177_neg : (387979793 / 1000000000) ≤ -Real.log (500 / 737) ∧
    -Real.log (500 / 737) ≤ (193989897 / 500000000) := by
  have h := checkLog_sound (w := (237 / 1237)) (n := 12)
    (lo := (387979793 / 1000000000)) (hi := (193989897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737 / 500) = 1/(500 / 737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12177 : Bounds (387979793 / 1000000000) (193989897 / 500000000) (Real.log (737 / 500)) := by
  have h := reflection_log_12177_neg
  have he : Real.log (737 / 500) = -Real.log (500 / 737) := by
    rw [show ((737 / 500) : ℝ) = ((500 / 737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12178_neg : (321227033 / 500000000) ≤ -Real.log (263 / 500) ∧
    -Real.log (263 / 500) ≤ (642454067 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 763)) (n := 12)
    (lo := (321227033 / 500000000)) (hi := (642454067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 263) = 1/(263 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12178 : Bounds (-642454067 / 1000000000) (-321227033 / 500000000) (Real.log (263 / 500)) := by
  have h := reflection_log_12178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12179_neg : (473887 / 1000000000) ≤ -Real.log (500000 / 500237) ∧
    -Real.log (500000 / 500237) ≤ (14809 / 31250000) := by
  have h := checkLog_sound (w := (237 / 1000237)) (n := 12)
    (lo := (473887 / 1000000000)) (hi := (14809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500237 / 500000) = 1/(500000 / 500237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12179 : Bounds (473887 / 1000000000) (14809 / 31250000) (Real.log (500237 / 500000)) := by
  have h := reflection_log_12179_neg
  have he : Real.log (500237 / 500000) = -Real.log (500000 / 500237) := by
    rw [show ((500237 / 500000) : ℝ) = ((500000 / 500237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12180_neg : (926 / 1953125) ≤ -Real.log (499763 / 500000) ∧
    -Real.log (499763 / 500000) ≤ (474113 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 999763)) (n := 12)
    (lo := (926 / 1953125)) (hi := (474113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499763) = 1/(499763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12180 : Bounds (-474113 / 1000000000) (-926 / 1953125) (Real.log (499763 / 500000)) := by
  have h := reflection_log_12180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12181_neg : (220346041 / 1000000000) ≤ -Real.log (250000 / 311627) ∧
    -Real.log (250000 / 311627) ≤ (110173021 / 500000000) := by
  have h := checkLog_sound (w := (61627 / 561627)) (n := 12)
    (lo := (220346041 / 1000000000)) (hi := (110173021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311627 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311627 / 250000) = 1/(250000 / 311627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12181 : Bounds (220346041 / 1000000000) (110173021 / 500000000) (Real.log (311627 / 250000)) := by
  have h := reflection_log_12181_neg
  have he : Real.log (311627 / 250000) = -Real.log (250000 / 311627) := by
    rw [show ((311627 / 250000) : ℝ) = ((250000 / 311627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12182_neg : (141518439 / 500000000) ≤ -Real.log (188373 / 250000) ∧
    -Real.log (188373 / 250000) ≤ (283036879 / 1000000000) := by
  have h := checkLog_sound (w := (61627 / 438373)) (n := 12)
    (lo := (141518439 / 500000000)) (hi := (283036879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188373) = 1/(188373 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12182 : Bounds (-283036879 / 1000000000) (-141518439 / 500000000) (Real.log (188373 / 250000)) := by
  have h := reflection_log_12182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12183_neg : (110582397 / 500000000) ≤ -Real.log (1000000 / 1247529) ∧
    -Real.log (1000000 / 1247529) ≤ (44232959 / 200000000) := by
  have h := checkLog_sound (w := (247529 / 2247529)) (n := 12)
    (lo := (110582397 / 500000000)) (hi := (44232959 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247529 / 1000000) = 1/(1000000 / 1247529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12183 : Bounds (110582397 / 500000000) (44232959 / 200000000) (Real.log (1247529 / 1000000)) := by
  have h := reflection_log_12183_neg
  have he : Real.log (1247529 / 1000000) = -Real.log (1000000 / 1247529) := by
    rw [show ((1247529 / 1000000) : ℝ) = ((1000000 / 1247529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12184_neg : (284392821 / 1000000000) ≤ -Real.log (752471 / 1000000) ∧
    -Real.log (752471 / 1000000) ≤ (142196411 / 500000000) := by
  have h := checkLog_sound (w := (247529 / 1752471)) (n := 12)
    (lo := (284392821 / 1000000000)) (hi := (142196411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752471) = 1/(752471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12184 : Bounds (-142196411 / 500000000) (-284392821 / 1000000000) (Real.log (752471 / 1000000)) := by
  have h := reflection_log_12184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12185_neg : (31614013 / 500000000) ≤ -Real.log (938729394159 / 1000000000000) ∧
    -Real.log (938729394159 / 1000000000000) ≤ (63228027 / 1000000000) := by
  have h := checkLog_sound (w := (61270605841 / 1938729394159)) (n := 12)
    (lo := (31614013 / 500000000)) (hi := (63228027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 938729394159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 938729394159) = 1/(938729394159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12185 : Bounds (-63228027 / 1000000000) (-31614013 / 500000000) (Real.log (938729394159 / 1000000000000)) := by
  have h := reflection_log_12185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12186_neg : (15672709 / 250000000) ≤ -Real.log (58702112871 / 62500000000) ∧
    -Real.log (58702112871 / 62500000000) ≤ (62690837 / 1000000000) := by
  have h := checkLog_sound (w := (3797887129 / 121202112871)) (n := 12)
    (lo := (15672709 / 250000000)) (hi := (62690837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58702112871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58702112871) = 1/(58702112871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12186 : Bounds (-62690837 / 1000000000) (-15672709 / 250000000) (Real.log (58702112871 / 62500000000)) := by
  have h := reflection_log_12186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12187_neg : (12584573 / 25000000) ≤ -Real.log (20000000000 / 33086164153) ∧
    -Real.log (20000000000 / 33086164153) ≤ (503382921 / 1000000000) := by
  have h := checkLog_sound (w := (13086164153 / 53086164153)) (n := 12)
    (lo := (12584573 / 25000000)) (hi := (503382921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33086164153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33086164153 / 20000000000) = 1/(20000000000 / 33086164153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12187 : Bounds (12584573 / 25000000) (503382921 / 1000000000) (Real.log (33086164153 / 20000000000)) := by
  have h := reflection_log_12187_neg
  have he : Real.log (33086164153 / 20000000000) = -Real.log (20000000000 / 33086164153) := by
    rw [show ((33086164153 / 20000000000) : ℝ) = ((20000000000 / 33086164153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12188_neg : (31597351 / 62500000) ≤ -Real.log (250000000000 / 414477435011) ∧
    -Real.log (250000000000 / 414477435011) ≤ (505557617 / 1000000000) := by
  have h := checkLog_sound (w := (164477435011 / 664477435011)) (n := 12)
    (lo := (31597351 / 62500000)) (hi := (505557617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414477435011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414477435011 / 250000000000) = 1/(250000000000 / 414477435011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12188 : Bounds (31597351 / 62500000) (505557617 / 1000000000) (Real.log (414477435011 / 250000000000)) := by
  have h := reflection_log_12188_neg
  have he : Real.log (414477435011 / 250000000000) = -Real.log (250000000000 / 414477435011) := by
    rw [show ((414477435011 / 250000000000) : ℝ) = ((250000000000 / 414477435011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12189_neg : (1027855867 / 1000000000) ≤ -Real.log (500000000000 / 1397533206831) ∧
    -Real.log (500000000000 / 1397533206831) ≤ (1027855869 / 1000000000) := by
  have h := checkLog_sound (w := (397533206831 / 2397533206831)) (n := 12)
    (lo := (334708687 / 1000000000)) (hi := (20919293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397533206831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1397533206831 / 1000000000000) = 1/(500000000000 / 1397533206831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12189 : Bounds (1027855867 / 1000000000) (1027855869 / 1000000000) (Real.log (1397533206831 / 500000000000)) := by
  have h := reflection_log_12189_neg
  have he : Real.log (1397533206831 / 500000000000) = -Real.log (500000000000 / 1397533206831) := by
    rw [show ((1397533206831 / 500000000000) : ℝ) = ((500000000000 / 1397533206831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12190_neg : (1030433859 / 1000000000) ≤ -Real.log (500000000000 / 1401140684411) ∧
    -Real.log (500000000000 / 1401140684411) ≤ (1030433861 / 1000000000) := by
  have h := checkLog_sound (w := (401140684411 / 2401140684411)) (n := 12)
    (lo := (337286679 / 1000000000)) (hi := (8432167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401140684411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1401140684411 / 1000000000000) = 1/(500000000000 / 1401140684411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12190 : Bounds (1030433859 / 1000000000) (1030433861 / 1000000000) (Real.log (1401140684411 / 500000000000)) := by
  have h := reflection_log_12190_neg
  have he : Real.log (1401140684411 / 500000000000) = -Real.log (500000000000 / 1401140684411) := by
    rw [show ((1401140684411 / 500000000000) : ℝ) = ((500000000000 / 1401140684411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12191_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12191 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_12191_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12192_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12192 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_12192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12193_neg : (474887 / 1000000000) ≤ -Real.log (40000 / 40019) ∧
    -Real.log (40000 / 40019) ≤ (59361 / 125000000) := by
  have h := checkLog_sound (w := (19 / 80019)) (n := 12)
    (lo := (474887 / 1000000000)) (hi := (59361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40019 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40019 / 40000) = 1/(40000 / 40019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12193 : Bounds (474887 / 1000000000) (59361 / 125000000) (Real.log (40019 / 40000)) := by
  have h := reflection_log_12193_neg
  have he : Real.log (40019 / 40000) = -Real.log (40000 / 40019) := by
    rw [show ((40019 / 40000) : ℝ) = ((40000 / 40019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12194_neg : (59389 / 125000000) ≤ -Real.log (39981 / 40000) ∧
    -Real.log (39981 / 40000) ≤ (475113 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 79981)) (n := 12)
    (lo := (59389 / 125000000)) (hi := (475113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39981) = 1/(39981 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12194 : Bounds (-475113 / 1000000000) (-59389 / 125000000) (Real.log (39981 / 40000)) := by
  have h := reflection_log_12194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12195_neg : (220801611 / 1000000000) ≤ -Real.log (250000 / 311769) ∧
    -Real.log (250000 / 311769) ≤ (55200403 / 250000000) := by
  have h := checkLog_sound (w := (61769 / 561769)) (n := 12)
    (lo := (220801611 / 1000000000)) (hi := (55200403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311769 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311769 / 250000) = 1/(250000 / 311769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12195 : Bounds (220801611 / 1000000000) (55200403 / 250000000) (Real.log (311769 / 250000)) := by
  have h := reflection_log_12195_neg
  have he : Real.log (311769 / 250000) = -Real.log (250000 / 311769) := by
    rw [show ((311769 / 250000) : ℝ) = ((250000 / 311769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12196_neg : (56758197 / 200000000) ≤ -Real.log (188231 / 250000) ∧
    -Real.log (188231 / 250000) ≤ (141895493 / 500000000) := by
  have h := checkLog_sound (w := (61769 / 438231)) (n := 12)
    (lo := (56758197 / 200000000)) (hi := (141895493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188231) = 1/(188231 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12196 : Bounds (-141895493 / 500000000) (-56758197 / 200000000) (Real.log (188231 / 250000)) := by
  have h := reflection_log_12196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12197_neg : (27702599 / 125000000) ≤ -Real.log (500000 / 624049) ∧
    -Real.log (500000 / 624049) ≤ (221620793 / 1000000000) := by
  have h := checkLog_sound (w := (124049 / 1124049)) (n := 12)
    (lo := (27702599 / 125000000)) (hi := (221620793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624049 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624049 / 500000) = 1/(500000 / 624049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12197 : Bounds (27702599 / 125000000) (221620793 / 1000000000) (Real.log (624049 / 500000)) := by
  have h := reflection_log_12197_neg
  have he : Real.log (624049 / 500000) = -Real.log (500000 / 624049) := by
    rw [show ((624049 / 500000) : ℝ) = ((500000 / 624049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12198_neg : (142574641 / 500000000) ≤ -Real.log (375951 / 500000) ∧
    -Real.log (375951 / 500000) ≤ (285149283 / 1000000000) := by
  have h := checkLog_sound (w := (124049 / 875951)) (n := 12)
    (lo := (142574641 / 500000000)) (hi := (285149283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375951) = 1/(375951 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12198 : Bounds (-285149283 / 1000000000) (-142574641 / 500000000) (Real.log (375951 / 500000)) := by
  have h := reflection_log_12198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12199_neg : (6352849 / 100000000) ≤ -Real.log (234611845599 / 250000000000) ∧
    -Real.log (234611845599 / 250000000000) ≤ (63528491 / 1000000000) := by
  have h := checkLog_sound (w := (15388154401 / 484611845599)) (n := 12)
    (lo := (6352849 / 100000000)) (hi := (63528491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234611845599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234611845599) = 1/(234611845599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12199 : Bounds (-63528491 / 1000000000) (-6352849 / 100000000) (Real.log (234611845599 / 250000000000)) := by
  have h := reflection_log_12199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12200_neg : (31494687 / 500000000) ≤ -Real.log (58684590639 / 62500000000) ∧
    -Real.log (58684590639 / 62500000000) ≤ (100783 / 1600000) := by
  have h := checkLog_sound (w := (3815409361 / 121184590639)) (n := 12)
    (lo := (31494687 / 500000000)) (hi := (100783 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58684590639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58684590639) = 1/(58684590639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12200 : Bounds (-100783 / 1600000) (-31494687 / 500000000) (Real.log (58684590639 / 62500000000)) := by
  have h := reflection_log_12200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12201_neg : (504592597 / 1000000000) ≤ -Real.log (250000000000 / 414077649271) ∧
    -Real.log (250000000000 / 414077649271) ≤ (252296299 / 500000000) := by
  have h := checkLog_sound (w := (164077649271 / 664077649271)) (n := 12)
    (lo := (504592597 / 1000000000)) (hi := (252296299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414077649271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414077649271 / 250000000000) = 1/(250000000000 / 414077649271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12201 : Bounds (504592597 / 1000000000) (252296299 / 500000000) (Real.log (414077649271 / 250000000000)) := by
  have h := reflection_log_12201_neg
  have he : Real.log (414077649271 / 250000000000) = -Real.log (250000000000 / 414077649271) := by
    rw [show ((414077649271 / 250000000000) : ℝ) = ((250000000000 / 414077649271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12202_neg : (20270803 / 40000000) ≤ -Real.log (50000000000 / 82996055337) ∧
    -Real.log (50000000000 / 82996055337) ≤ (126692519 / 250000000) := by
  have h := checkLog_sound (w := (32996055337 / 132996055337)) (n := 12)
    (lo := (20270803 / 40000000)) (hi := (126692519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82996055337 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82996055337 / 50000000000) = 1/(50000000000 / 82996055337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12202 : Bounds (20270803 / 40000000) (126692519 / 250000000) (Real.log (82996055337 / 50000000000)) := by
  have h := reflection_log_12202_neg
  have he : Real.log (82996055337 / 50000000000) = -Real.log (50000000000 / 82996055337) := by
    rw [show ((82996055337 / 50000000000) : ℝ) = ((50000000000 / 82996055337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12203_neg : (1030433859 / 1000000000) ≤ -Real.log (50000000000 / 140114068441) ∧
    -Real.log (50000000000 / 140114068441) ≤ (1030433861 / 1000000000) := by
  have h := checkLog_sound (w := (40114068441 / 240114068441)) (n := 12)
    (lo := (337286679 / 1000000000)) (hi := (8432167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140114068441 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(140114068441 / 100000000000) = 1/(50000000000 / 140114068441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12203 : Bounds (1030433859 / 1000000000) (1030433861 / 1000000000) (Real.log (140114068441 / 50000000000)) := by
  have h := reflection_log_12203_neg
  have he : Real.log (140114068441 / 50000000000) = -Real.log (50000000000 / 140114068441) := by
    rw [show ((140114068441 / 50000000000) : ℝ) = ((50000000000 / 140114068441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12204_neg : (206603001 / 200000000) ≤ -Real.log (250000000000 / 702380952381) ∧
    -Real.log (250000000000 / 702380952381) ≤ (1033015007 / 1000000000) := by
  have h := checkLog_sound (w := (202380952381 / 1202380952381)) (n := 12)
    (lo := (13594713 / 40000000)) (hi := (169933913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702380952381 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(702380952381 / 500000000000) = 1/(250000000000 / 702380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12204 : Bounds (206603001 / 200000000) (1033015007 / 1000000000) (Real.log (702380952381 / 250000000000)) := by
  have h := reflection_log_12204_neg
  have he : Real.log (702380952381 / 250000000000) = -Real.log (250000000000 / 702380952381) := by
    rw [show ((702380952381 / 250000000000) : ℝ) = ((250000000000 / 702380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12205_neg : (194667863 / 500000000) ≤ -Real.log (250 / 369) ∧
    -Real.log (250 / 369) ≤ (389335727 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 619)) (n := 12)
    (lo := (194667863 / 500000000)) (hi := (389335727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 250) = 1/(250 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12205 : Bounds (194667863 / 500000000) (389335727 / 1000000000) (Real.log (369 / 250)) := by
  have h := reflection_log_12205_neg
  have he : Real.log (369 / 250) = -Real.log (250 / 369) := by
    rw [show ((369 / 250) : ℝ) = ((250 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12206_neg : (323131797 / 500000000) ≤ -Real.log (131 / 250) ∧
    -Real.log (131 / 250) ≤ (129252719 / 200000000) := by
  have h := checkLog_sound (w := (119 / 381)) (n := 12)
    (lo := (323131797 / 500000000)) (hi := (129252719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 131) = 1/(131 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12206 : Bounds (-129252719 / 200000000) (-323131797 / 500000000) (Real.log (131 / 250)) := by
  have h := reflection_log_12206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12207_neg : (237943 / 500000000) ≤ -Real.log (250000 / 250119) ∧
    -Real.log (250000 / 250119) ≤ (475887 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 500119)) (n := 12)
    (lo := (237943 / 500000000)) (hi := (475887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250119 / 250000) = 1/(250000 / 250119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12207 : Bounds (237943 / 500000000) (475887 / 1000000000) (Real.log (250119 / 250000)) := by
  have h := reflection_log_12207_neg
  have he : Real.log (250119 / 250000) = -Real.log (250000 / 250119) := by
    rw [show ((250119 / 250000) : ℝ) = ((250000 / 250119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12208_neg : (476113 / 1000000000) ≤ -Real.log (249881 / 250000) ∧
    -Real.log (249881 / 250000) ≤ (238057 / 500000000) := by
  have h := checkLog_sound (w := (119 / 499881)) (n := 12)
    (lo := (476113 / 1000000000)) (hi := (238057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249881) = 1/(249881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12208 : Bounds (-238057 / 500000000) (-476113 / 1000000000) (Real.log (249881 / 250000)) := by
  have h := reflection_log_12208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12209_neg : (55314243 / 250000000) ≤ -Real.log (250000 / 311911) ∧
    -Real.log (250000 / 311911) ≤ (221256973 / 1000000000) := by
  have h := checkLog_sound (w := (61911 / 561911)) (n := 12)
    (lo := (55314243 / 250000000)) (hi := (221256973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311911 / 250000) = 1/(250000 / 311911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12209 : Bounds (55314243 / 250000000) (221256973 / 1000000000) (Real.log (311911 / 250000)) := by
  have h := reflection_log_12209_neg
  have he : Real.log (311911 / 250000) = -Real.log (250000 / 311911) := by
    rw [show ((311911 / 250000) : ℝ) = ((250000 / 311911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12210_neg : (142272831 / 500000000) ≤ -Real.log (188089 / 250000) ∧
    -Real.log (188089 / 250000) ≤ (284545663 / 1000000000) := by
  have h := checkLog_sound (w := (61911 / 438089)) (n := 12)
    (lo := (142272831 / 500000000)) (hi := (284545663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188089) = 1/(188089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12210 : Bounds (-284545663 / 1000000000) (-142272831 / 500000000) (Real.log (188089 / 250000)) := by
  have h := reflection_log_12210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12211_neg : (222077383 / 1000000000) ≤ -Real.log (250000 / 312167) ∧
    -Real.log (250000 / 312167) ≤ (27759673 / 125000000) := by
  have h := checkLog_sound (w := (62167 / 562167)) (n := 12)
    (lo := (222077383 / 1000000000)) (hi := (27759673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312167 / 250000) = 1/(250000 / 312167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12211 : Bounds (222077383 / 1000000000) (27759673 / 125000000) (Real.log (312167 / 250000)) := by
  have h := reflection_log_12211_neg
  have he : Real.log (312167 / 250000) = -Real.log (250000 / 312167) := by
    rw [show ((312167 / 250000) : ℝ) = ((250000 / 312167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12212_neg : (285907647 / 1000000000) ≤ -Real.log (187833 / 250000) ∧
    -Real.log (187833 / 250000) ≤ (4467307 / 15625000) := by
  have h := checkLog_sound (w := (62167 / 437833)) (n := 12)
    (lo := (285907647 / 1000000000)) (hi := (4467307 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187833) = 1/(187833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12212 : Bounds (-4467307 / 15625000) (-285907647 / 1000000000) (Real.log (187833 / 250000)) := by
  have h := reflection_log_12212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12213_neg : (7978783 / 125000000) ≤ -Real.log (58635264111 / 62500000000) ∧
    -Real.log (58635264111 / 62500000000) ≤ (12766053 / 200000000) := by
  have h := checkLog_sound (w := (3864735889 / 121135264111)) (n := 12)
    (lo := (7978783 / 125000000)) (hi := (12766053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58635264111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58635264111) = 1/(58635264111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12213 : Bounds (-12766053 / 200000000) (-7978783 / 125000000) (Real.log (58635264111 / 62500000000)) := by
  have h := reflection_log_12213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12214_neg : (63288689 / 1000000000) ≤ -Real.log (58667028079 / 62500000000) ∧
    -Real.log (58667028079 / 62500000000) ≤ (6328869 / 100000000) := by
  have h := checkLog_sound (w := (3832971921 / 121167028079)) (n := 12)
    (lo := (63288689 / 1000000000)) (hi := (6328869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58667028079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58667028079) = 1/(58667028079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12214 : Bounds (-6328869 / 100000000) (-63288689 / 1000000000) (Real.log (58667028079 / 62500000000)) := by
  have h := reflection_log_12214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12215_neg : (101160527 / 200000000) ≤ -Real.log (500000000000 / 829158004987) ∧
    -Real.log (500000000000 / 829158004987) ≤ (126450659 / 250000000) := by
  have h := checkLog_sound (w := (329158004987 / 1329158004987)) (n := 12)
    (lo := (101160527 / 200000000)) (hi := (126450659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829158004987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829158004987 / 500000000000) = 1/(500000000000 / 829158004987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12215 : Bounds (101160527 / 200000000) (126450659 / 250000000) (Real.log (829158004987 / 500000000000)) := by
  have h := reflection_log_12215_neg
  have he : Real.log (829158004987 / 500000000000) = -Real.log (500000000000 / 829158004987) := by
    rw [show ((829158004987 / 500000000000) : ℝ) = ((500000000000 / 829158004987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12216_neg : (50798503 / 100000000) ≤ -Real.log (250000000000 / 415484765723) ∧
    -Real.log (250000000000 / 415484765723) ≤ (507985031 / 1000000000) := by
  have h := checkLog_sound (w := (165484765723 / 665484765723)) (n := 12)
    (lo := (50798503 / 100000000)) (hi := (507985031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415484765723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415484765723 / 250000000000) = 1/(250000000000 / 415484765723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12216 : Bounds (50798503 / 100000000) (507985031 / 1000000000) (Real.log (415484765723 / 250000000000)) := by
  have h := reflection_log_12216_neg
  have he : Real.log (415484765723 / 250000000000) = -Real.log (250000000000 / 415484765723) := by
    rw [show ((415484765723 / 250000000000) : ℝ) = ((250000000000 / 415484765723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12217_neg : (206603001 / 200000000) ≤ -Real.log (500000000000 / 1404761904761) ∧
    -Real.log (500000000000 / 1404761904761) ≤ (1033015007 / 1000000000) := by
  have h := checkLog_sound (w := (404761904761 / 2404761904761)) (n := 12)
    (lo := (13594713 / 40000000)) (hi := (169933913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1404761904761 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1404761904761 / 1000000000000) = 1/(500000000000 / 1404761904761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12217 : Bounds (206603001 / 200000000) (1033015007 / 1000000000) (Real.log (1404761904761 / 500000000000)) := by
  have h := reflection_log_12217_neg
  have he : Real.log (1404761904761 / 500000000000) = -Real.log (500000000000 / 1404761904761) := by
    rw [show ((1404761904761 / 500000000000) : ℝ) = ((500000000000 / 1404761904761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12218_neg : (25889983 / 25000000) ≤ -Real.log (100000000000 / 281679389313) ∧
    -Real.log (100000000000 / 281679389313) ≤ (517799661 / 500000000) := by
  have h := checkLog_sound (w := (81679389313 / 481679389313)) (n := 12)
    (lo := (17122607 / 50000000)) (hi := (342452141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281679389313 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(281679389313 / 200000000000) = 1/(100000000000 / 281679389313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12218 : Bounds (25889983 / 25000000) (517799661 / 500000000) (Real.log (281679389313 / 100000000000)) := by
  have h := reflection_log_12218_neg
  have he : Real.log (281679389313 / 100000000000) = -Real.log (100000000000 / 281679389313) := by
    rw [show ((281679389313 / 100000000000) : ℝ) = ((100000000000 / 281679389313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12219_neg : (390013003 / 1000000000) ≤ -Real.log (1000 / 1477) ∧
    -Real.log (1000 / 1477) ≤ (97503251 / 250000000) := by
  have h := checkLog_sound (w := (477 / 2477)) (n := 12)
    (lo := (390013003 / 1000000000)) (hi := (97503251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1477 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1477 / 1000) = 1/(1000 / 1477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12219 : Bounds (390013003 / 1000000000) (97503251 / 250000000) (Real.log (1477 / 1000)) := by
  have h := reflection_log_12219_neg
  have he : Real.log (1477 / 1000) = -Real.log (1000 / 1477) := by
    rw [show ((1477 / 1000) : ℝ) = ((1000 / 1477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12220_neg : (324086907 / 500000000) ≤ -Real.log (523 / 1000) ∧
    -Real.log (523 / 1000) ≤ (129634763 / 200000000) := by
  have h := checkLog_sound (w := (477 / 1523)) (n := 12)
    (lo := (324086907 / 500000000)) (hi := (129634763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 523) = 1/(523 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12220 : Bounds (-129634763 / 200000000) (-324086907 / 500000000) (Real.log (523 / 1000)) := by
  have h := reflection_log_12220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12221_neg : (238443 / 500000000) ≤ -Real.log (1000000 / 1000477) ∧
    -Real.log (1000000 / 1000477) ≤ (476887 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 2000477)) (n := 12)
    (lo := (238443 / 500000000)) (hi := (476887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000477 / 1000000) = 1/(1000000 / 1000477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12221 : Bounds (238443 / 500000000) (476887 / 1000000000) (Real.log (1000477 / 1000000)) := by
  have h := reflection_log_12221_neg
  have he : Real.log (1000477 / 1000000) = -Real.log (1000000 / 1000477) := by
    rw [show ((1000477 / 1000000) : ℝ) = ((1000000 / 1000477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12222_neg : (477113 / 1000000000) ≤ -Real.log (999523 / 1000000) ∧
    -Real.log (999523 / 1000000) ≤ (238557 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1999523)) (n := 12)
    (lo := (477113 / 1000000000)) (hi := (238557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999523) = 1/(999523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12222 : Bounds (-238557 / 500000000) (-477113 / 1000000000) (Real.log (999523 / 1000000)) := by
  have h := reflection_log_12222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12223_neg : (6928529 / 31250000) ≤ -Real.log (1000000 / 1248213) ∧
    -Real.log (1000000 / 1248213) ≤ (221712929 / 1000000000) := by
  have h := checkLog_sound (w := (248213 / 2248213)) (n := 12)
    (lo := (6928529 / 31250000)) (hi := (221712929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248213 / 1000000) = 1/(1000000 / 1248213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12223 : Bounds (6928529 / 31250000) (221712929 / 1000000000) (Real.log (1248213 / 1000000)) := by
  have h := reflection_log_12223_neg
  have he : Real.log (1248213 / 1000000) = -Real.log (1000000 / 1248213) := by
    rw [show ((1248213 / 1000000) : ℝ) = ((1000000 / 1248213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
