import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10688_neg : (51887073 / 250000000) ≤ -Real.log (406287 / 500000) ∧
    -Real.log (406287 / 500000) ≤ (207548293 / 1000000000) := by
  have h := checkLog_sound (w := (93713 / 906287)) (n := 12)
    (lo := (51887073 / 250000000)) (hi := (207548293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406287) = 1/(406287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10688 : Bounds (-207548293 / 1000000000) (-51887073 / 250000000) (Real.log (406287 / 500000)) := by
  have h := reflection_log_10688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10689_neg : (172542227 / 1000000000) ≤ -Real.log (500000 / 594161) ∧
    -Real.log (500000 / 594161) ≤ (43135557 / 250000000) := by
  have h := checkLog_sound (w := (94161 / 1094161)) (n := 12)
    (lo := (172542227 / 1000000000)) (hi := (43135557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594161 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594161 / 500000) = 1/(500000 / 594161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10689 : Bounds (172542227 / 1000000000) (43135557 / 250000000) (Real.log (594161 / 500000)) := by
  have h := reflection_log_10689_neg
  have he : Real.log (594161 / 500000) = -Real.log (500000 / 594161) := by
    rw [show ((594161 / 500000) : ℝ) = ((500000 / 594161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10690_neg : (208651569 / 1000000000) ≤ -Real.log (405839 / 500000) ∧
    -Real.log (405839 / 500000) ≤ (20865157 / 100000000) := by
  have h := checkLog_sound (w := (94161 / 905839)) (n := 12)
    (lo := (208651569 / 1000000000)) (hi := (20865157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405839) = 1/(405839 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10690 : Bounds (-20865157 / 100000000) (-208651569 / 1000000000) (Real.log (405839 / 500000)) := by
  have h := reflection_log_10690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10691_neg : (36109341 / 1000000000) ≤ -Real.log (241133706079 / 250000000000) ∧
    -Real.log (241133706079 / 250000000000) ≤ (18054671 / 500000000) := by
  have h := checkLog_sound (w := (8866293921 / 491133706079)) (n := 12)
    (lo := (36109341 / 1000000000)) (hi := (18054671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241133706079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241133706079) = 1/(241133706079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10691 : Bounds (-18054671 / 500000000) (-36109341 / 1000000000) (Real.log (241133706079 / 250000000000)) := by
  have h := reflection_log_10691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10692_neg : (1117511 / 31250000) ≤ -Real.log (241217873631 / 250000000000) ∧
    -Real.log (241217873631 / 250000000000) ≤ (35760353 / 1000000000) := by
  have h := checkLog_sound (w := (8782126369 / 491217873631)) (n := 12)
    (lo := (1117511 / 31250000)) (hi := (35760353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241217873631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241217873631) = 1/(241217873631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10692 : Bounds (-35760353 / 1000000000) (-1117511 / 31250000) (Real.log (241217873631 / 250000000000)) := by
  have h := reflection_log_10692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10693_neg : (379336231 / 1000000000) ≤ -Real.log (250000000000 / 365328573151) ∧
    -Real.log (250000000000 / 365328573151) ≤ (47417029 / 125000000) := by
  have h := checkLog_sound (w := (115328573151 / 615328573151)) (n := 12)
    (lo := (379336231 / 1000000000)) (hi := (47417029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365328573151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365328573151 / 250000000000) = 1/(250000000000 / 365328573151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10693 : Bounds (379336231 / 1000000000) (47417029 / 125000000) (Real.log (365328573151 / 250000000000)) := by
  have h := reflection_log_10693_neg
  have he : Real.log (365328573151 / 250000000000) = -Real.log (250000000000 / 365328573151) := by
    rw [show ((365328573151 / 250000000000) : ℝ) = ((250000000000 / 365328573151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10694_neg : (381193797 / 1000000000) ≤ -Real.log (500000000000 / 732015651527) ∧
    -Real.log (500000000000 / 732015651527) ≤ (190596899 / 500000000) := by
  have h := checkLog_sound (w := (232015651527 / 1232015651527)) (n := 12)
    (lo := (381193797 / 1000000000)) (hi := (190596899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732015651527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732015651527 / 500000000000) = 1/(500000000000 / 732015651527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10694 : Bounds (381193797 / 1000000000) (190596899 / 500000000) (Real.log (732015651527 / 500000000000)) := by
  have h := reflection_log_10694_neg
  have he : Real.log (732015651527 / 500000000000) = -Real.log (500000000000 / 732015651527) := by
    rw [show ((732015651527 / 500000000000) : ℝ) = ((500000000000 / 732015651527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10695_neg : (153518617 / 200000000) ≤ -Real.log (250000000000 / 538643533123) ∧
    -Real.log (250000000000 / 538643533123) ≤ (767593087 / 1000000000) := by
  have h := checkLog_sound (w := (38643533123 / 1038643533123)) (n := 12)
    (lo := (14889181 / 200000000)) (hi := (37222953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538643533123 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(538643533123 / 500000000000) = 1/(250000000000 / 538643533123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10695 : Bounds (153518617 / 200000000) (767593087 / 1000000000) (Real.log (538643533123 / 250000000000)) := by
  have h := reflection_log_10695_neg
  have he : Real.log (538643533123 / 250000000000) = -Real.log (250000000000 / 538643533123) := by
    rw [show ((538643533123 / 250000000000) : ℝ) = ((250000000000 / 538643533123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10696_neg : (384951707 / 500000000) ≤ -Real.log (125000000000 / 269944707741) ∧
    -Real.log (125000000000 / 269944707741) ≤ (96237927 / 125000000) := by
  have h := checkLog_sound (w := (19944707741 / 519944707741)) (n := 12)
    (lo := (38378117 / 500000000)) (hi := (15351247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269944707741 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269944707741 / 250000000000) = 1/(125000000000 / 269944707741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10696 : Bounds (384951707 / 500000000) (96237927 / 125000000) (Real.log (269944707741 / 125000000000)) := by
  have h := reflection_log_10696_neg
  have he : Real.log (269944707741 / 125000000000) = -Real.log (125000000000 / 269944707741) := by
    rw [show ((269944707741 / 125000000000) : ℝ) = ((125000000000 / 269944707741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10697_neg : (313349819 / 1000000000) ≤ -Real.log (125 / 171) ∧
    -Real.log (125 / 171) ≤ (15667491 / 50000000) := by
  have h := checkLog_sound (w := (23 / 148)) (n := 12)
    (lo := (313349819 / 1000000000)) (hi := (15667491 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 125) = 1/(125 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10697 : Bounds (313349819 / 1000000000) (15667491 / 50000000) (Real.log (171 / 125)) := by
  have h := reflection_log_10697_neg
  have he : Real.log (171 / 125) = -Real.log (125 / 171) := by
    rw [show ((171 / 125) : ℝ) = ((125 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10698_neg : (114716471 / 250000000) ≤ -Real.log (79 / 125) ∧
    -Real.log (79 / 125) ≤ (91773177 / 200000000) := by
  have h := checkLog_sound (w := (23 / 102)) (n := 12)
    (lo := (114716471 / 250000000)) (hi := (91773177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 79) = 1/(79 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10698 : Bounds (-91773177 / 200000000) (-114716471 / 250000000) (Real.log (79 / 125)) := by
  have h := reflection_log_10698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10699_neg : (91983 / 250000000) ≤ -Real.log (62500 / 62523) ∧
    -Real.log (62500 / 62523) ≤ (367933 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 125023)) (n := 12)
    (lo := (91983 / 250000000)) (hi := (367933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62523 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62523 / 62500) = 1/(62500 / 62523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10699 : Bounds (91983 / 250000000) (367933 / 1000000000) (Real.log (62523 / 62500)) := by
  have h := reflection_log_10699_neg
  have he : Real.log (62523 / 62500) = -Real.log (62500 / 62523) := by
    rw [show ((62523 / 62500) : ℝ) = ((62500 / 62523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10700_neg : (368067 / 1000000000) ≤ -Real.log (62477 / 62500) ∧
    -Real.log (62477 / 62500) ≤ (92017 / 250000000) := by
  have h := checkLog_sound (w := (23 / 124977)) (n := 12)
    (lo := (368067 / 1000000000)) (hi := (92017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62477) = 1/(62477 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10700 : Bounds (-92017 / 250000000) (-368067 / 1000000000) (Real.log (62477 / 62500)) := by
  have h := reflection_log_10700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10701_neg : (172240917 / 1000000000) ≤ -Real.log (250000 / 296991) ∧
    -Real.log (250000 / 296991) ≤ (86120459 / 500000000) := by
  have h := checkLog_sound (w := (46991 / 546991)) (n := 12)
    (lo := (172240917 / 1000000000)) (hi := (86120459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296991 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296991 / 250000) = 1/(250000 / 296991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10701 : Bounds (172240917 / 1000000000) (86120459 / 500000000) (Real.log (296991 / 250000)) := by
  have h := reflection_log_10701_neg
  have he : Real.log (296991 / 250000) = -Real.log (250000 / 296991) := by
    rw [show ((296991 / 250000) : ℝ) = ((250000 / 296991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10702_neg : (52052651 / 250000000) ≤ -Real.log (203009 / 250000) ∧
    -Real.log (203009 / 250000) ≤ (41642121 / 200000000) := by
  have h := checkLog_sound (w := (46991 / 453009)) (n := 12)
    (lo := (52052651 / 250000000)) (hi := (41642121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203009) = 1/(203009 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10702 : Bounds (-41642121 / 200000000) (-52052651 / 250000000) (Real.log (203009 / 250000)) := by
  have h := reflection_log_10702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10703_neg : (172996547 / 1000000000) ≤ -Real.log (500000 / 594431) ∧
    -Real.log (500000 / 594431) ≤ (43249137 / 250000000) := by
  have h := checkLog_sound (w := (94431 / 1094431)) (n := 12)
    (lo := (172996547 / 1000000000)) (hi := (43249137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594431 / 500000) = 1/(500000 / 594431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10703 : Bounds (172996547 / 1000000000) (43249137 / 250000000) (Real.log (594431 / 500000)) := by
  have h := reflection_log_10703_neg
  have he : Real.log (594431 / 500000) = -Real.log (500000 / 594431) := by
    rw [show ((594431 / 500000) : ℝ) = ((500000 / 594431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10704_neg : (209317079 / 1000000000) ≤ -Real.log (405569 / 500000) ∧
    -Real.log (405569 / 500000) ≤ (5232927 / 25000000) := by
  have h := checkLog_sound (w := (94431 / 905569)) (n := 12)
    (lo := (209317079 / 1000000000)) (hi := (5232927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405569) = 1/(405569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10704 : Bounds (-5232927 / 25000000) (-209317079 / 1000000000) (Real.log (405569 / 500000)) := by
  have h := reflection_log_10704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10705_neg : (36320531 / 1000000000) ≤ -Real.log (241082786239 / 250000000000) ∧
    -Real.log (241082786239 / 250000000000) ≤ (9080133 / 250000000) := by
  have h := checkLog_sound (w := (8917213761 / 491082786239)) (n := 12)
    (lo := (36320531 / 1000000000)) (hi := (9080133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241082786239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241082786239) = 1/(241082786239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10705 : Bounds (-9080133 / 250000000) (-36320531 / 1000000000) (Real.log (241082786239 / 250000000000)) := by
  have h := reflection_log_10705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10706_neg : (35969687 / 1000000000) ≤ -Real.log (60291845919 / 62500000000) ∧
    -Real.log (60291845919 / 62500000000) ≤ (4496211 / 125000000) := by
  have h := checkLog_sound (w := (2208154081 / 122791845919)) (n := 12)
    (lo := (35969687 / 1000000000)) (hi := (4496211 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60291845919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60291845919) = 1/(60291845919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10706 : Bounds (-4496211 / 125000000) (-35969687 / 1000000000) (Real.log (60291845919 / 62500000000)) := by
  have h := reflection_log_10706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10707_neg : (190225761 / 500000000) ≤ -Real.log (500000000000 / 731472496293) ∧
    -Real.log (500000000000 / 731472496293) ≤ (380451523 / 1000000000) := by
  have h := checkLog_sound (w := (231472496293 / 1231472496293)) (n := 12)
    (lo := (190225761 / 500000000)) (hi := (380451523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731472496293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731472496293 / 500000000000) = 1/(500000000000 / 731472496293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10707 : Bounds (190225761 / 500000000) (380451523 / 1000000000) (Real.log (731472496293 / 500000000000)) := by
  have h := reflection_log_10707_neg
  have he : Real.log (731472496293 / 500000000000) = -Real.log (500000000000 / 731472496293) := by
    rw [show ((731472496293 / 500000000000) : ℝ) = ((500000000000 / 731472496293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10708_neg : (191156813 / 500000000) ≤ -Real.log (500000000000 / 732835842977) ∧
    -Real.log (500000000000 / 732835842977) ≤ (382313627 / 1000000000) := by
  have h := checkLog_sound (w := (232835842977 / 1232835842977)) (n := 12)
    (lo := (191156813 / 500000000)) (hi := (382313627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732835842977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732835842977 / 500000000000) = 1/(500000000000 / 732835842977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10708 : Bounds (191156813 / 500000000) (382313627 / 1000000000) (Real.log (732835842977 / 500000000000)) := by
  have h := reflection_log_10708_neg
  have he : Real.log (732835842977 / 500000000000) = -Real.log (500000000000 / 732835842977) := by
    rw [show ((732835842977 / 500000000000) : ℝ) = ((500000000000 / 732835842977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10709_neg : (384951707 / 500000000) ≤ -Real.log (500000000000 / 1079778830963) ∧
    -Real.log (500000000000 / 1079778830963) ≤ (96237927 / 125000000) := by
  have h := checkLog_sound (w := (79778830963 / 2079778830963)) (n := 12)
    (lo := (38378117 / 500000000)) (hi := (15351247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079778830963 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1079778830963 / 1000000000000) = 1/(500000000000 / 1079778830963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10709 : Bounds (384951707 / 500000000) (96237927 / 125000000) (Real.log (1079778830963 / 500000000000)) := by
  have h := reflection_log_10709_neg
  have he : Real.log (1079778830963 / 500000000000) = -Real.log (500000000000 / 1079778830963) := by
    rw [show ((1079778830963 / 500000000000) : ℝ) = ((500000000000 / 1079778830963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10710_neg : (772215703 / 1000000000) ≤ -Real.log (500000000000 / 1082278481013) ∧
    -Real.log (500000000000 / 1082278481013) ≤ (154443141 / 200000000) := by
  have h := checkLog_sound (w := (82278481013 / 2082278481013)) (n := 12)
    (lo := (79068523 / 1000000000)) (hi := (19767131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082278481013 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1082278481013 / 1000000000000) = 1/(500000000000 / 1082278481013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10710 : Bounds (772215703 / 1000000000) (154443141 / 200000000) (Real.log (1082278481013 / 500000000000)) := by
  have h := reflection_log_10710_neg
  have he : Real.log (1082278481013 / 500000000000) = -Real.log (500000000000 / 1082278481013) := by
    rw [show ((1082278481013 / 500000000000) : ℝ) = ((500000000000 / 1082278481013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10711_neg : (157040273 / 500000000) ≤ -Real.log (1000 / 1369) ∧
    -Real.log (1000 / 1369) ≤ (314080547 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 2369)) (n := 12)
    (lo := (157040273 / 500000000)) (hi := (314080547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369 / 1000) = 1/(1000 / 1369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10711 : Bounds (157040273 / 500000000) (314080547 / 1000000000) (Real.log (1369 / 1000)) := by
  have h := reflection_log_10711_neg
  have he : Real.log (1369 / 1000) = -Real.log (1000 / 1369) := by
    rw [show ((1369 / 1000) : ℝ) = ((1000 / 1369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10712_neg : (57556177 / 125000000) ≤ -Real.log (631 / 1000) ∧
    -Real.log (631 / 1000) ≤ (460449417 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1631)) (n := 12)
    (lo := (57556177 / 125000000)) (hi := (460449417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 631) = 1/(631 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10712 : Bounds (-460449417 / 1000000000) (-57556177 / 125000000) (Real.log (631 / 1000)) := by
  have h := reflection_log_10712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10713_neg : (368931 / 1000000000) ≤ -Real.log (1000000 / 1000369) ∧
    -Real.log (1000000 / 1000369) ≤ (92233 / 250000000) := by
  have h := checkLog_sound (w := (369 / 2000369)) (n := 12)
    (lo := (368931 / 1000000000)) (hi := (92233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000369 / 1000000) = 1/(1000000 / 1000369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10713 : Bounds (368931 / 1000000000) (92233 / 250000000) (Real.log (1000369 / 1000000)) := by
  have h := reflection_log_10713_neg
  have he : Real.log (1000369 / 1000000) = -Real.log (1000000 / 1000369) := by
    rw [show ((1000369 / 1000000) : ℝ) = ((1000000 / 1000369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10714_neg : (92267 / 250000000) ≤ -Real.log (999631 / 1000000) ∧
    -Real.log (999631 / 1000000) ≤ (369069 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1999631)) (n := 12)
    (lo := (92267 / 250000000)) (hi := (369069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999631) = 1/(999631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10714 : Bounds (-369069 / 1000000000) (-92267 / 250000000) (Real.log (999631 / 1000000)) := by
  have h := reflection_log_10714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10715_neg : (43173633 / 250000000) ≤ -Real.log (1000000 / 1188503) ∧
    -Real.log (1000000 / 1188503) ≤ (172694533 / 1000000000) := by
  have h := checkLog_sound (w := (188503 / 2188503)) (n := 12)
    (lo := (43173633 / 250000000)) (hi := (172694533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188503 / 1000000) = 1/(1000000 / 1188503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10715 : Bounds (43173633 / 250000000) (172694533 / 1000000000) (Real.log (1188503 / 1000000)) := by
  have h := reflection_log_10715_neg
  have he : Real.log (1188503 / 1000000) = -Real.log (1000000 / 1188503) := by
    rw [show ((1188503 / 1000000) : ℝ) = ((1000000 / 1188503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10716_neg : (52218647 / 250000000) ≤ -Real.log (811497 / 1000000) ∧
    -Real.log (811497 / 1000000) ≤ (208874589 / 1000000000) := by
  have h := checkLog_sound (w := (188503 / 1811497)) (n := 12)
    (lo := (52218647 / 250000000)) (hi := (208874589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811497) = 1/(811497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10716 : Bounds (-208874589 / 1000000000) (-52218647 / 250000000) (Real.log (811497 / 1000000)) := by
  have h := reflection_log_10716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10717_neg : (173450659 / 1000000000) ≤ -Real.log (500000 / 594701) ∧
    -Real.log (500000 / 594701) ≤ (8672533 / 50000000) := by
  have h := checkLog_sound (w := (94701 / 1094701)) (n := 12)
    (lo := (173450659 / 1000000000)) (hi := (8672533 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594701 / 500000) = 1/(500000 / 594701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10717 : Bounds (173450659 / 1000000000) (8672533 / 50000000) (Real.log (594701 / 500000)) := by
  have h := reflection_log_10717_neg
  have he : Real.log (594701 / 500000) = -Real.log (500000 / 594701) := by
    rw [show ((594701 / 500000) : ℝ) = ((500000 / 594701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10718_neg : (26247879 / 125000000) ≤ -Real.log (405299 / 500000) ∧
    -Real.log (405299 / 500000) ≤ (209983033 / 1000000000) := by
  have h := checkLog_sound (w := (94701 / 905299)) (n := 12)
    (lo := (26247879 / 125000000)) (hi := (209983033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405299) = 1/(405299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10718 : Bounds (-209983033 / 1000000000) (-26247879 / 125000000) (Real.log (405299 / 500000)) := by
  have h := reflection_log_10718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10719_neg : (9133093 / 250000000) ≤ -Real.log (241031720599 / 250000000000) ∧
    -Real.log (241031720599 / 250000000000) ≤ (36532373 / 1000000000) := by
  have h := checkLog_sound (w := (8968279401 / 491031720599)) (n := 12)
    (lo := (9133093 / 250000000)) (hi := (36532373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241031720599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241031720599) = 1/(241031720599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10719 : Bounds (-36532373 / 1000000000) (-9133093 / 250000000) (Real.log (241031720599 / 250000000000)) := by
  have h := reflection_log_10719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10720_neg : (4522507 / 125000000) ≤ -Real.log (964466618991 / 1000000000000) ∧
    -Real.log (964466618991 / 1000000000000) ≤ (36180057 / 1000000000) := by
  have h := checkLog_sound (w := (35533381009 / 1964466618991)) (n := 12)
    (lo := (4522507 / 125000000)) (hi := (36180057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964466618991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964466618991) = 1/(964466618991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10720 : Bounds (-36180057 / 1000000000) (-4522507 / 125000000) (Real.log (964466618991 / 1000000000000)) := by
  have h := reflection_log_10720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10721_neg : (2384807 / 6250000) ≤ -Real.log (62500000000 / 91536305741) ∧
    -Real.log (62500000000 / 91536305741) ≤ (381569121 / 1000000000) := by
  have h := checkLog_sound (w := (29036305741 / 154036305741)) (n := 12)
    (lo := (2384807 / 6250000)) (hi := (381569121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91536305741 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91536305741 / 62500000000) = 1/(62500000000 / 91536305741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10721 : Bounds (2384807 / 6250000) (381569121 / 1000000000) (Real.log (91536305741 / 62500000000)) := by
  have h := reflection_log_10721_neg
  have he : Real.log (91536305741 / 62500000000) = -Real.log (62500000000 / 91536305741) := by
    rw [show ((91536305741 / 62500000000) : ℝ) = ((62500000000 / 91536305741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10722_neg : (383433691 / 1000000000) ≤ -Real.log (62500000000 / 91707140901) ∧
    -Real.log (62500000000 / 91707140901) ≤ (95858423 / 250000000) := by
  have h := checkLog_sound (w := (29207140901 / 154207140901)) (n := 12)
    (lo := (383433691 / 1000000000)) (hi := (95858423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91707140901 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91707140901 / 62500000000) = 1/(62500000000 / 91707140901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10722 : Bounds (383433691 / 1000000000) (95858423 / 250000000) (Real.log (91707140901 / 62500000000)) := by
  have h := reflection_log_10722_neg
  have he : Real.log (91707140901 / 62500000000) = -Real.log (62500000000 / 91707140901) := by
    rw [show ((91707140901 / 62500000000) : ℝ) = ((62500000000 / 91707140901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10723_neg : (772215703 / 1000000000) ≤ -Real.log (125000000000 / 270569620253) ∧
    -Real.log (125000000000 / 270569620253) ≤ (154443141 / 200000000) := by
  have h := checkLog_sound (w := (20569620253 / 520569620253)) (n := 12)
    (lo := (79068523 / 1000000000)) (hi := (19767131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270569620253 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270569620253 / 250000000000) = 1/(125000000000 / 270569620253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10723 : Bounds (772215703 / 1000000000) (154443141 / 200000000) (Real.log (270569620253 / 125000000000)) := by
  have h := reflection_log_10723_neg
  have he : Real.log (270569620253 / 125000000000) = -Real.log (125000000000 / 270569620253) := by
    rw [show ((270569620253 / 125000000000) : ℝ) = ((125000000000 / 270569620253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10724_neg : (387264981 / 500000000) ≤ -Real.log (500000000000 / 1084786053883) ∧
    -Real.log (500000000000 / 1084786053883) ≤ (193632491 / 250000000) := by
  have h := checkLog_sound (w := (84786053883 / 2084786053883)) (n := 12)
    (lo := (40691391 / 500000000)) (hi := (81382783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084786053883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084786053883 / 1000000000000) = 1/(500000000000 / 1084786053883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10724 : Bounds (387264981 / 500000000) (193632491 / 250000000) (Real.log (1084786053883 / 500000000000)) := by
  have h := reflection_log_10724_neg
  have he : Real.log (1084786053883 / 500000000000) = -Real.log (500000000000 / 1084786053883) := by
    rw [show ((1084786053883 / 500000000000) : ℝ) = ((500000000000 / 1084786053883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10725_neg : (314810739 / 1000000000) ≤ -Real.log (100 / 137) ∧
    -Real.log (100 / 137) ≤ (15740537 / 50000000) := by
  have h := checkLog_sound (w := (37 / 237)) (n := 12)
    (lo := (314810739 / 1000000000)) (hi := (15740537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137 / 100) = 1/(100 / 137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10725 : Bounds (314810739 / 1000000000) (15740537 / 50000000) (Real.log (137 / 100)) := by
  have h := reflection_log_10725_neg
  have he : Real.log (137 / 100) = -Real.log (100 / 137) := by
    rw [show ((137 / 100) : ℝ) = ((100 / 137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10726_neg : (462035459 / 1000000000) ≤ -Real.log (63 / 100) ∧
    -Real.log (63 / 100) ≤ (23101773 / 50000000) := by
  have h := checkLog_sound (w := (37 / 163)) (n := 12)
    (lo := (462035459 / 1000000000)) (hi := (23101773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 63) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 63) = 1/(63 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10726 : Bounds (-23101773 / 50000000) (-462035459 / 1000000000) (Real.log (63 / 100)) := by
  have h := reflection_log_10726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10727_neg : (369931 / 1000000000) ≤ -Real.log (100000 / 100037) ∧
    -Real.log (100000 / 100037) ≤ (92483 / 250000000) := by
  have h := checkLog_sound (w := (37 / 200037)) (n := 12)
    (lo := (369931 / 1000000000)) (hi := (92483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100037 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100037 / 100000) = 1/(100000 / 100037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10727 : Bounds (369931 / 1000000000) (92483 / 250000000) (Real.log (100037 / 100000)) := by
  have h := reflection_log_10727_neg
  have he : Real.log (100037 / 100000) = -Real.log (100000 / 100037) := by
    rw [show ((100037 / 100000) : ℝ) = ((100000 / 100037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10728_neg : (92517 / 250000000) ≤ -Real.log (99963 / 100000) ∧
    -Real.log (99963 / 100000) ≤ (370069 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 199963)) (n := 12)
    (lo := (92517 / 250000000)) (hi := (370069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99963) = 1/(99963 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10728 : Bounds (-370069 / 1000000000) (-92517 / 250000000) (Real.log (99963 / 100000)) := by
  have h := reflection_log_10728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10729_neg : (8657397 / 50000000) ≤ -Real.log (500000 / 594521) ∧
    -Real.log (500000 / 594521) ≤ (173147941 / 1000000000) := by
  have h := checkLog_sound (w := (94521 / 1094521)) (n := 12)
    (lo := (8657397 / 50000000)) (hi := (173147941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594521 / 500000) = 1/(500000 / 594521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10729 : Bounds (8657397 / 50000000) (173147941 / 1000000000) (Real.log (594521 / 500000)) := by
  have h := reflection_log_10729_neg
  have he : Real.log (594521 / 500000) = -Real.log (500000 / 594521) := by
    rw [show ((594521 / 500000) : ℝ) = ((500000 / 594521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10730_neg : (104769507 / 500000000) ≤ -Real.log (405479 / 500000) ∧
    -Real.log (405479 / 500000) ≤ (41907803 / 200000000) := by
  have h := checkLog_sound (w := (94521 / 905479)) (n := 12)
    (lo := (104769507 / 500000000)) (hi := (41907803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405479) = 1/(405479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10730 : Bounds (-41907803 / 200000000) (-104769507 / 500000000) (Real.log (405479 / 500000)) := by
  have h := reflection_log_10730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10731_neg : (86952283 / 500000000) ≤ -Real.log (500000 / 594971) ∧
    -Real.log (500000 / 594971) ≤ (173904567 / 1000000000) := by
  have h := checkLog_sound (w := (94971 / 1094971)) (n := 12)
    (lo := (86952283 / 500000000)) (hi := (173904567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594971 / 500000) = 1/(500000 / 594971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10731 : Bounds (86952283 / 500000000) (173904567 / 1000000000) (Real.log (594971 / 500000)) := by
  have h := reflection_log_10731_neg
  have he : Real.log (594971 / 500000) = -Real.log (500000 / 594971) := by
    rw [show ((594971 / 500000) : ℝ) = ((500000 / 594971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10732_neg : (52662357 / 250000000) ≤ -Real.log (405029 / 500000) ∧
    -Real.log (405029 / 500000) ≤ (210649429 / 1000000000) := by
  have h := checkLog_sound (w := (94971 / 905029)) (n := 12)
    (lo := (52662357 / 250000000)) (hi := (210649429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405029) = 1/(405029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10732 : Bounds (-210649429 / 1000000000) (-52662357 / 250000000) (Real.log (405029 / 500000)) := by
  have h := reflection_log_10732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10733_neg : (18372431 / 500000000) ≤ -Real.log (240980509159 / 250000000000) ∧
    -Real.log (240980509159 / 250000000000) ≤ (36744863 / 1000000000) := by
  have h := checkLog_sound (w := (9019490841 / 490980509159)) (n := 12)
    (lo := (18372431 / 500000000)) (hi := (36744863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240980509159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240980509159) = 1/(240980509159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10733 : Bounds (-36744863 / 1000000000) (-18372431 / 500000000) (Real.log (240980509159 / 250000000000)) := by
  have h := reflection_log_10733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10734_neg : (36391073 / 1000000000) ≤ -Real.log (241065780559 / 250000000000) ∧
    -Real.log (241065780559 / 250000000000) ≤ (18195537 / 500000000) := by
  have h := checkLog_sound (w := (8934219441 / 491065780559)) (n := 12)
    (lo := (36391073 / 1000000000)) (hi := (18195537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241065780559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241065780559) = 1/(241065780559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10734 : Bounds (-18195537 / 500000000) (-36391073 / 1000000000) (Real.log (241065780559 / 250000000000)) := by
  have h := reflection_log_10734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10735_neg : (76537391 / 200000000) ≤ -Real.log (250000000000 / 366554741429) ∧
    -Real.log (250000000000 / 366554741429) ≤ (95671739 / 250000000) := by
  have h := checkLog_sound (w := (116554741429 / 616554741429)) (n := 12)
    (lo := (76537391 / 200000000)) (hi := (95671739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366554741429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366554741429 / 250000000000) = 1/(250000000000 / 366554741429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10735 : Bounds (76537391 / 200000000) (95671739 / 250000000) (Real.log (366554741429 / 250000000000)) := by
  have h := reflection_log_10735_neg
  have he : Real.log (366554741429 / 250000000000) = -Real.log (250000000000 / 366554741429) := by
    rw [show ((366554741429 / 250000000000) : ℝ) = ((250000000000 / 366554741429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10736_neg : (76910799 / 200000000) ≤ -Real.log (250000000000 / 367239753203) ∧
    -Real.log (250000000000 / 367239753203) ≤ (96138499 / 250000000) := by
  have h := checkLog_sound (w := (117239753203 / 617239753203)) (n := 12)
    (lo := (76910799 / 200000000)) (hi := (96138499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367239753203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367239753203 / 250000000000) = 1/(250000000000 / 367239753203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10736 : Bounds (76910799 / 200000000) (96138499 / 250000000) (Real.log (367239753203 / 250000000000)) := by
  have h := reflection_log_10736_neg
  have he : Real.log (367239753203 / 250000000000) = -Real.log (250000000000 / 367239753203) := by
    rw [show ((367239753203 / 250000000000) : ℝ) = ((250000000000 / 367239753203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10737_neg : (387264981 / 500000000) ≤ -Real.log (250000000000 / 542393026941) ∧
    -Real.log (250000000000 / 542393026941) ≤ (193632491 / 250000000) := by
  have h := checkLog_sound (w := (42393026941 / 1042393026941)) (n := 12)
    (lo := (40691391 / 500000000)) (hi := (81382783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542393026941 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(542393026941 / 500000000000) = 1/(250000000000 / 542393026941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10737 : Bounds (387264981 / 500000000) (193632491 / 250000000) (Real.log (542393026941 / 250000000000)) := by
  have h := reflection_log_10737_neg
  have he : Real.log (542393026941 / 250000000000) = -Real.log (250000000000 / 542393026941) := by
    rw [show ((542393026941 / 250000000000) : ℝ) = ((250000000000 / 542393026941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10738_neg : (388423099 / 500000000) ≤ -Real.log (250000000000 / 543650793651) ∧
    -Real.log (250000000000 / 543650793651) ≤ (3884231 / 5000000) := by
  have h := checkLog_sound (w := (43650793651 / 1043650793651)) (n := 12)
    (lo := (41849509 / 500000000)) (hi := (83699019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543650793651 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543650793651 / 500000000000) = 1/(250000000000 / 543650793651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10738 : Bounds (388423099 / 500000000) (3884231 / 5000000) (Real.log (543650793651 / 250000000000)) := by
  have h := reflection_log_10738_neg
  have he : Real.log (543650793651 / 250000000000) = -Real.log (250000000000 / 543650793651) := by
    rw [show ((543650793651 / 250000000000) : ℝ) = ((250000000000 / 543650793651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10739_neg : (788851 / 2500000) ≤ -Real.log (1000 / 1371) ∧
    -Real.log (1000 / 1371) ≤ (315540401 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2371)) (n := 12)
    (lo := (788851 / 2500000)) (hi := (315540401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1371 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1371 / 1000) = 1/(1000 / 1371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10739 : Bounds (788851 / 2500000) (315540401 / 1000000000) (Real.log (1371 / 1000)) := by
  have h := reflection_log_10739_neg
  have he : Real.log (1371 / 1000) = -Real.log (1000 / 1371) := by
    rw [show ((1371 / 1000) : ℝ) = ((1000 / 1371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10740_neg : (231812011 / 500000000) ≤ -Real.log (629 / 1000) ∧
    -Real.log (629 / 1000) ≤ (463624023 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 1629)) (n := 12)
    (lo := (231812011 / 500000000)) (hi := (463624023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 629) = 1/(629 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10740 : Bounds (-463624023 / 1000000000) (-231812011 / 500000000) (Real.log (629 / 1000)) := by
  have h := reflection_log_10740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10741_neg : (370931 / 1000000000) ≤ -Real.log (1000000 / 1000371) ∧
    -Real.log (1000000 / 1000371) ≤ (92733 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2000371)) (n := 12)
    (lo := (370931 / 1000000000)) (hi := (92733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000371 / 1000000) = 1/(1000000 / 1000371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10741 : Bounds (370931 / 1000000000) (92733 / 250000000) (Real.log (1000371 / 1000000)) := by
  have h := reflection_log_10741_neg
  have he : Real.log (1000371 / 1000000) = -Real.log (1000000 / 1000371) := by
    rw [show ((1000371 / 1000000) : ℝ) = ((1000000 / 1000371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10742_neg : (92767 / 250000000) ≤ -Real.log (999629 / 1000000) ∧
    -Real.log (999629 / 1000000) ≤ (371069 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 1999629)) (n := 12)
    (lo := (92767 / 250000000)) (hi := (371069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999629) = 1/(999629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10742 : Bounds (-371069 / 1000000000) (-92767 / 250000000) (Real.log (999629 / 1000000)) := by
  have h := reflection_log_10742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10743_neg : (21700143 / 125000000) ≤ -Real.log (1000000 / 1189581) ∧
    -Real.log (1000000 / 1189581) ≤ (34720229 / 200000000) := by
  have h := checkLog_sound (w := (189581 / 2189581)) (n := 12)
    (lo := (21700143 / 125000000)) (hi := (34720229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189581 / 1000000) = 1/(1000000 / 1189581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10743 : Bounds (21700143 / 125000000) (34720229 / 200000000) (Real.log (1189581 / 1000000)) := by
  have h := reflection_log_10743_neg
  have he : Real.log (1189581 / 1000000) = -Real.log (1000000 / 1189581) := by
    rw [show ((1189581 / 1000000) : ℝ) = ((1000000 / 1189581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10744_neg : (210203881 / 1000000000) ≤ -Real.log (810419 / 1000000) ∧
    -Real.log (810419 / 1000000) ≤ (105101941 / 500000000) := by
  have h := checkLog_sound (w := (189581 / 1810419)) (n := 12)
    (lo := (210203881 / 1000000000)) (hi := (105101941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810419) = 1/(810419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10744 : Bounds (-105101941 / 500000000) (-210203881 / 1000000000) (Real.log (810419 / 1000000)) := by
  have h := reflection_log_10744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10745_neg : (174358267 / 1000000000) ≤ -Real.log (500000 / 595241) ∧
    -Real.log (500000 / 595241) ≤ (43589567 / 250000000) := by
  have h := checkLog_sound (w := (95241 / 1095241)) (n := 12)
    (lo := (174358267 / 1000000000)) (hi := (43589567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595241 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595241 / 500000) = 1/(500000 / 595241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10745 : Bounds (174358267 / 1000000000) (43589567 / 250000000) (Real.log (595241 / 500000)) := by
  have h := reflection_log_10745_neg
  have he : Real.log (595241 / 500000) = -Real.log (500000 / 595241) := by
    rw [show ((595241 / 500000) : ℝ) = ((500000 / 595241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10746_neg : (21131627 / 100000000) ≤ -Real.log (404759 / 500000) ∧
    -Real.log (404759 / 500000) ≤ (211316271 / 1000000000) := by
  have h := checkLog_sound (w := (95241 / 904759)) (n := 12)
    (lo := (21131627 / 100000000)) (hi := (211316271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404759) = 1/(404759 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10746 : Bounds (-211316271 / 1000000000) (-21131627 / 100000000) (Real.log (404759 / 500000)) := by
  have h := reflection_log_10746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10747_neg : (36958003 / 1000000000) ≤ -Real.log (240929151919 / 250000000000) ∧
    -Real.log (240929151919 / 250000000000) ≤ (9239501 / 250000000) := by
  have h := checkLog_sound (w := (9070848081 / 490929151919)) (n := 12)
    (lo := (36958003 / 1000000000)) (hi := (9239501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240929151919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240929151919) = 1/(240929151919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10747 : Bounds (-9239501 / 250000000) (-36958003 / 1000000000) (Real.log (240929151919 / 250000000000)) := by
  have h := reflection_log_10747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10748_neg : (2287671 / 62500000) ≤ -Real.log (964059044439 / 1000000000000) ∧
    -Real.log (964059044439 / 1000000000000) ≤ (36602737 / 1000000000) := by
  have h := checkLog_sound (w := (35940955561 / 1964059044439)) (n := 12)
    (lo := (2287671 / 62500000)) (hi := (36602737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964059044439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964059044439) = 1/(964059044439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10748 : Bounds (-36602737 / 1000000000) (-2287671 / 62500000) (Real.log (964059044439 / 1000000000000)) := by
  have h := reflection_log_10748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10749_neg : (15352201 / 40000000) ≤ -Real.log (500000000000 / 733929609251) ∧
    -Real.log (500000000000 / 733929609251) ≤ (191902513 / 500000000) := by
  have h := checkLog_sound (w := (233929609251 / 1233929609251)) (n := 12)
    (lo := (15352201 / 40000000)) (hi := (191902513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733929609251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733929609251 / 500000000000) = 1/(500000000000 / 733929609251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10749 : Bounds (15352201 / 40000000) (191902513 / 500000000) (Real.log (733929609251 / 500000000000)) := by
  have h := reflection_log_10749_neg
  have he : Real.log (733929609251 / 500000000000) = -Real.log (500000000000 / 733929609251) := by
    rw [show ((733929609251 / 500000000000) : ℝ) = ((500000000000 / 733929609251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10750_neg : (385674537 / 1000000000) ≤ -Real.log (500000000000 / 735302982763) ∧
    -Real.log (500000000000 / 735302982763) ≤ (192837269 / 500000000) := by
  have h := checkLog_sound (w := (235302982763 / 1235302982763)) (n := 12)
    (lo := (385674537 / 1000000000)) (hi := (192837269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735302982763 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735302982763 / 500000000000) = 1/(500000000000 / 735302982763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10750 : Bounds (385674537 / 1000000000) (192837269 / 500000000) (Real.log (735302982763 / 500000000000)) := by
  have h := reflection_log_10750_neg
  have he : Real.log (735302982763 / 500000000000) = -Real.log (500000000000 / 735302982763) := by
    rw [show ((735302982763 / 500000000000) : ℝ) = ((500000000000 / 735302982763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10751_neg : (388423099 / 500000000) ≤ -Real.log (500000000000 / 1087301587301) ∧
    -Real.log (500000000000 / 1087301587301) ≤ (3884231 / 5000000) := by
  have h := checkLog_sound (w := (87301587301 / 2087301587301)) (n := 12)
    (lo := (41849509 / 500000000)) (hi := (83699019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087301587301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1087301587301 / 1000000000000) = 1/(500000000000 / 1087301587301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10751 : Bounds (388423099 / 500000000) (3884231 / 5000000) (Real.log (1087301587301 / 500000000000)) := by
  have h := reflection_log_10751_neg
  have he : Real.log (1087301587301 / 500000000000) = -Real.log (500000000000 / 1087301587301) := by
    rw [show ((1087301587301 / 500000000000) : ℝ) = ((500000000000 / 1087301587301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
