import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15168_neg : (65155557 / 125000000) ≤ -Real.log (593781153391 / 1000000000000) ∧
    -Real.log (593781153391 / 1000000000000) ≤ (521244457 / 1000000000) := by
  have h := checkLog_sound (w := (406218846609 / 1593781153391)) (n := 12)
    (lo := (65155557 / 125000000)) (hi := (521244457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 593781153391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 593781153391) = 1/(593781153391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15168 : Bounds (-521244457 / 1000000000) (-65155557 / 125000000) (Real.log (593781153391 / 1000000000000)) := by
  have h := reflection_log_15168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15169_neg : (753703141 / 500000000) ≤ -Real.log (250000000000 / 1128751237429) ∧
    -Real.log (250000000000 / 1128751237429) ≤ (301481257 / 200000000) := by
  have h := checkLog_sound (w := (128751237429 / 2128751237429)) (n := 12)
    (lo := (60555961 / 500000000)) (hi := (121111923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128751237429 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1128751237429 / 1000000000000) = 1/(250000000000 / 1128751237429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15169 : Bounds (753703141 / 500000000) (301481257 / 200000000) (Real.log (1128751237429 / 250000000000)) := by
  have h := reflection_log_15169_neg
  have he : Real.log (1128751237429 / 250000000000) = -Real.log (250000000000 / 1128751237429) := by
    rw [show ((1128751237429 / 250000000000) : ℝ) = ((250000000000 / 1128751237429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15170_neg : (757161527 / 500000000) ≤ -Real.log (500000000000 / 2273171232231) ∧
    -Real.log (500000000000 / 2273171232231) ≤ (1514323057 / 1000000000) := by
  have h := checkLog_sound (w := (273171232231 / 4273171232231)) (n := 12)
    (lo := (64014347 / 500000000)) (hi := (25605739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2273171232231 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2273171232231 / 2000000000000) = 1/(500000000000 / 2273171232231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15170 : Bounds (757161527 / 500000000) (1514323057 / 1000000000) (Real.log (2273171232231 / 500000000000)) := by
  have h := reflection_log_15170_neg
  have he : Real.log (2273171232231 / 500000000000) = -Real.log (500000000000 / 2273171232231) := by
    rw [show ((2273171232231 / 500000000000) : ℝ) = ((500000000000 / 2273171232231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15171_neg : (5029431881 / 1000000000) ≤ -Real.log (125000000000 / 19105769230769) ∧
    -Real.log (125000000000 / 19105769230769) ≤ (5029431889 / 1000000000) := by
  have h := checkLog_sound (w := (3105769230769 / 35105769230769)) (n := 12)
    (lo := (177401621 / 1000000000)) (hi := (88700811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19105769230769 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(19105769230769 / 16000000000000) = 1/(125000000000 / 19105769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15171 : Bounds (5029431881 / 1000000000) (5029431889 / 1000000000) (Real.log (19105769230769 / 125000000000)) := by
  have h := reflection_log_15171_neg
  have he : Real.log (19105769230769 / 125000000000) = -Real.log (125000000000 / 19105769230769) := by
    rw [show ((19105769230769 / 125000000000) : ℝ) = ((125000000000 / 19105769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15172_neg : (5109977733 / 1000000000) ≤ -Real.log (250000000000 / 41416666666667) ∧
    -Real.log (250000000000 / 41416666666667) ≤ (5109977741 / 1000000000) := by
  have h := checkLog_sound (w := (9416666666667 / 73416666666667)) (n := 12)
    (lo := (257947473 / 1000000000)) (hi := (128973737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41416666666667 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(41416666666667 / 32000000000000) = 1/(250000000000 / 41416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15172 : Bounds (5109977733 / 1000000000) (5109977741 / 1000000000) (Real.log (41416666666667 / 250000000000)) := by
  have h := reflection_log_15172_neg
  have he : Real.log (41416666666667 / 250000000000) = -Real.log (250000000000 / 41416666666667) := by
    rw [show ((41416666666667 / 250000000000) : ℝ) = ((250000000000 / 41416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15173_neg : (687631999 / 1000000000) ≤ -Real.log (1000 / 1989) ∧
    -Real.log (1000 / 1989) ≤ (42977 / 62500) := by
  have h := checkLog_sound (w := (989 / 2989)) (n := 12)
    (lo := (687631999 / 1000000000)) (hi := (42977 / 62500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1989 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1989 / 1000) = 1/(1000 / 1989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15173 : Bounds (687631999 / 1000000000) (42977 / 62500) (Real.log (1989 / 1000)) := by
  have h := reflection_log_15173_neg
  have he : Real.log (1989 / 1000) = -Real.log (1000 / 1989) := by
    rw [show ((1989 / 1000) : ℝ) = ((1000 / 1989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15174_neg : (2254930001 / 500000000) ≤ -Real.log (11 / 1000) ∧
    -Real.log (11 / 1000) ≤ (4509860009 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 88) = 1/(11 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15174 : Bounds (-4509860009 / 1000000000) (-2254930001 / 500000000) (Real.log (11 / 1000)) := by
  have h := reflection_log_15174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15175_neg : (988511 / 1000000000) ≤ -Real.log (1000000 / 1000989) ∧
    -Real.log (1000000 / 1000989) ≤ (30891 / 31250000) := by
  have h := checkLog_sound (w := (989 / 2000989)) (n := 12)
    (lo := (988511 / 1000000000)) (hi := (30891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000989 / 1000000) = 1/(1000000 / 1000989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15175 : Bounds (988511 / 1000000000) (30891 / 31250000) (Real.log (1000989 / 1000000)) := by
  have h := reflection_log_15175_neg
  have he : Real.log (1000989 / 1000000) = -Real.log (1000000 / 1000989) := by
    rw [show ((1000989 / 1000000) : ℝ) = ((1000000 / 1000989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15176_neg : (989489 / 1000000000) ≤ -Real.log (999011 / 1000000) ∧
    -Real.log (999011 / 1000000) ≤ (98949 / 100000000) := by
  have h := checkLog_sound (w := (989 / 1999011)) (n := 12)
    (lo := (989489 / 1000000000)) (hi := (98949 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999011) = 1/(999011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15176 : Bounds (-98949 / 100000000) (-989489 / 1000000000) (Real.log (999011 / 1000000)) := by
  have h := reflection_log_15176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15177_neg : (9878907 / 20000000) ≤ -Real.log (1000000 / 1638769) ∧
    -Real.log (1000000 / 1638769) ≤ (493945351 / 1000000000) := by
  have h := checkLog_sound (w := (638769 / 2638769)) (n := 12)
    (lo := (9878907 / 20000000)) (hi := (493945351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638769 / 1000000) = 1/(1000000 / 1638769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15177 : Bounds (9878907 / 20000000) (493945351 / 1000000000) (Real.log (1638769 / 1000000)) := by
  have h := reflection_log_15177_neg
  have he : Real.log (1638769 / 1000000) = -Real.log (1000000 / 1638769) := by
    rw [show ((1638769 / 1000000) : ℝ) = ((1000000 / 1638769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15178_neg : (203647527 / 200000000) ≤ -Real.log (361231 / 1000000) ∧
    -Real.log (361231 / 1000000) ≤ (1018237637 / 1000000000) := by
  have h := checkLog_sound (w := (138769 / 861231)) (n := 12)
    (lo := (65018091 / 200000000)) (hi := (40636307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 361231) = 1/(361231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15178 : Bounds (-1018237637 / 1000000000) (-203647527 / 200000000) (Real.log (361231 / 1000000)) := by
  have h := reflection_log_15178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15179_neg : (123801467 / 250000000) ≤ -Real.log (250000 / 410209) ∧
    -Real.log (250000 / 410209) ≤ (495205869 / 1000000000) := by
  have h := checkLog_sound (w := (160209 / 660209)) (n := 12)
    (lo := (123801467 / 250000000)) (hi := (495205869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410209 / 250000) = 1/(250000 / 410209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15179 : Bounds (123801467 / 250000000) (495205869 / 1000000000) (Real.log (410209 / 250000)) := by
  have h := reflection_log_15179_neg
  have he : Real.log (410209 / 250000) = -Real.log (250000 / 410209) := by
    rw [show ((410209 / 250000) : ℝ) = ((250000 / 410209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15180_neg : (1023976169 / 1000000000) ≤ -Real.log (89791 / 250000) ∧
    -Real.log (89791 / 250000) ≤ (1023976171 / 1000000000) := by
  have h := checkLog_sound (w := (35209 / 214791)) (n := 12)
    (lo := (330828989 / 1000000000)) (hi := (33082899 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 89791) = 1/(89791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15180 : Bounds (-1023976171 / 1000000000) (-1023976169 / 1000000000) (Real.log (89791 / 250000)) := by
  have h := reflection_log_15180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15181_neg : (264385151 / 500000000) ≤ -Real.log (36833076319 / 62500000000) ∧
    -Real.log (36833076319 / 62500000000) ≤ (528770303 / 1000000000) := by
  have h := checkLog_sound (w := (25666923681 / 99333076319)) (n := 12)
    (lo := (264385151 / 500000000)) (hi := (528770303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36833076319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36833076319) = 1/(36833076319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15181 : Bounds (-528770303 / 1000000000) (-264385151 / 500000000) (Real.log (36833076319 / 62500000000)) := by
  have h := reflection_log_15181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15182_neg : (104858457 / 200000000) ≤ -Real.log (591974164639 / 1000000000000) ∧
    -Real.log (591974164639 / 1000000000000) ≤ (262146143 / 500000000) := by
  have h := checkLog_sound (w := (408025835361 / 1591974164639)) (n := 12)
    (lo := (104858457 / 200000000)) (hi := (262146143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 591974164639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 591974164639) = 1/(591974164639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15182 : Bounds (-262146143 / 500000000) (-104858457 / 200000000) (Real.log (591974164639 / 1000000000000)) := by
  have h := reflection_log_15182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15183_neg : (302436597 / 200000000) ≤ -Real.log (500000000000 / 2268311689749) ∧
    -Real.log (500000000000 / 2268311689749) ≤ (378045747 / 250000000) := by
  have h := checkLog_sound (w := (268311689749 / 4268311689749)) (n := 12)
    (lo := (1007109 / 8000000)) (hi := (62944313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2268311689749 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2268311689749 / 2000000000000) = 1/(500000000000 / 2268311689749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15183 : Bounds (302436597 / 200000000) (378045747 / 250000000) (Real.log (2268311689749 / 500000000000)) := by
  have h := reflection_log_15183_neg
  have he : Real.log (2268311689749 / 500000000000) = -Real.log (500000000000 / 2268311689749) := by
    rw [show ((2268311689749 / 500000000000) : ℝ) = ((500000000000 / 2268311689749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15184_neg : (1519182037 / 1000000000) ≤ -Real.log (15625000000 / 71382606553) ∧
    -Real.log (15625000000 / 71382606553) ≤ (37979551 / 25000000) := by
  have h := checkLog_sound (w := (8882606553 / 133882606553)) (n := 12)
    (lo := (132887677 / 1000000000)) (hi := (66443839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71382606553 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(71382606553 / 62500000000) = 1/(15625000000 / 71382606553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15184 : Bounds (1519182037 / 1000000000) (37979551 / 25000000) (Real.log (71382606553 / 15625000000)) := by
  have h := reflection_log_15184_neg
  have he : Real.log (71382606553 / 15625000000) = -Real.log (15625000000 / 71382606553) := by
    rw [show ((71382606553 / 15625000000) : ℝ) = ((15625000000 / 71382606553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15185_neg : (5109977733 / 1000000000) ≤ -Real.log (500000000000 / 82833333333333) ∧
    -Real.log (500000000000 / 82833333333333) ≤ (5109977741 / 1000000000) := by
  have h := checkLog_sound (w := (18833333333333 / 146833333333333)) (n := 12)
    (lo := (257947473 / 1000000000)) (hi := (128973737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82833333333333 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(82833333333333 / 64000000000000) = 1/(500000000000 / 82833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15185 : Bounds (5109977733 / 1000000000) (5109977741 / 1000000000) (Real.log (82833333333333 / 500000000000)) := by
  have h := reflection_log_15185_neg
  have he : Real.log (82833333333333 / 500000000000) = -Real.log (500000000000 / 82833333333333) := by
    rw [show ((82833333333333 / 500000000000) : ℝ) = ((500000000000 / 82833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15186_neg : (2598746001 / 500000000) ≤ -Real.log (500000000000 / 90409090909091) ∧
    -Real.log (500000000000 / 90409090909091) ≤ (519749201 / 100000000) := by
  have h := checkLog_sound (w := (26409090909091 / 154409090909091)) (n := 12)
    (lo := (172730871 / 500000000)) (hi := (345461743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90409090909091 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(90409090909091 / 64000000000000) = 1/(500000000000 / 90409090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15186 : Bounds (2598746001 / 500000000) (519749201 / 100000000) (Real.log (90409090909091 / 500000000000)) := by
  have h := reflection_log_15186_neg
  have he : Real.log (90409090909091 / 500000000000) = -Real.log (500000000000 / 90409090909091) := by
    rw [show ((90409090909091 / 500000000000) : ℝ) = ((500000000000 / 90409090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15187_neg : (344067319 / 500000000) ≤ -Real.log (100 / 199) ∧
    -Real.log (100 / 199) ≤ (688134639 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 299)) (n := 12)
    (lo := (344067319 / 500000000)) (hi := (688134639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 100) = 1/(100 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15187 : Bounds (344067319 / 500000000) (688134639 / 1000000000) (Real.log (199 / 100)) := by
  have h := reflection_log_15187_neg
  have he : Real.log (199 / 100) = -Real.log (100 / 199) := by
    rw [show ((199 / 100) : ℝ) = ((100 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15188_neg : (2302585091 / 500000000) ≤ -Real.log (1 / 100) ∧
    -Real.log (1 / 100) ≤ (4605170189 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25 / 16) = 1/(1 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15188 : Bounds (-4605170189 / 1000000000) (-2302585091 / 500000000) (Real.log (1 / 100)) := by
  have h := reflection_log_15188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15189_neg : (98951 / 100000000) ≤ -Real.log (100000 / 100099) ∧
    -Real.log (100000 / 100099) ≤ (989511 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 200099)) (n := 12)
    (lo := (98951 / 100000000)) (hi := (989511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100099 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100099 / 100000) = 1/(100000 / 100099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15189 : Bounds (98951 / 100000000) (989511 / 1000000000) (Real.log (100099 / 100000)) := by
  have h := reflection_log_15189_neg
  have he : Real.log (100099 / 100000) = -Real.log (100000 / 100099) := by
    rw [show ((100099 / 100000) : ℝ) = ((100000 / 100099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15190_neg : (99049 / 100000000) ≤ -Real.log (99901 / 100000) ∧
    -Real.log (99901 / 100000) ≤ (990491 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 199901)) (n := 12)
    (lo := (99049 / 100000000)) (hi := (990491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99901) = 1/(99901 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15190 : Bounds (-990491 / 1000000000) (-99049 / 100000000) (Real.log (99901 / 100000)) := by
  have h := reflection_log_15190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15191_neg : (247410617 / 500000000) ≤ -Real.log (200000 / 328041) ∧
    -Real.log (200000 / 328041) ≤ (98964247 / 200000000) := by
  have h := checkLog_sound (w := (128041 / 528041)) (n := 12)
    (lo := (247410617 / 500000000)) (hi := (98964247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328041 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328041 / 200000) = 1/(200000 / 328041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15191 : Bounds (247410617 / 500000000) (98964247 / 200000000) (Real.log (328041 / 200000)) := by
  have h := reflection_log_15191_neg
  have he : Real.log (328041 / 200000) = -Real.log (200000 / 328041) := by
    rw [show ((328041 / 200000) : ℝ) = ((200000 / 328041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15192_neg : (1022220853 / 1000000000) ≤ -Real.log (71959 / 200000) ∧
    -Real.log (71959 / 200000) ≤ (204444171 / 200000000) := by
  have h := checkLog_sound (w := (28041 / 171959)) (n := 12)
    (lo := (329073673 / 1000000000)) (hi := (164536837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71959) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71959) = 1/(71959 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15192 : Bounds (-204444171 / 200000000) (-1022220853 / 1000000000) (Real.log (71959 / 200000)) := by
  have h := reflection_log_15192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15193_neg : (248046109 / 500000000) ≤ -Real.log (1000000 / 1642291) ∧
    -Real.log (1000000 / 1642291) ≤ (496092219 / 1000000000) := by
  have h := checkLog_sound (w := (642291 / 2642291)) (n := 12)
    (lo := (248046109 / 500000000)) (hi := (496092219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642291 / 1000000) = 1/(1000000 / 1642291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15193 : Bounds (248046109 / 500000000) (496092219 / 1000000000) (Real.log (1642291 / 1000000)) := by
  have h := reflection_log_15193_neg
  have he : Real.log (1642291 / 1000000) = -Real.log (1000000 / 1642291) := by
    rw [show ((1642291 / 1000000) : ℝ) = ((1000000 / 1642291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15194_neg : (1028035471 / 1000000000) ≤ -Real.log (357709 / 1000000) ∧
    -Real.log (357709 / 1000000) ≤ (1028035473 / 1000000000) := by
  have h := checkLog_sound (w := (142291 / 857709)) (n := 12)
    (lo := (334888291 / 1000000000)) (hi := (83722073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357709) = 1/(357709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15194 : Bounds (-1028035473 / 1000000000) (-1028035471 / 1000000000) (Real.log (357709 / 1000000)) := by
  have h := reflection_log_15194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15195_neg : (265971627 / 500000000) ≤ -Real.log (587462271319 / 1000000000000) ∧
    -Real.log (587462271319 / 1000000000000) ≤ (106388651 / 200000000) := by
  have h := checkLog_sound (w := (412537728681 / 1587462271319)) (n := 12)
    (lo := (265971627 / 500000000)) (hi := (106388651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 587462271319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 587462271319) = 1/(587462271319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15195 : Bounds (-106388651 / 200000000) (-265971627 / 500000000) (Real.log (587462271319 / 1000000000000)) := by
  have h := reflection_log_15195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15196_neg : (26369981 / 50000000) ≤ -Real.log (23605502319 / 40000000000) ∧
    -Real.log (23605502319 / 40000000000) ≤ (527399621 / 1000000000) := by
  have h := checkLog_sound (w := (16394497681 / 63605502319)) (n := 12)
    (lo := (26369981 / 50000000)) (hi := (527399621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23605502319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23605502319) = 1/(23605502319 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15196 : Bounds (-527399621 / 1000000000) (-26369981 / 50000000) (Real.log (23605502319 / 40000000000)) := by
  have h := reflection_log_15196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15197_neg : (1517042087 / 1000000000) ≤ -Real.log (125000000000 / 569840117289) ∧
    -Real.log (125000000000 / 569840117289) ≤ (151704209 / 100000000) := by
  have h := checkLog_sound (w := (69840117289 / 1069840117289)) (n := 12)
    (lo := (130747727 / 1000000000)) (hi := (8171733 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569840117289 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(569840117289 / 500000000000) = 1/(125000000000 / 569840117289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15197 : Bounds (1517042087 / 1000000000) (151704209 / 100000000) (Real.log (569840117289 / 125000000000)) := by
  have h := reflection_log_15197_neg
  have he : Real.log (569840117289 / 125000000000) = -Real.log (125000000000 / 569840117289) := by
    rw [show ((569840117289 / 125000000000) : ℝ) = ((125000000000 / 569840117289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15198_neg : (1524127689 / 1000000000) ≤ -Real.log (50000000000 / 229556846487) ∧
    -Real.log (50000000000 / 229556846487) ≤ (381031923 / 250000000) := by
  have h := checkLog_sound (w := (29556846487 / 429556846487)) (n := 12)
    (lo := (137833329 / 1000000000)) (hi := (13783333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229556846487 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(229556846487 / 200000000000) = 1/(50000000000 / 229556846487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15198 : Bounds (1524127689 / 1000000000) (381031923 / 250000000) (Real.log (229556846487 / 50000000000)) := by
  have h := reflection_log_15198_neg
  have he : Real.log (229556846487 / 50000000000) = -Real.log (50000000000 / 229556846487) := by
    rw [show ((229556846487 / 50000000000) : ℝ) = ((50000000000 / 229556846487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15199_neg : (2598746001 / 500000000) ≤ -Real.log (50000000000 / 9040909090909) ∧
    -Real.log (50000000000 / 9040909090909) ≤ (519749201 / 100000000) := by
  have h := checkLog_sound (w := (2640909090909 / 15440909090909)) (n := 12)
    (lo := (172730871 / 500000000)) (hi := (345461743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9040909090909 / 6400000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(9040909090909 / 6400000000000) = 1/(50000000000 / 9040909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15199 : Bounds (2598746001 / 500000000) (519749201 / 100000000) (Real.log (9040909090909 / 50000000000)) := by
  have h := reflection_log_15199_neg
  have he : Real.log (9040909090909 / 50000000000) = -Real.log (50000000000 / 9040909090909) := by
    rw [show ((9040909090909 / 50000000000) : ℝ) = ((50000000000 / 9040909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15200_neg : (264665241 / 50000000) ≤ -Real.log (1 / 199) ∧
    -Real.log (1 / 199) ≤ (1323326207 / 250000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(199 / 128) = 1/(1 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15200 : Bounds (264665241 / 50000000) (1323326207 / 250000000) (Real.log (199 / 1)) := by
  have h := reflection_log_15200_neg
  have he : Real.log (199 / 1) = -Real.log (1 / 199) := by
    rw [show ((199 / 1) : ℝ) = ((1 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15201_neg : (5376837 / 7812500) ≤ -Real.log (5000 / 9951) ∧
    -Real.log (5000 / 9951) ≤ (688235137 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 14951)) (n := 12)
    (lo := (5376837 / 7812500)) (hi := (688235137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9951 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9951 / 5000) = 1/(5000 / 9951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15201 : Bounds (5376837 / 7812500) (688235137 / 1000000000) (Real.log (9951 / 5000)) := by
  have h := reflection_log_15201_neg
  have he : Real.log (9951 / 5000) = -Real.log (5000 / 9951) := by
    rw [show ((9951 / 5000) : ℝ) = ((5000 / 9951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15202_neg : (4625372889 / 1000000000) ≤ -Real.log (49 / 5000) ∧
    -Real.log (49 / 5000) ≤ (144542903 / 31250000) := by
  have h := checkLog_sound (w := (233 / 1017)) (n := 12)
    (lo := (466489809 / 1000000000)) (hi := (46648981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 392) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 392) = 1/(49 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15202 : Bounds (-144542903 / 31250000) (-4625372889 / 1000000000) (Real.log (49 / 5000)) := by
  have h := reflection_log_15202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15203_neg : (98971 / 100000000) ≤ -Real.log (5000000 / 5004951) ∧
    -Real.log (5000000 / 5004951) ≤ (989711 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 10004951)) (n := 12)
    (lo := (98971 / 100000000)) (hi := (989711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004951 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004951 / 5000000) = 1/(5000000 / 5004951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15203 : Bounds (98971 / 100000000) (989711 / 1000000000) (Real.log (5004951 / 5000000)) := by
  have h := reflection_log_15203_neg
  have he : Real.log (5004951 / 5000000) = -Real.log (5000000 / 5004951) := by
    rw [show ((5004951 / 5000000) : ℝ) = ((5000000 / 5004951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15204_neg : (99069 / 100000000) ≤ -Real.log (4995049 / 5000000) ∧
    -Real.log (4995049 / 5000000) ≤ (990691 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 9995049)) (n := 12)
    (lo := (99069 / 100000000)) (hi := (990691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995049) = 1/(4995049 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15204 : Bounds (-990691 / 1000000000) (-99069 / 100000000) (Real.log (4995049 / 5000000)) := by
  have h := reflection_log_15204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15205_neg : (247854267 / 500000000) ≤ -Real.log (1000000 / 1641661) ∧
    -Real.log (1000000 / 1641661) ≤ (99141707 / 200000000) := by
  have h := checkLog_sound (w := (641661 / 2641661)) (n := 12)
    (lo := (247854267 / 500000000)) (hi := (99141707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641661 / 1000000) = 1/(1000000 / 1641661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15205 : Bounds (247854267 / 500000000) (99141707 / 200000000) (Real.log (1641661 / 1000000)) := by
  have h := reflection_log_15205_neg
  have he : Real.log (1641661 / 1000000) = -Real.log (1000000 / 1641661) := by
    rw [show ((1641661 / 1000000) : ℝ) = ((1000000 / 1641661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15206_neg : (256568953 / 250000000) ≤ -Real.log (358339 / 1000000) ∧
    -Real.log (358339 / 1000000) ≤ (513137907 / 500000000) := by
  have h := checkLog_sound (w := (141661 / 858339)) (n := 12)
    (lo := (41641079 / 125000000)) (hi := (333128633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 358339) = 1/(358339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15206 : Bounds (-513137907 / 500000000) (-256568953 / 250000000) (Real.log (358339 / 1000000)) := by
  have h := reflection_log_15206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15207_neg : (24813561 / 50000000) ≤ -Real.log (200000 / 328517) ∧
    -Real.log (200000 / 328517) ≤ (496271221 / 1000000000) := by
  have h := checkLog_sound (w := (128517 / 528517)) (n := 12)
    (lo := (24813561 / 50000000)) (hi := (496271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328517 / 200000) = 1/(200000 / 328517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15207 : Bounds (24813561 / 50000000) (496271221 / 1000000000) (Real.log (328517 / 200000)) := by
  have h := reflection_log_15207_neg
  have he : Real.log (328517 / 200000) = -Real.log (200000 / 328517) := by
    rw [show ((328517 / 200000) : ℝ) = ((200000 / 328517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15208_neg : (514428853 / 500000000) ≤ -Real.log (71483 / 200000) ∧
    -Real.log (71483 / 200000) ≤ (257214427 / 250000000) := by
  have h := checkLog_sound (w := (28517 / 171483)) (n := 12)
    (lo := (167855263 / 500000000)) (hi := (335710527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71483) = 1/(71483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15208 : Bounds (-257214427 / 250000000) (-514428853 / 500000000) (Real.log (71483 / 200000)) := by
  have h := reflection_log_15208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15209_neg : (266293243 / 500000000) ≤ -Real.log (23483380711 / 40000000000) ∧
    -Real.log (23483380711 / 40000000000) ≤ (532586487 / 1000000000) := by
  have h := checkLog_sound (w := (16516619289 / 63483380711)) (n := 12)
    (lo := (266293243 / 500000000)) (hi := (532586487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23483380711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23483380711) = 1/(23483380711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15209 : Bounds (-532586487 / 1000000000) (-266293243 / 500000000) (Real.log (23483380711 / 40000000000)) := by
  have h := reflection_log_15209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15210_neg : (530567279 / 1000000000) ≤ -Real.log (588271161079 / 1000000000000) ∧
    -Real.log (588271161079 / 1000000000000) ≤ (6632091 / 12500000) := by
  have h := checkLog_sound (w := (411728838921 / 1588271161079)) (n := 12)
    (lo := (530567279 / 1000000000)) (hi := (6632091 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 588271161079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 588271161079) = 1/(588271161079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15210 : Bounds (-6632091 / 12500000) (-530567279 / 1000000000) (Real.log (588271161079 / 1000000000000)) := by
  have h := reflection_log_15210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15211_neg : (760992173 / 500000000) ≤ -Real.log (500000000000 / 2290653543153) ∧
    -Real.log (500000000000 / 2290653543153) ≤ (1521984349 / 1000000000) := by
  have h := checkLog_sound (w := (290653543153 / 4290653543153)) (n := 12)
    (lo := (67844993 / 500000000)) (hi := (135689987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2290653543153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2290653543153 / 2000000000000) = 1/(500000000000 / 2290653543153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15211 : Bounds (760992173 / 500000000) (1521984349 / 1000000000) (Real.log (2290653543153 / 500000000000)) := by
  have h := reflection_log_15211_neg
  have he : Real.log (2290653543153 / 500000000000) = -Real.log (500000000000 / 2290653543153) := by
    rw [show ((2290653543153 / 500000000000) : ℝ) = ((500000000000 / 2290653543153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15212_neg : (762564463 / 500000000) ≤ -Real.log (250000000000 / 1148934012283) ∧
    -Real.log (250000000000 / 1148934012283) ≤ (1525128929 / 1000000000) := by
  have h := checkLog_sound (w := (148934012283 / 2148934012283)) (n := 12)
    (lo := (69417283 / 500000000)) (hi := (138834567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148934012283 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1148934012283 / 1000000000000) = 1/(250000000000 / 1148934012283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15212 : Bounds (762564463 / 500000000) (1525128929 / 1000000000) (Real.log (1148934012283 / 250000000000)) := by
  have h := reflection_log_15212_neg
  have he : Real.log (1148934012283 / 250000000000) = -Real.log (250000000000 / 1148934012283) := by
    rw [show ((1148934012283 / 250000000000) : ℝ) = ((250000000000 / 1148934012283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15213_neg : (212544321 / 40000000) ≤ -Real.log (500000000000 / 101540816326531) ∧
    -Real.log (500000000000 / 101540816326531) ≤ (5313608033 / 1000000000) := by
  have h := checkLog_sound (w := (37540816326531 / 165540816326531)) (n := 12)
    (lo := (92315553 / 200000000)) (hi := (230788883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101540816326531 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(101540816326531 / 64000000000000) = 1/(500000000000 / 101540816326531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15213 : Bounds (212544321 / 40000000) (5313608033 / 1000000000) (Real.log (101540816326531 / 500000000000)) := by
  have h := reflection_log_15213_neg
  have he : Real.log (101540816326531 / 500000000000) = -Real.log (500000000000 / 101540816326531) := by
    rw [show ((101540816326531 / 500000000000) : ℝ) = ((500000000000 / 101540816326531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15214_neg : (688335623 / 1000000000) ≤ -Real.log (625 / 1244) ∧
    -Real.log (625 / 1244) ≤ (86041953 / 125000000) := by
  have h := checkLog_sound (w := (619 / 1869)) (n := 12)
    (lo := (688335623 / 1000000000)) (hi := (86041953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244 / 625) = 1/(625 / 1244) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15214 : Bounds (688335623 / 1000000000) (86041953 / 125000000) (Real.log (1244 / 625)) := by
  have h := reflection_log_15214_neg
  have he : Real.log (1244 / 625) = -Real.log (625 / 1244) := by
    rw [show ((1244 / 625) : ℝ) = ((625 / 1244) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15215_neg : (4645992177 / 1000000000) ≤ -Real.log (6 / 625) ∧
    -Real.log (6 / 625) ≤ (580749023 / 125000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 384) = 1/(6 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15215 : Bounds (-580749023 / 125000000) (-4645992177 / 1000000000) (Real.log (6 / 625)) := by
  have h := reflection_log_15215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15216_neg : (989909 / 1000000000) ≤ -Real.log (625000 / 625619) ∧
    -Real.log (625000 / 625619) ≤ (98991 / 100000000) := by
  have h := checkLog_sound (w := (619 / 1250619)) (n := 12)
    (lo := (989909 / 1000000000)) (hi := (98991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625619 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625619 / 625000) = 1/(625000 / 625619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15216 : Bounds (989909 / 1000000000) (98991 / 100000000) (Real.log (625619 / 625000)) := by
  have h := reflection_log_15216_neg
  have he : Real.log (625619 / 625000) = -Real.log (625000 / 625619) := by
    rw [show ((625619 / 625000) : ℝ) = ((625000 / 625619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15217_neg : (99089 / 100000000) ≤ -Real.log (624381 / 625000) ∧
    -Real.log (624381 / 625000) ≤ (990891 / 1000000000) := by
  have h := checkLog_sound (w := (619 / 1249381)) (n := 12)
    (lo := (99089 / 100000000)) (hi := (990891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624381) = 1/(624381 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15217 : Bounds (-990891 / 1000000000) (-99089 / 100000000) (Real.log (624381 / 625000)) := by
  have h := reflection_log_15217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15218_neg : (99177521 / 200000000) ≤ -Real.log (200000 / 328391) ∧
    -Real.log (200000 / 328391) ≤ (247943803 / 500000000) := by
  have h := checkLog_sound (w := (128391 / 528391)) (n := 12)
    (lo := (99177521 / 200000000)) (hi := (247943803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328391 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328391 / 200000) = 1/(200000 / 328391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15218 : Bounds (99177521 / 200000000) (247943803 / 500000000) (Real.log (328391 / 200000)) := by
  have h := reflection_log_15218_neg
  have he : Real.log (328391 / 200000) = -Real.log (200000 / 328391) := by
    rw [show ((328391 / 200000) : ℝ) = ((200000 / 328391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15219_neg : (1027096601 / 1000000000) ≤ -Real.log (71609 / 200000) ∧
    -Real.log (71609 / 200000) ≤ (1027096603 / 1000000000) := by
  have h := checkLog_sound (w := (28391 / 171609)) (n := 12)
    (lo := (333949421 / 1000000000)) (hi := (166974711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71609) = 1/(71609 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15219 : Bounds (-1027096603 / 1000000000) (-1027096601 / 1000000000) (Real.log (71609 / 200000)) := by
  have h := reflection_log_15219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15220_neg : (496450799 / 1000000000) ≤ -Real.log (3125 / 5134) ∧
    -Real.log (3125 / 5134) ≤ (1241127 / 2500000) := by
  have h := checkLog_sound (w := (2009 / 8259)) (n := 12)
    (lo := (496450799 / 1000000000)) (hi := (1241127 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5134 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5134 / 3125) = 1/(3125 / 5134) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15220 : Bounds (496450799 / 1000000000) (1241127 / 2500000) (Real.log (5134 / 3125)) := by
  have h := reflection_log_15220_neg
  have he : Real.log (5134 / 3125) = -Real.log (3125 / 5134) := by
    rw [show ((5134 / 3125) : ℝ) = ((3125 / 5134) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15221_neg : (514841709 / 500000000) ≤ -Real.log (1116 / 3125) ∧
    -Real.log (1116 / 3125) ≤ (51484171 / 50000000) := by
  have h := checkLog_sound (w := (893 / 5357)) (n := 12)
    (lo := (168268119 / 500000000)) (hi := (336536239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2232) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2232) = 1/(1116 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15221 : Bounds (-51484171 / 50000000) (-514841709 / 500000000) (Real.log (1116 / 3125)) := by
  have h := reflection_log_15221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15222_neg : (533232619 / 1000000000) ≤ -Real.log (5729544 / 9765625) ∧
    -Real.log (5729544 / 9765625) ≤ (26661631 / 50000000) := by
  have h := checkLog_sound (w := (4036081 / 15495169)) (n := 12)
    (lo := (533232619 / 1000000000)) (hi := (26661631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 5729544) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 5729544) = 1/(5729544 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15222 : Bounds (-26661631 / 50000000) (-533232619 / 1000000000) (Real.log (5729544 / 9765625)) := by
  have h := reflection_log_15222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15223_neg : (531208997 / 1000000000) ≤ -Real.log (23515751119 / 40000000000) ∧
    -Real.log (23515751119 / 40000000000) ≤ (265604499 / 500000000) := by
  have h := checkLog_sound (w := (16484248881 / 63515751119)) (n := 12)
    (lo := (531208997 / 1000000000)) (hi := (265604499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23515751119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23515751119) = 1/(23515751119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15223 : Bounds (-265604499 / 500000000) (-531208997 / 1000000000) (Real.log (23515751119 / 40000000000)) := by
  have h := reflection_log_15223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15224_neg : (761492103 / 500000000) ≤ -Real.log (500000000000 / 2292945020877) ∧
    -Real.log (500000000000 / 2292945020877) ≤ (1522984209 / 1000000000) := by
  have h := checkLog_sound (w := (292945020877 / 4292945020877)) (n := 12)
    (lo := (68344923 / 500000000)) (hi := (136689847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2292945020877 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2292945020877 / 2000000000000) = 1/(500000000000 / 2292945020877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15224 : Bounds (761492103 / 500000000) (1522984209 / 1000000000) (Real.log (2292945020877 / 500000000000)) := by
  have h := reflection_log_15224_neg
  have he : Real.log (2292945020877 / 500000000000) = -Real.log (500000000000 / 2292945020877) := by
    rw [show ((2292945020877 / 500000000000) : ℝ) = ((500000000000 / 2292945020877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15225_neg : (1526134217 / 1000000000) ≤ -Real.log (50000000000 / 230017921147) ∧
    -Real.log (50000000000 / 230017921147) ≤ (76306711 / 50000000) := by
  have h := checkLog_sound (w := (30017921147 / 430017921147)) (n := 12)
    (lo := (139839857 / 1000000000)) (hi := (69919929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230017921147 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(230017921147 / 200000000000) = 1/(50000000000 / 230017921147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15225 : Bounds (1526134217 / 1000000000) (76306711 / 50000000) (Real.log (230017921147 / 50000000000)) := by
  have h := reflection_log_15225_neg
  have he : Real.log (230017921147 / 50000000000) = -Real.log (50000000000 / 230017921147) := by
    rw [show ((230017921147 / 50000000000) : ℝ) = ((50000000000 / 230017921147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15226_neg : (212544321 / 40000000) ≤ -Real.log (50000000000 / 10154081632653) ∧
    -Real.log (50000000000 / 10154081632653) ≤ (5313608033 / 1000000000) := by
  have h := checkLog_sound (w := (3754081632653 / 16554081632653)) (n := 12)
    (lo := (92315553 / 200000000)) (hi := (230788883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10154081632653 / 6400000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10154081632653 / 6400000000000) = 1/(50000000000 / 10154081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15226 : Bounds (212544321 / 40000000) (5313608033 / 1000000000) (Real.log (10154081632653 / 50000000000)) := by
  have h := reflection_log_15226_neg
  have he : Real.log (10154081632653 / 50000000000) = -Real.log (50000000000 / 10154081632653) := by
    rw [show ((10154081632653 / 50000000000) : ℝ) = ((50000000000 / 10154081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15227_neg : (26671639 / 5000000) ≤ -Real.log (500000000000 / 103666666666667) ∧
    -Real.log (500000000000 / 103666666666667) ≤ (10418609 / 1953125) := by
  have h := checkLog_sound (w := (39666666666667 / 167666666666667)) (n := 12)
    (lo := (24114877 / 50000000)) (hi := (482297541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103666666666667 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(103666666666667 / 64000000000000) = 1/(500000000000 / 103666666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15227 : Bounds (26671639 / 5000000) (10418609 / 1953125) (Real.log (103666666666667 / 500000000000)) := by
  have h := reflection_log_15227_neg
  have he : Real.log (103666666666667 / 500000000000) = -Real.log (500000000000 / 103666666666667) := by
    rw [show ((103666666666667 / 500000000000) : ℝ) = ((500000000000 / 103666666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15228_neg : (6884361 / 10000000) ≤ -Real.log (5000 / 9953) ∧
    -Real.log (5000 / 9953) ≤ (688436101 / 1000000000) := by
  have h := checkLog_sound (w := (4953 / 14953)) (n := 12)
    (lo := (6884361 / 10000000)) (hi := (688436101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9953 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9953 / 5000) = 1/(5000 / 9953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15228 : Bounds (6884361 / 10000000) (688436101 / 1000000000) (Real.log (9953 / 5000)) := by
  have h := reflection_log_15228_neg
  have he : Real.log (9953 / 5000) = -Real.log (5000 / 9953) := by
    rw [show ((9953 / 5000) : ℝ) = ((5000 / 9953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15229_neg : (2333522793 / 500000000) ≤ -Real.log (47 / 5000) ∧
    -Real.log (47 / 5000) ≤ (4667045593 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1001)) (n := 12)
    (lo := (254081253 / 500000000)) (hi := (508162507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 376) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 376) = 1/(47 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15229 : Bounds (-4667045593 / 1000000000) (-2333522793 / 500000000) (Real.log (47 / 5000)) := by
  have h := reflection_log_15229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15230_neg : (990109 / 1000000000) ≤ -Real.log (5000000 / 5004953) ∧
    -Real.log (5000000 / 5004953) ≤ (99011 / 100000000) := by
  have h := checkLog_sound (w := (4953 / 10004953)) (n := 12)
    (lo := (990109 / 1000000000)) (hi := (99011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004953 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004953 / 5000000) = 1/(5000000 / 5004953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15230 : Bounds (990109 / 1000000000) (99011 / 100000000) (Real.log (5004953 / 5000000)) := by
  have h := reflection_log_15230_neg
  have he : Real.log (5004953 / 5000000) = -Real.log (5000000 / 5004953) := by
    rw [show ((5004953 / 5000000) : ℝ) = ((5000000 / 5004953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15231_neg : (99109 / 100000000) ≤ -Real.log (4995047 / 5000000) ∧
    -Real.log (4995047 / 5000000) ≤ (991091 / 1000000000) := by
  have h := checkLog_sound (w := (4953 / 9995047)) (n := 12)
    (lo := (99109 / 100000000)) (hi := (991091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995047) = 1/(4995047 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15231 : Bounds (-991091 / 1000000000) (-99109 / 100000000) (Real.log (4995047 / 5000000)) := by
  have h := reflection_log_15231_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
