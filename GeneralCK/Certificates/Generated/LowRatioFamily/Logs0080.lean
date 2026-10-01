import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5120_neg : (377831579 / 1000000000) ≤ -Real.log (250000000000 / 364779294233) ∧
    -Real.log (250000000000 / 364779294233) ≤ (18891579 / 50000000) := by
  have h := checkLog_sound (w := (114779294233 / 614779294233)) (n := 12)
    (lo := (377831579 / 1000000000)) (hi := (18891579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364779294233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364779294233 / 250000000000) = 1/(250000000000 / 364779294233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5120 : Bounds (377831579 / 1000000000) (18891579 / 50000000) (Real.log (364779294233 / 250000000000)) := by
  have h := reflection_log_5120_neg
  have he : Real.log (364779294233 / 250000000000) = -Real.log (250000000000 / 364779294233) := by
    rw [show ((364779294233 / 250000000000) : ℝ) = ((250000000000 / 364779294233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5121_neg : (189019403 / 500000000) ≤ -Real.log (50000000000 / 72970978849) ∧
    -Real.log (50000000000 / 72970978849) ≤ (378038807 / 1000000000) := by
  have h := checkLog_sound (w := (22970978849 / 122970978849)) (n := 12)
    (lo := (189019403 / 500000000)) (hi := (378038807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72970978849 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72970978849 / 50000000000) = 1/(50000000000 / 72970978849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5121 : Bounds (189019403 / 500000000) (378038807 / 1000000000) (Real.log (72970978849 / 50000000000)) := by
  have h := reflection_log_5121_neg
  have he : Real.log (72970978849 / 50000000000) = -Real.log (50000000000 / 72970978849) := by
    rw [show ((72970978849 / 50000000000) : ℝ) = ((50000000000 / 72970978849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5122_neg : (85672433 / 500000000) ≤ -Real.log (10000 / 11869) ∧
    -Real.log (10000 / 11869) ≤ (171344867 / 1000000000) := by
  have h := checkLog_sound (w := (1869 / 21869)) (n := 12)
    (lo := (85672433 / 500000000)) (hi := (171344867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11869 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11869 / 10000) = 1/(10000 / 11869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5122 : Bounds (85672433 / 500000000) (171344867 / 1000000000) (Real.log (11869 / 10000)) := by
  have h := reflection_log_5122_neg
  have he : Real.log (11869 / 10000) = -Real.log (10000 / 11869) := by
    rw [show ((11869 / 10000) : ℝ) = ((10000 / 11869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5123_neg : (8276047 / 40000000) ≤ -Real.log (8131 / 10000) ∧
    -Real.log (8131 / 10000) ≤ (25862647 / 125000000) := by
  have h := checkLog_sound (w := (1869 / 18131)) (n := 12)
    (lo := (8276047 / 40000000)) (hi := (25862647 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8131) = 1/(8131 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5123 : Bounds (-25862647 / 125000000) (-8276047 / 40000000) (Real.log (8131 / 10000)) := by
  have h := reflection_log_5123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5124_neg : (93441 / 500000000) ≤ -Real.log (10000000 / 10001869) ∧
    -Real.log (10000000 / 10001869) ≤ (186883 / 1000000000) := by
  have h := checkLog_sound (w := (1869 / 20001869)) (n := 12)
    (lo := (93441 / 500000000)) (hi := (186883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001869 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001869 / 10000000) = 1/(10000000 / 10001869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5124 : Bounds (93441 / 500000000) (186883 / 1000000000) (Real.log (10001869 / 10000000)) := by
  have h := reflection_log_5124_neg
  have he : Real.log (10001869 / 10000000) = -Real.log (10000000 / 10001869) := by
    rw [show ((10001869 / 10000000) : ℝ) = ((10000000 / 10001869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5125_neg : (186917 / 1000000000) ≤ -Real.log (9998131 / 10000000) ∧
    -Real.log (9998131 / 10000000) ≤ (93459 / 500000000) := by
  have h := checkLog_sound (w := (1869 / 19998131)) (n := 12)
    (lo := (186917 / 1000000000)) (hi := (93459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998131) = 1/(9998131 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5125 : Bounds (-93459 / 500000000) (-186917 / 1000000000) (Real.log (9998131 / 10000000)) := by
  have h := reflection_log_5125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5126_neg : (44875103 / 500000000) ≤ -Real.log (1000000 / 1093901) ∧
    -Real.log (1000000 / 1093901) ≤ (89750207 / 1000000000) := by
  have h := checkLog_sound (w := (93901 / 2093901)) (n := 12)
    (lo := (44875103 / 500000000)) (hi := (89750207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093901 / 1000000) = 1/(1000000 / 1093901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5126 : Bounds (44875103 / 500000000) (89750207 / 1000000000) (Real.log (1093901 / 1000000)) := by
  have h := reflection_log_5126_neg
  have he : Real.log (1093901 / 1000000) = -Real.log (1000000 / 1093901) := by
    rw [show ((1093901 / 1000000) : ℝ) = ((1000000 / 1093901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5127_neg : (98606707 / 1000000000) ≤ -Real.log (906099 / 1000000) ∧
    -Real.log (906099 / 1000000) ≤ (24651677 / 250000000) := by
  have h := checkLog_sound (w := (93901 / 1906099)) (n := 12)
    (lo := (98606707 / 1000000000)) (hi := (24651677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906099) = 1/(906099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5127 : Bounds (-24651677 / 250000000) (-98606707 / 1000000000) (Real.log (906099 / 1000000)) := by
  have h := reflection_log_5127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5128_neg : (44983419 / 500000000) ≤ -Real.log (500000 / 547069) ∧
    -Real.log (500000 / 547069) ≤ (89966839 / 1000000000) := by
  have h := checkLog_sound (w := (47069 / 1047069)) (n := 12)
    (lo := (44983419 / 500000000)) (hi := (89966839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547069 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547069 / 500000) = 1/(500000 / 547069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5128 : Bounds (44983419 / 500000000) (89966839 / 1000000000) (Real.log (547069 / 500000)) := by
  have h := reflection_log_5128_neg
  have he : Real.log (547069 / 500000) = -Real.log (500000 / 547069) := by
    rw [show ((547069 / 500000) : ℝ) = ((500000 / 547069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5129_neg : (49434151 / 500000000) ≤ -Real.log (452931 / 500000) ∧
    -Real.log (452931 / 500000) ≤ (98868303 / 1000000000) := by
  have h := checkLog_sound (w := (47069 / 952931)) (n := 12)
    (lo := (49434151 / 500000000)) (hi := (98868303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452931) = 1/(452931 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5129 : Bounds (-98868303 / 1000000000) (-49434151 / 500000000) (Real.log (452931 / 500000)) := by
  have h := reflection_log_5129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5130_neg : (8901463 / 1000000000) ≤ -Real.log (247784509239 / 250000000000) ∧
    -Real.log (247784509239 / 250000000000) ≤ (1112683 / 125000000) := by
  have h := checkLog_sound (w := (2215490761 / 497784509239)) (n := 12)
    (lo := (8901463 / 1000000000)) (hi := (1112683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247784509239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247784509239) = 1/(247784509239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5130 : Bounds (-1112683 / 125000000) (-8901463 / 1000000000) (Real.log (247784509239 / 250000000000)) := by
  have h := reflection_log_5130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5131_neg : (8856501 / 1000000000) ≤ -Real.log (991182602199 / 1000000000000) ∧
    -Real.log (991182602199 / 1000000000000) ≤ (4428251 / 500000000) := by
  have h := checkLog_sound (w := (8817397801 / 1991182602199)) (n := 12)
    (lo := (8856501 / 1000000000)) (hi := (4428251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991182602199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991182602199) = 1/(991182602199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5131 : Bounds (-4428251 / 500000000) (-8856501 / 1000000000) (Real.log (991182602199 / 1000000000000)) := by
  have h := reflection_log_5131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5132_neg : (188356913 / 1000000000) ≤ -Real.log (250000000000 / 301816081907) ∧
    -Real.log (250000000000 / 301816081907) ≤ (94178457 / 500000000) := by
  have h := checkLog_sound (w := (51816081907 / 551816081907)) (n := 12)
    (lo := (188356913 / 1000000000)) (hi := (94178457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301816081907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301816081907 / 250000000000) = 1/(250000000000 / 301816081907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5132 : Bounds (188356913 / 1000000000) (94178457 / 500000000) (Real.log (301816081907 / 250000000000)) := by
  have h := reflection_log_5132_neg
  have he : Real.log (301816081907 / 250000000000) = -Real.log (250000000000 / 301816081907) := by
    rw [show ((301816081907 / 250000000000) : ℝ) = ((250000000000 / 301816081907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5133_neg : (188835141 / 1000000000) ≤ -Real.log (20000000000 / 24156836251) ∧
    -Real.log (20000000000 / 24156836251) ≤ (94417571 / 500000000) := by
  have h := checkLog_sound (w := (4156836251 / 44156836251)) (n := 12)
    (lo := (188835141 / 1000000000)) (hi := (94417571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24156836251 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24156836251 / 20000000000) = 1/(20000000000 / 24156836251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5133 : Bounds (188835141 / 1000000000) (94417571 / 500000000) (Real.log (24156836251 / 20000000000)) := by
  have h := reflection_log_5133_neg
  have he : Real.log (24156836251 / 20000000000) = -Real.log (20000000000 / 24156836251) := by
    rw [show ((24156836251 / 20000000000) : ℝ) = ((20000000000 / 24156836251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5134_neg : (189019403 / 500000000) ≤ -Real.log (500000000000 / 729709788489) ∧
    -Real.log (500000000000 / 729709788489) ≤ (378038807 / 1000000000) := by
  have h := checkLog_sound (w := (229709788489 / 1229709788489)) (n := 12)
    (lo := (189019403 / 500000000)) (hi := (378038807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729709788489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729709788489 / 500000000000) = 1/(500000000000 / 729709788489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5134 : Bounds (189019403 / 500000000) (378038807 / 1000000000) (Real.log (729709788489 / 500000000000)) := by
  have h := reflection_log_5134_neg
  have he : Real.log (729709788489 / 500000000000) = -Real.log (500000000000 / 729709788489) := by
    rw [show ((729709788489 / 500000000000) : ℝ) = ((500000000000 / 729709788489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5135_neg : (378246041 / 1000000000) ≤ -Real.log (100000000000 / 145972205141) ∧
    -Real.log (100000000000 / 145972205141) ≤ (189123021 / 500000000) := by
  have h := checkLog_sound (w := (45972205141 / 245972205141)) (n := 12)
    (lo := (378246041 / 1000000000)) (hi := (189123021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145972205141 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145972205141 / 100000000000) = 1/(100000000000 / 145972205141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5135 : Bounds (378246041 / 1000000000) (189123021 / 500000000) (Real.log (145972205141 / 100000000000)) := by
  have h := reflection_log_5135_neg
  have he : Real.log (145972205141 / 100000000000) = -Real.log (100000000000 / 145972205141) := by
    rw [show ((145972205141 / 100000000000) : ℝ) = ((100000000000 / 145972205141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5136_neg : (34285823 / 200000000) ≤ -Real.log (1000 / 1187) ∧
    -Real.log (1000 / 1187) ≤ (42857279 / 250000000) := by
  have h := checkLog_sound (w := (187 / 2187)) (n := 12)
    (lo := (34285823 / 200000000)) (hi := (42857279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 1000) = 1/(1000 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5136 : Bounds (34285823 / 200000000) (42857279 / 250000000) (Real.log (1187 / 1000)) := by
  have h := reflection_log_5136_neg
  have he : Real.log (1187 / 1000) = -Real.log (1000 / 1187) := by
    rw [show ((1187 / 1000) : ℝ) = ((1000 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5137_neg : (207024169 / 1000000000) ≤ -Real.log (813 / 1000) ∧
    -Real.log (813 / 1000) ≤ (20702417 / 100000000) := by
  have h := checkLog_sound (w := (187 / 1813)) (n := 12)
    (lo := (207024169 / 1000000000)) (hi := (20702417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 813) = 1/(813 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5137 : Bounds (-20702417 / 100000000) (-207024169 / 1000000000) (Real.log (813 / 1000)) := by
  have h := reflection_log_5137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5138_neg : (93491 / 500000000) ≤ -Real.log (1000000 / 1000187) ∧
    -Real.log (1000000 / 1000187) ≤ (186983 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 2000187)) (n := 12)
    (lo := (93491 / 500000000)) (hi := (186983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000187 / 1000000) = 1/(1000000 / 1000187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5138 : Bounds (93491 / 500000000) (186983 / 1000000000) (Real.log (1000187 / 1000000)) := by
  have h := reflection_log_5138_neg
  have he : Real.log (1000187 / 1000000) = -Real.log (1000000 / 1000187) := by
    rw [show ((1000187 / 1000000) : ℝ) = ((1000000 / 1000187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5139_neg : (187017 / 1000000000) ≤ -Real.log (999813 / 1000000) ∧
    -Real.log (999813 / 1000000) ≤ (93509 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1999813)) (n := 12)
    (lo := (187017 / 1000000000)) (hi := (93509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999813) = 1/(999813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5139 : Bounds (-93509 / 500000000) (-187017 / 1000000000) (Real.log (999813 / 1000000)) := by
  have h := reflection_log_5139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5140_neg : (89795913 / 1000000000) ≤ -Real.log (1000000 / 1093951) ∧
    -Real.log (1000000 / 1093951) ≤ (44897957 / 500000000) := by
  have h := checkLog_sound (w := (93951 / 2093951)) (n := 12)
    (lo := (89795913 / 1000000000)) (hi := (44897957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093951 / 1000000) = 1/(1000000 / 1093951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5140 : Bounds (89795913 / 1000000000) (44897957 / 500000000) (Real.log (1093951 / 1000000)) := by
  have h := reflection_log_5140_neg
  have he : Real.log (1093951 / 1000000) = -Real.log (1000000 / 1093951) := by
    rw [show ((1093951 / 1000000) : ℝ) = ((1000000 / 1093951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5141_neg : (9866189 / 100000000) ≤ -Real.log (906049 / 1000000) ∧
    -Real.log (906049 / 1000000) ≤ (98661891 / 1000000000) := by
  have h := checkLog_sound (w := (93951 / 1906049)) (n := 12)
    (lo := (9866189 / 100000000)) (hi := (98661891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906049) = 1/(906049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5141 : Bounds (-98661891 / 1000000000) (-9866189 / 100000000) (Real.log (906049 / 1000000)) := by
  have h := reflection_log_5141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5142_neg : (90013449 / 1000000000) ≤ -Real.log (1000000 / 1094189) ∧
    -Real.log (1000000 / 1094189) ≤ (1800269 / 20000000) := by
  have h := checkLog_sound (w := (94189 / 2094189)) (n := 12)
    (lo := (90013449 / 1000000000)) (hi := (1800269 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094189 / 1000000) = 1/(1000000 / 1094189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5142 : Bounds (90013449 / 1000000000) (1800269 / 20000000) (Real.log (1094189 / 1000000)) := by
  have h := reflection_log_5142_neg
  have he : Real.log (1094189 / 1000000) = -Real.log (1000000 / 1094189) := by
    rw [show ((1094189 / 1000000) : ℝ) = ((1000000 / 1094189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5143_neg : (98924603 / 1000000000) ≤ -Real.log (905811 / 1000000) ∧
    -Real.log (905811 / 1000000) ≤ (24731151 / 250000000) := by
  have h := checkLog_sound (w := (94189 / 1905811)) (n := 12)
    (lo := (98924603 / 1000000000)) (hi := (24731151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905811) = 1/(905811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5143 : Bounds (-24731151 / 250000000) (-98924603 / 1000000000) (Real.log (905811 / 1000000)) := by
  have h := reflection_log_5143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5144_neg : (4455577 / 500000000) ≤ -Real.log (991128432279 / 1000000000000) ∧
    -Real.log (991128432279 / 1000000000000) ≤ (1782231 / 200000000) := by
  have h := checkLog_sound (w := (8871567721 / 1991128432279)) (n := 12)
    (lo := (4455577 / 500000000)) (hi := (1782231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991128432279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991128432279) = 1/(991128432279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5144 : Bounds (-1782231 / 200000000) (-4455577 / 500000000) (Real.log (991128432279 / 1000000000000)) := by
  have h := reflection_log_5144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5145_neg : (8865977 / 1000000000) ≤ -Real.log (991173209599 / 1000000000000) ∧
    -Real.log (991173209599 / 1000000000000) ≤ (4432989 / 500000000) := by
  have h := checkLog_sound (w := (8826790401 / 1991173209599)) (n := 12)
    (lo := (8865977 / 1000000000)) (hi := (4432989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991173209599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991173209599) = 1/(991173209599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5145 : Bounds (-4432989 / 500000000) (-8865977 / 1000000000) (Real.log (991173209599 / 1000000000000)) := by
  have h := reflection_log_5145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5146_neg : (188457803 / 1000000000) ≤ -Real.log (125000000000 / 150923266843) ∧
    -Real.log (125000000000 / 150923266843) ≤ (47114451 / 250000000) := by
  have h := checkLog_sound (w := (25923266843 / 275923266843)) (n := 12)
    (lo := (188457803 / 1000000000)) (hi := (47114451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150923266843 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150923266843 / 125000000000) = 1/(125000000000 / 150923266843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5146 : Bounds (188457803 / 1000000000) (47114451 / 250000000) (Real.log (150923266843 / 125000000000)) := by
  have h := reflection_log_5146_neg
  have he : Real.log (150923266843 / 125000000000) = -Real.log (125000000000 / 150923266843) := by
    rw [show ((150923266843 / 125000000000) : ℝ) = ((125000000000 / 150923266843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5147_neg : (188938053 / 1000000000) ≤ -Real.log (125000000000 / 150995765121) ∧
    -Real.log (125000000000 / 150995765121) ≤ (94469027 / 500000000) := by
  have h := checkLog_sound (w := (25995765121 / 275995765121)) (n := 12)
    (lo := (188938053 / 1000000000)) (hi := (94469027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150995765121 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150995765121 / 125000000000) = 1/(125000000000 / 150995765121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5147 : Bounds (188938053 / 1000000000) (94469027 / 500000000) (Real.log (150995765121 / 125000000000)) := by
  have h := reflection_log_5147_neg
  have he : Real.log (150995765121 / 125000000000) = -Real.log (125000000000 / 150995765121) := by
    rw [show ((150995765121 / 125000000000) : ℝ) = ((125000000000 / 150995765121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5148_neg : (378246041 / 1000000000) ≤ -Real.log (62500000000 / 91232628213) ∧
    -Real.log (62500000000 / 91232628213) ≤ (189123021 / 500000000) := by
  have h := checkLog_sound (w := (28732628213 / 153732628213)) (n := 12)
    (lo := (378246041 / 1000000000)) (hi := (189123021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91232628213 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91232628213 / 62500000000) = 1/(62500000000 / 91232628213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5148 : Bounds (378246041 / 1000000000) (189123021 / 500000000) (Real.log (91232628213 / 62500000000)) := by
  have h := reflection_log_5148_neg
  have he : Real.log (91232628213 / 62500000000) = -Real.log (62500000000 / 91232628213) := by
    rw [show ((91232628213 / 62500000000) : ℝ) = ((62500000000 / 91232628213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5149_neg : (75690657 / 200000000) ≤ -Real.log (125000000000 / 182503075031) ∧
    -Real.log (125000000000 / 182503075031) ≤ (189226643 / 500000000) := by
  have h := checkLog_sound (w := (57503075031 / 307503075031)) (n := 12)
    (lo := (75690657 / 200000000)) (hi := (189226643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182503075031 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182503075031 / 125000000000) = 1/(125000000000 / 182503075031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5149 : Bounds (75690657 / 200000000) (189226643 / 500000000) (Real.log (182503075031 / 125000000000)) := by
  have h := reflection_log_5149_neg
  have he : Real.log (182503075031 / 125000000000) = -Real.log (125000000000 / 182503075031) := by
    rw [show ((182503075031 / 125000000000) : ℝ) = ((125000000000 / 182503075031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5150_neg : (85756679 / 500000000) ≤ -Real.log (10000 / 11871) ∧
    -Real.log (10000 / 11871) ≤ (171513359 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 21871)) (n := 12)
    (lo := (85756679 / 500000000)) (hi := (171513359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11871 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11871 / 10000) = 1/(10000 / 11871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5150 : Bounds (85756679 / 500000000) (171513359 / 1000000000) (Real.log (11871 / 10000)) := by
  have h := reflection_log_5150_neg
  have he : Real.log (11871 / 10000) = -Real.log (10000 / 11871) := by
    rw [show ((11871 / 10000) : ℝ) = ((10000 / 11871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5151_neg : (103573589 / 500000000) ≤ -Real.log (8129 / 10000) ∧
    -Real.log (8129 / 10000) ≤ (207147179 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 18129)) (n := 12)
    (lo := (103573589 / 500000000)) (hi := (207147179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8129) = 1/(8129 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5151 : Bounds (-207147179 / 1000000000) (-103573589 / 500000000) (Real.log (8129 / 10000)) := by
  have h := reflection_log_5151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5152_neg : (93541 / 500000000) ≤ -Real.log (10000000 / 10001871) ∧
    -Real.log (10000000 / 10001871) ≤ (187083 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 20001871)) (n := 12)
    (lo := (93541 / 500000000)) (hi := (187083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001871 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001871 / 10000000) = 1/(10000000 / 10001871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5152 : Bounds (93541 / 500000000) (187083 / 1000000000) (Real.log (10001871 / 10000000)) := by
  have h := reflection_log_5152_neg
  have he : Real.log (10001871 / 10000000) = -Real.log (10000000 / 10001871) := by
    rw [show ((10001871 / 10000000) : ℝ) = ((10000000 / 10001871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5153_neg : (187117 / 1000000000) ≤ -Real.log (9998129 / 10000000) ∧
    -Real.log (9998129 / 10000000) ≤ (93559 / 500000000) := by
  have h := checkLog_sound (w := (1871 / 19998129)) (n := 12)
    (lo := (187117 / 1000000000)) (hi := (93559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998129) = 1/(9998129 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5153 : Bounds (-93559 / 500000000) (-187117 / 1000000000) (Real.log (9998129 / 10000000)) := by
  have h := reflection_log_5153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5154_neg : (22460633 / 250000000) ≤ -Real.log (500000 / 547001) ∧
    -Real.log (500000 / 547001) ≤ (89842533 / 1000000000) := by
  have h := checkLog_sound (w := (47001 / 1047001)) (n := 12)
    (lo := (22460633 / 250000000)) (hi := (89842533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547001 / 500000) = 1/(500000 / 547001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5154 : Bounds (22460633 / 250000000) (89842533 / 1000000000) (Real.log (547001 / 500000)) := by
  have h := reflection_log_5154_neg
  have he : Real.log (547001 / 500000) = -Real.log (500000 / 547001) := by
    rw [show ((547001 / 500000) : ℝ) = ((500000 / 547001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5155_neg : (4935909 / 50000000) ≤ -Real.log (452999 / 500000) ∧
    -Real.log (452999 / 500000) ≤ (98718181 / 1000000000) := by
  have h := checkLog_sound (w := (47001 / 952999)) (n := 12)
    (lo := (4935909 / 50000000)) (hi := (98718181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452999) = 1/(452999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5155 : Bounds (-98718181 / 1000000000) (-4935909 / 50000000) (Real.log (452999 / 500000)) := by
  have h := reflection_log_5155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5156_neg : (45030029 / 500000000) ≤ -Real.log (6250 / 6839) ∧
    -Real.log (6250 / 6839) ≤ (90060059 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 13089)) (n := 12)
    (lo := (45030029 / 500000000)) (hi := (90060059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6839 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6839 / 6250) = 1/(6250 / 6839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5156 : Bounds (45030029 / 500000000) (90060059 / 1000000000) (Real.log (6839 / 6250)) := by
  have h := reflection_log_5156_neg
  have he : Real.log (6839 / 6250) = -Real.log (6250 / 6839) := by
    rw [show ((6839 / 6250) : ℝ) = ((6250 / 6839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5157_neg : (24745227 / 250000000) ≤ -Real.log (5661 / 6250) ∧
    -Real.log (5661 / 6250) ≤ (98980909 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 11911)) (n := 12)
    (lo := (24745227 / 250000000)) (hi := (98980909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5661) = 1/(5661 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5157 : Bounds (-98980909 / 1000000000) (-24745227 / 250000000) (Real.log (5661 / 6250)) := by
  have h := reflection_log_5157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5158_neg : (178417 / 20000000) ≤ -Real.log (38715579 / 39062500) ∧
    -Real.log (38715579 / 39062500) ≤ (8920851 / 1000000000) := by
  have h := checkLog_sound (w := (346921 / 77778079)) (n := 12)
    (lo := (178417 / 20000000)) (hi := (8920851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38715579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38715579) = 1/(38715579 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5158 : Bounds (-8920851 / 1000000000) (-178417 / 20000000) (Real.log (38715579 / 39062500)) := by
  have h := reflection_log_5158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5159_neg : (69341 / 7812500) ≤ -Real.log (247790905999 / 250000000000) ∧
    -Real.log (247790905999 / 250000000000) ≤ (8875649 / 1000000000) := by
  have h := checkLog_sound (w := (2209094001 / 497790905999)) (n := 12)
    (lo := (69341 / 7812500)) (hi := (8875649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247790905999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247790905999) = 1/(247790905999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5159 : Bounds (-8875649 / 1000000000) (-69341 / 7812500) (Real.log (247790905999 / 250000000000)) := by
  have h := reflection_log_5159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5160_neg : (23570089 / 125000000) ≤ -Real.log (500000000000 / 603755195927) ∧
    -Real.log (500000000000 / 603755195927) ≤ (188560713 / 1000000000) := by
  have h := checkLog_sound (w := (103755195927 / 1103755195927)) (n := 12)
    (lo := (23570089 / 125000000)) (hi := (188560713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603755195927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603755195927 / 500000000000) = 1/(500000000000 / 603755195927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5160 : Bounds (23570089 / 125000000) (188560713 / 1000000000) (Real.log (603755195927 / 500000000000)) := by
  have h := reflection_log_5160_neg
  have he : Real.log (603755195927 / 500000000000) = -Real.log (500000000000 / 603755195927) := by
    rw [show ((603755195927 / 500000000000) : ℝ) = ((500000000000 / 603755195927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5161_neg : (189040967 / 1000000000) ≤ -Real.log (500000000000 / 604045221693) ∧
    -Real.log (500000000000 / 604045221693) ≤ (23630121 / 125000000) := by
  have h := checkLog_sound (w := (104045221693 / 1104045221693)) (n := 12)
    (lo := (189040967 / 1000000000)) (hi := (23630121 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604045221693 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604045221693 / 500000000000) = 1/(500000000000 / 604045221693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5161 : Bounds (189040967 / 1000000000) (23630121 / 125000000) (Real.log (604045221693 / 500000000000)) := by
  have h := reflection_log_5161_neg
  have he : Real.log (604045221693 / 500000000000) = -Real.log (500000000000 / 604045221693) := by
    rw [show ((604045221693 / 500000000000) : ℝ) = ((500000000000 / 604045221693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5162_neg : (75690657 / 200000000) ≤ -Real.log (500000000000 / 730012300123) ∧
    -Real.log (500000000000 / 730012300123) ≤ (189226643 / 500000000) := by
  have h := checkLog_sound (w := (230012300123 / 1230012300123)) (n := 12)
    (lo := (75690657 / 200000000)) (hi := (189226643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730012300123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730012300123 / 500000000000) = 1/(500000000000 / 730012300123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5162 : Bounds (75690657 / 200000000) (189226643 / 500000000) (Real.log (730012300123 / 500000000000)) := by
  have h := reflection_log_5162_neg
  have he : Real.log (730012300123 / 500000000000) = -Real.log (500000000000 / 730012300123) := by
    rw [show ((730012300123 / 500000000000) : ℝ) = ((500000000000 / 730012300123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5163_neg : (47332567 / 125000000) ≤ -Real.log (500000000000 / 730163611761) ∧
    -Real.log (500000000000 / 730163611761) ≤ (378660537 / 1000000000) := by
  have h := checkLog_sound (w := (230163611761 / 1230163611761)) (n := 12)
    (lo := (47332567 / 125000000)) (hi := (378660537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730163611761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730163611761 / 500000000000) = 1/(500000000000 / 730163611761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5163 : Bounds (47332567 / 125000000) (378660537 / 1000000000) (Real.log (730163611761 / 500000000000)) := by
  have h := reflection_log_5163_neg
  have he : Real.log (730163611761 / 500000000000) = -Real.log (500000000000 / 730163611761) := by
    rw [show ((730163611761 / 500000000000) : ℝ) = ((500000000000 / 730163611761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5164_neg : (171597593 / 1000000000) ≤ -Real.log (625 / 742) ∧
    -Real.log (625 / 742) ≤ (85798797 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1367)) (n := 12)
    (lo := (171597593 / 1000000000)) (hi := (85798797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742 / 625) = 1/(625 / 742) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5164 : Bounds (171597593 / 1000000000) (85798797 / 500000000) (Real.log (742 / 625)) := by
  have h := reflection_log_5164_neg
  have he : Real.log (742 / 625) = -Real.log (625 / 742) := by
    rw [show ((742 / 625) : ℝ) = ((625 / 742) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5165_neg : (103635101 / 500000000) ≤ -Real.log (508 / 625) ∧
    -Real.log (508 / 625) ≤ (207270203 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1133)) (n := 12)
    (lo := (103635101 / 500000000)) (hi := (207270203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 508) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 508) = 1/(508 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5165 : Bounds (-207270203 / 1000000000) (-103635101 / 500000000) (Real.log (508 / 625)) := by
  have h := reflection_log_5165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5166_neg : (93591 / 500000000) ≤ -Real.log (625000 / 625117) ∧
    -Real.log (625000 / 625117) ≤ (187183 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1250117)) (n := 12)
    (lo := (93591 / 500000000)) (hi := (187183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625117 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625117 / 625000) = 1/(625000 / 625117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5166 : Bounds (93591 / 500000000) (187183 / 1000000000) (Real.log (625117 / 625000)) := by
  have h := reflection_log_5166_neg
  have he : Real.log (625117 / 625000) = -Real.log (625000 / 625117) := by
    rw [show ((625117 / 625000) : ℝ) = ((625000 / 625117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5167_neg : (187217 / 1000000000) ≤ -Real.log (624883 / 625000) ∧
    -Real.log (624883 / 625000) ≤ (93609 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1249883)) (n := 12)
    (lo := (187217 / 1000000000)) (hi := (93609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624883) = 1/(624883 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5167 : Bounds (-93609 / 500000000) (-187217 / 1000000000) (Real.log (624883 / 625000)) := by
  have h := reflection_log_5167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5168_neg : (22472287 / 250000000) ≤ -Real.log (1000000 / 1094053) ∧
    -Real.log (1000000 / 1094053) ≤ (89889149 / 1000000000) := by
  have h := checkLog_sound (w := (94053 / 2094053)) (n := 12)
    (lo := (22472287 / 250000000)) (hi := (89889149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094053 / 1000000) = 1/(1000000 / 1094053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5168 : Bounds (22472287 / 250000000) (89889149 / 1000000000) (Real.log (1094053 / 1000000)) := by
  have h := reflection_log_5168_neg
  have he : Real.log (1094053 / 1000000) = -Real.log (1000000 / 1094053) := by
    rw [show ((1094053 / 1000000) : ℝ) = ((1000000 / 1094053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5169_neg : (98774473 / 1000000000) ≤ -Real.log (905947 / 1000000) ∧
    -Real.log (905947 / 1000000) ≤ (49387237 / 500000000) := by
  have h := checkLog_sound (w := (94053 / 1905947)) (n := 12)
    (lo := (98774473 / 1000000000)) (hi := (49387237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905947) = 1/(905947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5169 : Bounds (-49387237 / 500000000) (-98774473 / 1000000000) (Real.log (905947 / 1000000)) := by
  have h := reflection_log_5169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5170_neg : (11263333 / 125000000) ≤ -Real.log (1000000 / 1094291) ∧
    -Real.log (1000000 / 1094291) ≤ (18021333 / 200000000) := by
  have h := checkLog_sound (w := (94291 / 2094291)) (n := 12)
    (lo := (11263333 / 125000000)) (hi := (18021333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094291 / 1000000) = 1/(1000000 / 1094291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5170 : Bounds (11263333 / 125000000) (18021333 / 200000000) (Real.log (1094291 / 1000000)) := by
  have h := reflection_log_5170_neg
  have he : Real.log (1094291 / 1000000) = -Real.log (1000000 / 1094291) := by
    rw [show ((1094291 / 1000000) : ℝ) = ((1000000 / 1094291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5171_neg : (3094913 / 31250000) ≤ -Real.log (905709 / 1000000) ∧
    -Real.log (905709 / 1000000) ≤ (99037217 / 1000000000) := by
  have h := checkLog_sound (w := (94291 / 1905709)) (n := 12)
    (lo := (3094913 / 31250000)) (hi := (99037217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905709) = 1/(905709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5171 : Bounds (-99037217 / 1000000000) (-3094913 / 31250000) (Real.log (905709 / 1000000)) := by
  have h := reflection_log_5171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5172_neg : (8930551 / 1000000000) ≤ -Real.log (991109207319 / 1000000000000) ∧
    -Real.log (991109207319 / 1000000000000) ≤ (1116319 / 125000000) := by
  have h := checkLog_sound (w := (8890792681 / 1991109207319)) (n := 12)
    (lo := (8930551 / 1000000000)) (hi := (1116319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991109207319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991109207319) = 1/(991109207319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5172 : Bounds (-1116319 / 125000000) (-8930551 / 1000000000) (Real.log (991109207319 / 1000000000000)) := by
  have h := reflection_log_5172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5173_neg : (2221331 / 250000000) ≤ -Real.log (991154033191 / 1000000000000) ∧
    -Real.log (991154033191 / 1000000000000) ≤ (355413 / 40000000) := by
  have h := checkLog_sound (w := (8845966809 / 1991154033191)) (n := 12)
    (lo := (2221331 / 250000000)) (hi := (355413 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991154033191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991154033191) = 1/(991154033191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5173 : Bounds (-355413 / 40000000) (-2221331 / 250000000) (Real.log (991154033191 / 1000000000000)) := by
  have h := reflection_log_5173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5174_neg : (94331811 / 500000000) ≤ -Real.log (500000000000 / 603817331477) ∧
    -Real.log (500000000000 / 603817331477) ≤ (188663623 / 1000000000) := by
  have h := checkLog_sound (w := (103817331477 / 1103817331477)) (n := 12)
    (lo := (94331811 / 500000000)) (hi := (188663623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603817331477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603817331477 / 500000000000) = 1/(500000000000 / 603817331477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5174 : Bounds (94331811 / 500000000) (188663623 / 1000000000) (Real.log (603817331477 / 500000000000)) := by
  have h := reflection_log_5174_neg
  have he : Real.log (603817331477 / 500000000000) = -Real.log (500000000000 / 603817331477) := by
    rw [show ((603817331477 / 500000000000) : ℝ) = ((500000000000 / 603817331477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5175_neg : (189143881 / 1000000000) ≤ -Real.log (250000000000 / 302053694951) ∧
    -Real.log (250000000000 / 302053694951) ≤ (94571941 / 500000000) := by
  have h := checkLog_sound (w := (52053694951 / 552053694951)) (n := 12)
    (lo := (189143881 / 1000000000)) (hi := (94571941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302053694951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302053694951 / 250000000000) = 1/(250000000000 / 302053694951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5175 : Bounds (189143881 / 1000000000) (94571941 / 500000000) (Real.log (302053694951 / 250000000000)) := by
  have h := reflection_log_5175_neg
  have he : Real.log (302053694951 / 250000000000) = -Real.log (250000000000 / 302053694951) := by
    rw [show ((302053694951 / 250000000000) : ℝ) = ((250000000000 / 302053694951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5176_neg : (47332567 / 125000000) ≤ -Real.log (6250000000 / 9127045147) ∧
    -Real.log (6250000000 / 9127045147) ≤ (378660537 / 1000000000) := by
  have h := checkLog_sound (w := (2877045147 / 15377045147)) (n := 12)
    (lo := (47332567 / 125000000)) (hi := (378660537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9127045147 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9127045147 / 6250000000) = 1/(6250000000 / 9127045147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5176 : Bounds (47332567 / 125000000) (378660537 / 1000000000) (Real.log (9127045147 / 6250000000)) := by
  have h := reflection_log_5176_neg
  have he : Real.log (9127045147 / 6250000000) = -Real.log (6250000000 / 9127045147) := by
    rw [show ((9127045147 / 6250000000) : ℝ) = ((6250000000 / 9127045147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5177_neg : (75773559 / 200000000) ≤ -Real.log (50000000000 / 73031496063) ∧
    -Real.log (50000000000 / 73031496063) ≤ (94716949 / 250000000) := by
  have h := checkLog_sound (w := (23031496063 / 123031496063)) (n := 12)
    (lo := (75773559 / 200000000)) (hi := (94716949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73031496063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73031496063 / 50000000000) = 1/(50000000000 / 73031496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5177 : Bounds (75773559 / 200000000) (94716949 / 250000000) (Real.log (73031496063 / 50000000000)) := by
  have h := reflection_log_5177_neg
  have he : Real.log (73031496063 / 50000000000) = -Real.log (50000000000 / 73031496063) := by
    rw [show ((73031496063 / 50000000000) : ℝ) = ((50000000000 / 73031496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5178_neg : (171681821 / 1000000000) ≤ -Real.log (10000 / 11873) ∧
    -Real.log (10000 / 11873) ≤ (85840911 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 21873)) (n := 12)
    (lo := (171681821 / 1000000000)) (hi := (85840911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11873 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11873 / 10000) = 1/(10000 / 11873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5178 : Bounds (171681821 / 1000000000) (85840911 / 500000000) (Real.log (11873 / 10000)) := by
  have h := reflection_log_5178_neg
  have he : Real.log (11873 / 10000) = -Real.log (10000 / 11873) := by
    rw [show ((11873 / 10000) : ℝ) = ((10000 / 11873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5179_neg : (207393241 / 1000000000) ≤ -Real.log (8127 / 10000) ∧
    -Real.log (8127 / 10000) ≤ (103696621 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 18127)) (n := 12)
    (lo := (207393241 / 1000000000)) (hi := (103696621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8127) = 1/(8127 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5179 : Bounds (-103696621 / 500000000) (-207393241 / 1000000000) (Real.log (8127 / 10000)) := by
  have h := reflection_log_5179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5180_neg : (93641 / 500000000) ≤ -Real.log (10000000 / 10001873) ∧
    -Real.log (10000000 / 10001873) ≤ (187283 / 1000000000) := by
  have h := checkLog_sound (w := (1873 / 20001873)) (n := 12)
    (lo := (93641 / 500000000)) (hi := (187283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001873 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001873 / 10000000) = 1/(10000000 / 10001873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5180 : Bounds (93641 / 500000000) (187283 / 1000000000) (Real.log (10001873 / 10000000)) := by
  have h := reflection_log_5180_neg
  have he : Real.log (10001873 / 10000000) = -Real.log (10000000 / 10001873) := by
    rw [show ((10001873 / 10000000) : ℝ) = ((10000000 / 10001873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5181_neg : (187317 / 1000000000) ≤ -Real.log (9998127 / 10000000) ∧
    -Real.log (9998127 / 10000000) ≤ (93659 / 500000000) := by
  have h := checkLog_sound (w := (1873 / 19998127)) (n := 12)
    (lo := (187317 / 1000000000)) (hi := (93659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998127) = 1/(9998127 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5181 : Bounds (-93659 / 500000000) (-187317 / 1000000000) (Real.log (9998127 / 10000000)) := by
  have h := reflection_log_5181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5182_neg : (89935763 / 1000000000) ≤ -Real.log (125000 / 136763) ∧
    -Real.log (125000 / 136763) ≤ (22483941 / 250000000) := by
  have h := checkLog_sound (w := (11763 / 261763)) (n := 12)
    (lo := (89935763 / 1000000000)) (hi := (22483941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136763 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136763 / 125000) = 1/(125000 / 136763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5182 : Bounds (89935763 / 1000000000) (22483941 / 250000000) (Real.log (136763 / 125000)) := by
  have h := reflection_log_5182_neg
  have he : Real.log (136763 / 125000) = -Real.log (125000 / 136763) := by
    rw [show ((136763 / 125000) : ℝ) = ((125000 / 136763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5183_neg : (98830769 / 1000000000) ≤ -Real.log (113237 / 125000) ∧
    -Real.log (113237 / 125000) ≤ (9883077 / 100000000) := by
  have h := checkLog_sound (w := (11763 / 238237)) (n := 12)
    (lo := (98830769 / 1000000000)) (hi := (9883077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113237) = 1/(113237 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5183 : Bounds (-9883077 / 100000000) (-98830769 / 1000000000) (Real.log (113237 / 125000)) := by
  have h := reflection_log_5183_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
