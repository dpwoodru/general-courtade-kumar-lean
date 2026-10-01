import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9728_neg : (1650197 / 10000000) ≤ -Real.log (847877 / 1000000) ∧
    -Real.log (847877 / 1000000) ≤ (165019701 / 1000000000) := by
  have h := checkLog_sound (w := (152123 / 1847877)) (n := 12)
    (lo := (1650197 / 10000000)) (hi := (165019701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847877) = 1/(847877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9728 : Bounds (-165019701 / 1000000000) (-1650197 / 10000000) (Real.log (847877 / 1000000)) := by
  have h := reflection_log_9728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9729_neg : (23413373 / 1000000000) ≤ -Real.log (976858592871 / 1000000000000) ∧
    -Real.log (976858592871 / 1000000000000) ≤ (11706687 / 500000000) := by
  have h := checkLog_sound (w := (23141407129 / 1976858592871)) (n := 12)
    (lo := (23413373 / 1000000000)) (hi := (11706687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976858592871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976858592871) = 1/(976858592871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9729 : Bounds (-11706687 / 500000000) (-23413373 / 1000000000) (Real.log (976858592871 / 1000000000000)) := by
  have h := reflection_log_9729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9730_neg : (11620113 / 500000000) ≤ -Real.log (244256936911 / 250000000000) ∧
    -Real.log (244256936911 / 250000000000) ≤ (23240227 / 1000000000) := by
  have h := checkLog_sound (w := (5743063089 / 494256936911)) (n := 12)
    (lo := (11620113 / 500000000)) (hi := (23240227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244256936911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244256936911) = 1/(244256936911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9730 : Bounds (-23240227 / 1000000000) (-11620113 / 500000000) (Real.log (244256936911 / 250000000000)) := by
  have h := reflection_log_9730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9731_neg : (38185717 / 125000000) ≤ -Real.log (250000000000 / 339321031453) ∧
    -Real.log (250000000000 / 339321031453) ≤ (305485737 / 1000000000) := by
  have h := checkLog_sound (w := (89321031453 / 589321031453)) (n := 12)
    (lo := (38185717 / 125000000)) (hi := (305485737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339321031453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339321031453 / 250000000000) = 1/(250000000000 / 339321031453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9731 : Bounds (38185717 / 125000000) (305485737 / 1000000000) (Real.log (339321031453 / 250000000000)) := by
  have h := reflection_log_9731_neg
  have he : Real.log (339321031453 / 250000000000) = -Real.log (250000000000 / 339321031453) := by
    rw [show ((339321031453 / 250000000000) : ℝ) = ((250000000000 / 339321031453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9732_neg : (76656507 / 250000000) ≤ -Real.log (62500000000 / 84927044253) ∧
    -Real.log (62500000000 / 84927044253) ≤ (306626029 / 1000000000) := by
  have h := checkLog_sound (w := (22427044253 / 147427044253)) (n := 12)
    (lo := (76656507 / 250000000)) (hi := (306626029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84927044253 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84927044253 / 62500000000) = 1/(62500000000 / 84927044253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9732 : Bounds (76656507 / 250000000) (306626029 / 1000000000) (Real.log (84927044253 / 62500000000)) := by
  have h := reflection_log_9732_neg
  have he : Real.log (84927044253 / 62500000000) = -Real.log (62500000000 / 84927044253) := by
    rw [show ((84927044253 / 62500000000) : ℝ) = ((62500000000 / 84927044253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9733_neg : (615744131 / 1000000000) ≤ -Real.log (500000000000 / 925516749821) ∧
    -Real.log (500000000000 / 925516749821) ≤ (153936033 / 250000000) := by
  have h := checkLog_sound (w := (425516749821 / 1425516749821)) (n := 12)
    (lo := (615744131 / 1000000000)) (hi := (153936033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925516749821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925516749821 / 500000000000) = 1/(500000000000 / 925516749821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9733 : Bounds (615744131 / 1000000000) (153936033 / 250000000) (Real.log (925516749821 / 500000000000)) := by
  have h := reflection_log_9733_neg
  have he : Real.log (925516749821 / 500000000000) = -Real.log (500000000000 / 925516749821) := by
    rw [show ((925516749821 / 500000000000) : ℝ) = ((500000000000 / 925516749821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9734_neg : (616842129 / 1000000000) ≤ -Real.log (250000000000 / 463266761769) ∧
    -Real.log (250000000000 / 463266761769) ≤ (61684213 / 100000000) := by
  have h := checkLog_sound (w := (213266761769 / 713266761769)) (n := 12)
    (lo := (616842129 / 1000000000)) (hi := (61684213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463266761769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463266761769 / 250000000000) = 1/(250000000000 / 463266761769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9734 : Bounds (616842129 / 1000000000) (61684213 / 100000000) (Real.log (463266761769 / 250000000000)) := by
  have h := reflection_log_9734_neg
  have he : Real.log (463266761769 / 250000000000) = -Real.log (250000000000 / 463266761769) := by
    rw [show ((463266761769 / 250000000000) : ℝ) = ((250000000000 / 463266761769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9735_neg : (10479183 / 40000000) ≤ -Real.log (2000 / 2599) ∧
    -Real.log (2000 / 2599) ≤ (32747447 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4599)) (n := 12)
    (lo := (10479183 / 40000000)) (hi := (32747447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2599 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2599 / 2000) = 1/(2000 / 2599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9735 : Bounds (10479183 / 40000000) (32747447 / 125000000) (Real.log (2599 / 2000)) := by
  have h := reflection_log_9735_neg
  have he : Real.log (2599 / 2000) = -Real.log (2000 / 2599) := by
    rw [show ((2599 / 2000) : ℝ) = ((2000 / 2599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9736_neg : (355960913 / 1000000000) ≤ -Real.log (1401 / 2000) ∧
    -Real.log (1401 / 2000) ≤ (177980457 / 500000000) := by
  have h := checkLog_sound (w := (599 / 3401)) (n := 12)
    (lo := (355960913 / 1000000000)) (hi := (177980457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1401) = 1/(1401 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9736 : Bounds (-177980457 / 500000000) (-355960913 / 1000000000) (Real.log (1401 / 2000)) := by
  have h := reflection_log_9736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9737_neg : (59891 / 200000000) ≤ -Real.log (2000000 / 2000599) ∧
    -Real.log (2000000 / 2000599) ≤ (4679 / 15625000) := by
  have h := checkLog_sound (w := (599 / 4000599)) (n := 12)
    (lo := (59891 / 200000000)) (hi := (4679 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000599 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000599 / 2000000) = 1/(2000000 / 2000599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9737 : Bounds (59891 / 200000000) (4679 / 15625000) (Real.log (2000599 / 2000000)) := by
  have h := reflection_log_9737_neg
  have he : Real.log (2000599 / 2000000) = -Real.log (2000000 / 2000599) := by
    rw [show ((2000599 / 2000000) : ℝ) = ((2000000 / 2000599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9738_neg : (37443 / 125000000) ≤ -Real.log (1999401 / 2000000) ∧
    -Real.log (1999401 / 2000000) ≤ (59909 / 200000000) := by
  have h := checkLog_sound (w := (599 / 3999401)) (n := 12)
    (lo := (37443 / 125000000)) (hi := (59909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999401) = 1/(1999401 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9738 : Bounds (-59909 / 200000000) (-37443 / 125000000) (Real.log (1999401 / 2000000)) := by
  have h := reflection_log_9738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9739_neg : (28270049 / 200000000) ≤ -Real.log (250000 / 287957) ∧
    -Real.log (250000 / 287957) ≤ (70675123 / 500000000) := by
  have h := checkLog_sound (w := (37957 / 537957)) (n := 12)
    (lo := (28270049 / 200000000)) (hi := (70675123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287957 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287957 / 250000) = 1/(250000 / 287957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9739 : Bounds (28270049 / 200000000) (70675123 / 500000000) (Real.log (287957 / 250000)) := by
  have h := reflection_log_9739_neg
  have he : Real.log (287957 / 250000) = -Real.log (250000 / 287957) := by
    rw [show ((287957 / 250000) : ℝ) = ((250000 / 287957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9740_neg : (164671833 / 1000000000) ≤ -Real.log (212043 / 250000) ∧
    -Real.log (212043 / 250000) ≤ (82335917 / 500000000) := by
  have h := checkLog_sound (w := (37957 / 462043)) (n := 12)
    (lo := (164671833 / 1000000000)) (hi := (82335917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212043) = 1/(212043 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9740 : Bounds (-82335917 / 500000000) (-164671833 / 1000000000) (Real.log (212043 / 250000)) := by
  have h := reflection_log_9740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9741_neg : (5673383 / 40000000) ≤ -Real.log (500000 / 576193) ∧
    -Real.log (500000 / 576193) ≤ (8864661 / 62500000) := by
  have h := checkLog_sound (w := (76193 / 1076193)) (n := 12)
    (lo := (5673383 / 40000000)) (hi := (8864661 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576193 / 500000) = 1/(500000 / 576193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9741 : Bounds (5673383 / 40000000) (8864661 / 62500000) (Real.log (576193 / 500000)) := by
  have h := reflection_log_9741_neg
  have he : Real.log (576193 / 500000) = -Real.log (500000 / 576193) := by
    rw [show ((576193 / 500000) : ℝ) = ((500000 / 576193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9742_neg : (33065987 / 200000000) ≤ -Real.log (423807 / 500000) ∧
    -Real.log (423807 / 500000) ≤ (10333121 / 62500000) := by
  have h := checkLog_sound (w := (76193 / 923807)) (n := 12)
    (lo := (33065987 / 200000000)) (hi := (10333121 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423807) = 1/(423807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9742 : Bounds (-10333121 / 62500000) (-33065987 / 200000000) (Real.log (423807 / 500000)) := by
  have h := reflection_log_9742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9743_neg : (23495359 / 1000000000) ≤ -Real.log (244194626751 / 250000000000) ∧
    -Real.log (244194626751 / 250000000000) ≤ (73423 / 3125000) := by
  have h := checkLog_sound (w := (5805373249 / 494194626751)) (n := 12)
    (lo := (23495359 / 1000000000)) (hi := (73423 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244194626751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244194626751) = 1/(244194626751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9743 : Bounds (-73423 / 3125000) (-23495359 / 1000000000) (Real.log (244194626751 / 250000000000)) := by
  have h := reflection_log_9743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9744_neg : (23321587 / 1000000000) ≤ -Real.log (61059266151 / 62500000000) ∧
    -Real.log (61059266151 / 62500000000) ≤ (5830397 / 250000000) := by
  have h := checkLog_sound (w := (1440733849 / 123559266151)) (n := 12)
    (lo := (23321587 / 1000000000)) (hi := (5830397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61059266151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61059266151) = 1/(61059266151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9744 : Bounds (-5830397 / 250000000) (-23321587 / 1000000000) (Real.log (61059266151 / 62500000000)) := by
  have h := reflection_log_9744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9745_neg : (306022079 / 1000000000) ≤ -Real.log (25000000000 / 33950307249) ∧
    -Real.log (25000000000 / 33950307249) ≤ (956319 / 3125000) := by
  have h := checkLog_sound (w := (8950307249 / 58950307249)) (n := 12)
    (lo := (306022079 / 1000000000)) (hi := (956319 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33950307249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33950307249 / 25000000000) = 1/(25000000000 / 33950307249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9745 : Bounds (306022079 / 1000000000) (956319 / 3125000) (Real.log (33950307249 / 25000000000)) := by
  have h := reflection_log_9745_neg
  have he : Real.log (33950307249 / 25000000000) = -Real.log (25000000000 / 33950307249) := by
    rw [show ((33950307249 / 25000000000) : ℝ) = ((25000000000 / 33950307249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9746_neg : (307164511 / 1000000000) ≤ -Real.log (500000000000 / 679782306569) ∧
    -Real.log (500000000000 / 679782306569) ≤ (9598891 / 31250000) := by
  have h := checkLog_sound (w := (179782306569 / 1179782306569)) (n := 12)
    (lo := (307164511 / 1000000000)) (hi := (9598891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679782306569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679782306569 / 500000000000) = 1/(500000000000 / 679782306569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9746 : Bounds (307164511 / 1000000000) (9598891 / 31250000) (Real.log (679782306569 / 500000000000)) := by
  have h := reflection_log_9746_neg
  have he : Real.log (679782306569 / 500000000000) = -Real.log (500000000000 / 679782306569) := by
    rw [show ((679782306569 / 500000000000) : ℝ) = ((500000000000 / 679782306569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9747_neg : (616842129 / 1000000000) ≤ -Real.log (500000000000 / 926533523537) ∧
    -Real.log (500000000000 / 926533523537) ≤ (61684213 / 100000000) := by
  have h := checkLog_sound (w := (426533523537 / 1426533523537)) (n := 12)
    (lo := (616842129 / 1000000000)) (hi := (61684213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926533523537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926533523537 / 500000000000) = 1/(500000000000 / 926533523537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9747 : Bounds (616842129 / 1000000000) (61684213 / 100000000) (Real.log (926533523537 / 500000000000)) := by
  have h := reflection_log_9747_neg
  have he : Real.log (926533523537 / 500000000000) = -Real.log (500000000000 / 926533523537) := by
    rw [show ((926533523537 / 500000000000) : ℝ) = ((500000000000 / 926533523537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9748_neg : (77242561 / 125000000) ≤ -Real.log (500000000000 / 927551748751) ∧
    -Real.log (500000000000 / 927551748751) ≤ (617940489 / 1000000000) := by
  have h := checkLog_sound (w := (427551748751 / 1427551748751)) (n := 12)
    (lo := (77242561 / 125000000)) (hi := (617940489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927551748751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927551748751 / 500000000000) = 1/(500000000000 / 927551748751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9748 : Bounds (77242561 / 125000000) (617940489 / 1000000000) (Real.log (927551748751 / 500000000000)) := by
  have h := reflection_log_9748_neg
  have he : Real.log (927551748751 / 500000000000) = -Real.log (500000000000 / 927551748751) := by
    rw [show ((927551748751 / 500000000000) : ℝ) = ((500000000000 / 927551748751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9749_neg : (32795533 / 125000000) ≤ -Real.log (10 / 13) ∧
    -Real.log (10 / 13) ≤ (52472853 / 200000000) := by
  have h := checkLog_sound (w := (3 / 23)) (n := 12)
    (lo := (32795533 / 125000000)) (hi := (52472853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 10) = 1/(10 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9749 : Bounds (32795533 / 125000000) (52472853 / 200000000) (Real.log (13 / 10)) := by
  have h := reflection_log_9749_neg
  have he : Real.log (13 / 10) = -Real.log (10 / 13) := by
    rw [show ((13 / 10) : ℝ) = ((10 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9750_neg : (356674943 / 1000000000) ≤ -Real.log (7 / 10) ∧
    -Real.log (7 / 10) ≤ (2786523 / 7812500) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 7) = 1/(7 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9750 : Bounds (-2786523 / 7812500) (-356674943 / 1000000000) (Real.log (7 / 10)) := by
  have h := reflection_log_9750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9751_neg : (59991 / 200000000) ≤ -Real.log (10000 / 10003) ∧
    -Real.log (10000 / 10003) ≤ (74989 / 250000000) := by
  have h := checkLog_sound (w := (3 / 20003)) (n := 12)
    (lo := (59991 / 200000000)) (hi := (74989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10003 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10003 / 10000) = 1/(10000 / 10003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9751 : Bounds (59991 / 200000000) (74989 / 250000000) (Real.log (10003 / 10000)) := by
  have h := reflection_log_9751_neg
  have he : Real.log (10003 / 10000) = -Real.log (10000 / 10003) := by
    rw [show ((10003 / 10000) : ℝ) = ((10000 / 10003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9752_neg : (60009 / 200000000) ≤ -Real.log (9997 / 10000) ∧
    -Real.log (9997 / 10000) ≤ (150023 / 500000000) := by
  have h := checkLog_sound (w := (3 / 19997)) (n := 12)
    (lo := (60009 / 200000000)) (hi := (150023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9997) = 1/(9997 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9752 : Bounds (-150023 / 500000000) (-60009 / 200000000) (Real.log (9997 / 10000)) := by
  have h := reflection_log_9752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9753_neg : (17697319 / 125000000) ≤ -Real.log (1000000 / 1152091) ∧
    -Real.log (1000000 / 1152091) ≤ (141578553 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 2152091)) (n := 12)
    (lo := (17697319 / 125000000)) (hi := (141578553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152091 / 1000000) = 1/(1000000 / 1152091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9753 : Bounds (17697319 / 125000000) (141578553 / 1000000000) (Real.log (1152091 / 1000000)) := by
  have h := reflection_log_9753_neg
  have he : Real.log (1152091 / 1000000) = -Real.log (1000000 / 1152091) := by
    rw [show ((1152091 / 1000000) : ℝ) = ((1000000 / 1152091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9754_neg : (4124549 / 25000000) ≤ -Real.log (847909 / 1000000) ∧
    -Real.log (847909 / 1000000) ≤ (164981961 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 1847909)) (n := 12)
    (lo := (4124549 / 25000000)) (hi := (164981961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847909) = 1/(847909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9754 : Bounds (-164981961 / 1000000000) (-4124549 / 25000000) (Real.log (847909 / 1000000)) := by
  have h := reflection_log_9754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9755_neg : (142062771 / 1000000000) ≤ -Real.log (1000000 / 1152649) ∧
    -Real.log (1000000 / 1152649) ≤ (35515693 / 250000000) := by
  have h := checkLog_sound (w := (152649 / 2152649)) (n := 12)
    (lo := (142062771 / 1000000000)) (hi := (35515693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152649 / 1000000) = 1/(1000000 / 1152649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9755 : Bounds (142062771 / 1000000000) (35515693 / 250000000) (Real.log (1152649 / 1000000)) := by
  have h := reflection_log_9755_neg
  have he : Real.log (1152649 / 1000000) = -Real.log (1000000 / 1152649) := by
    rw [show ((1152649 / 1000000) : ℝ) = ((1000000 / 1152649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9756_neg : (82820133 / 500000000) ≤ -Real.log (847351 / 1000000) ∧
    -Real.log (847351 / 1000000) ≤ (165640267 / 1000000000) := by
  have h := checkLog_sound (w := (152649 / 1847351)) (n := 12)
    (lo := (82820133 / 500000000)) (hi := (165640267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847351) = 1/(847351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9756 : Bounds (-165640267 / 1000000000) (-82820133 / 500000000) (Real.log (847351 / 1000000)) := by
  have h := reflection_log_9756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9757_neg : (11788747 / 500000000) ≤ -Real.log (976698282799 / 1000000000000) ∧
    -Real.log (976698282799 / 1000000000000) ≤ (4715499 / 200000000) := by
  have h := checkLog_sound (w := (23301717201 / 1976698282799)) (n := 12)
    (lo := (11788747 / 500000000)) (hi := (4715499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976698282799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976698282799) = 1/(976698282799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9757 : Bounds (-4715499 / 200000000) (-11788747 / 500000000) (Real.log (976698282799 / 1000000000000)) := by
  have h := reflection_log_9757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9758_neg : (1462713 / 62500000) ≤ -Real.log (976868327719 / 1000000000000) ∧
    -Real.log (976868327719 / 1000000000000) ≤ (23403409 / 1000000000) := by
  have h := checkLog_sound (w := (23131672281 / 1976868327719)) (n := 12)
    (lo := (1462713 / 62500000)) (hi := (23403409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976868327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976868327719) = 1/(976868327719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9758 : Bounds (-23403409 / 1000000000) (-1462713 / 62500000) (Real.log (976868327719 / 1000000000000)) := by
  have h := reflection_log_9758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9759_neg : (598751 / 1953125) ≤ -Real.log (62500000000 / 84921480371) ∧
    -Real.log (62500000000 / 84921480371) ≤ (306560513 / 1000000000) := by
  have h := checkLog_sound (w := (22421480371 / 147421480371)) (n := 12)
    (lo := (598751 / 1953125)) (hi := (306560513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84921480371 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84921480371 / 62500000000) = 1/(62500000000 / 84921480371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9759 : Bounds (598751 / 1953125) (306560513 / 1000000000) (Real.log (84921480371 / 62500000000)) := by
  have h := reflection_log_9759_neg
  have he : Real.log (84921480371 / 62500000000) = -Real.log (62500000000 / 84921480371) := by
    rw [show ((84921480371 / 62500000000) : ℝ) = ((62500000000 / 84921480371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9760_neg : (153851519 / 500000000) ≤ -Real.log (500000000000 / 680148486283) ∧
    -Real.log (500000000000 / 680148486283) ≤ (307703039 / 1000000000) := by
  have h := checkLog_sound (w := (180148486283 / 1180148486283)) (n := 12)
    (lo := (153851519 / 500000000)) (hi := (307703039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680148486283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680148486283 / 500000000000) = 1/(500000000000 / 680148486283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9760 : Bounds (153851519 / 500000000) (307703039 / 1000000000) (Real.log (680148486283 / 500000000000)) := by
  have h := reflection_log_9760_neg
  have he : Real.log (680148486283 / 500000000000) = -Real.log (500000000000 / 680148486283) := by
    rw [show ((680148486283 / 500000000000) : ℝ) = ((500000000000 / 680148486283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9761_neg : (77242561 / 125000000) ≤ -Real.log (400000000 / 742041399) ∧
    -Real.log (400000000 / 742041399) ≤ (617940489 / 1000000000) := by
  have h := checkLog_sound (w := (342041399 / 1142041399)) (n := 12)
    (lo := (77242561 / 125000000)) (hi := (617940489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742041399 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742041399 / 400000000) = 1/(400000000 / 742041399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9761 : Bounds (77242561 / 125000000) (617940489 / 1000000000) (Real.log (742041399 / 400000000)) := by
  have h := reflection_log_9761_neg
  have he : Real.log (742041399 / 400000000) = -Real.log (400000000 / 742041399) := by
    rw [show ((742041399 / 400000000) : ℝ) = ((400000000 / 742041399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9762_neg : (77379901 / 125000000) ≤ -Real.log (125000000000 / 232142857143) ∧
    -Real.log (125000000000 / 232142857143) ≤ (619039209 / 1000000000) := by
  have h := checkLog_sound (w := (107142857143 / 357142857143)) (n := 12)
    (lo := (77379901 / 125000000)) (hi := (619039209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232142857143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232142857143 / 125000000000) = 1/(125000000000 / 232142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9762 : Bounds (77379901 / 125000000) (619039209 / 1000000000) (Real.log (232142857143 / 125000000000)) := by
  have h := reflection_log_9762_neg
  have he : Real.log (232142857143 / 125000000000) = -Real.log (125000000000 / 232142857143) := by
    rw [show ((232142857143 / 125000000000) : ℝ) = ((125000000000 / 232142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9763_neg : (263133199 / 1000000000) ≤ -Real.log (1000 / 1301) ∧
    -Real.log (1000 / 1301) ≤ (657833 / 2500000) := by
  have h := checkLog_sound (w := (301 / 2301)) (n := 12)
    (lo := (263133199 / 1000000000)) (hi := (657833 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1000) = 1/(1000 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9763 : Bounds (263133199 / 1000000000) (657833 / 2500000) (Real.log (1301 / 1000)) := by
  have h := reflection_log_9763_neg
  have he : Real.log (1301 / 1000) = -Real.log (1000 / 1301) := by
    rw [show ((1301 / 1000) : ℝ) = ((1000 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9764_neg : (44763067 / 125000000) ≤ -Real.log (699 / 1000) ∧
    -Real.log (699 / 1000) ≤ (358104537 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1699)) (n := 12)
    (lo := (44763067 / 125000000)) (hi := (358104537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 699) = 1/(699 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9764 : Bounds (-358104537 / 1000000000) (-44763067 / 125000000) (Real.log (699 / 1000)) := by
  have h := reflection_log_9764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9765_neg : (150477 / 500000000) ≤ -Real.log (1000000 / 1000301) ∧
    -Real.log (1000000 / 1000301) ≤ (60191 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2000301)) (n := 12)
    (lo := (150477 / 500000000)) (hi := (60191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000301 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000301 / 1000000) = 1/(1000000 / 1000301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9765 : Bounds (150477 / 500000000) (60191 / 200000000) (Real.log (1000301 / 1000000)) := by
  have h := reflection_log_9765_neg
  have he : Real.log (1000301 / 1000000) = -Real.log (1000000 / 1000301) := by
    rw [show ((1000301 / 1000000) : ℝ) = ((1000000 / 1000301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9766_neg : (60209 / 200000000) ≤ -Real.log (999699 / 1000000) ∧
    -Real.log (999699 / 1000000) ≤ (150523 / 500000000) := by
  have h := checkLog_sound (w := (301 / 1999699)) (n := 12)
    (lo := (60209 / 200000000)) (hi := (150523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999699) = 1/(999699 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9766 : Bounds (-150523 / 500000000) (-60209 / 200000000) (Real.log (999699 / 1000000)) := by
  have h := reflection_log_9766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9767_neg : (70902969 / 500000000) ≤ -Real.log (1000000 / 1152353) ∧
    -Real.log (1000000 / 1152353) ≤ (141805939 / 1000000000) := by
  have h := checkLog_sound (w := (152353 / 2152353)) (n := 12)
    (lo := (70902969 / 500000000)) (hi := (141805939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152353 / 1000000) = 1/(1000000 / 1152353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9767 : Bounds (70902969 / 500000000) (141805939 / 1000000000) (Real.log (1152353 / 1000000)) := by
  have h := reflection_log_9767_neg
  have he : Real.log (1152353 / 1000000) = -Real.log (1000000 / 1152353) := by
    rw [show ((1152353 / 1000000) : ℝ) = ((1000000 / 1152353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9768_neg : (165291003 / 1000000000) ≤ -Real.log (847647 / 1000000) ∧
    -Real.log (847647 / 1000000) ≤ (41322751 / 250000000) := by
  have h := checkLog_sound (w := (152353 / 1847647)) (n := 12)
    (lo := (165291003 / 1000000000)) (hi := (41322751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847647) = 1/(847647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9768 : Bounds (-41322751 / 250000000) (-165291003 / 1000000000) (Real.log (847647 / 1000000)) := by
  have h := reflection_log_9768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9769_neg : (142519007 / 1000000000) ≤ -Real.log (40000 / 46127) ∧
    -Real.log (40000 / 46127) ≤ (4453719 / 31250000) := by
  have h := checkLog_sound (w := (6127 / 86127)) (n := 12)
    (lo := (142519007 / 1000000000)) (hi := (4453719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46127 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46127 / 40000) = 1/(40000 / 46127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9769 : Bounds (142519007 / 1000000000) (4453719 / 31250000) (Real.log (46127 / 40000)) := by
  have h := reflection_log_9769_neg
  have he : Real.log (46127 / 40000) = -Real.log (40000 / 46127) := by
    rw [show ((46127 / 40000) : ℝ) = ((40000 / 46127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9770_neg : (166261217 / 1000000000) ≤ -Real.log (33873 / 40000) ∧
    -Real.log (33873 / 40000) ≤ (83130609 / 500000000) := by
  have h := checkLog_sound (w := (6127 / 73873)) (n := 12)
    (lo := (166261217 / 1000000000)) (hi := (83130609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33873) = 1/(33873 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9770 : Bounds (-83130609 / 500000000) (-166261217 / 1000000000) (Real.log (33873 / 40000)) := by
  have h := reflection_log_9770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9771_neg : (23742209 / 1000000000) ≤ -Real.log (1562459871 / 1600000000) ∧
    -Real.log (1562459871 / 1600000000) ≤ (2374221 / 100000000) := by
  have h := checkLog_sound (w := (37540129 / 3162459871)) (n := 12)
    (lo := (23742209 / 1000000000)) (hi := (2374221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1562459871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1562459871) = 1/(1562459871 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9771 : Bounds (-2374221 / 100000000) (-23742209 / 1000000000) (Real.log (1562459871 / 1600000000)) := by
  have h := reflection_log_9771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9772_neg : (2935633 / 125000000) ≤ -Real.log (976788563391 / 1000000000000) ∧
    -Real.log (976788563391 / 1000000000000) ≤ (4697013 / 200000000) := by
  have h := checkLog_sound (w := (23211436609 / 1976788563391)) (n := 12)
    (lo := (2935633 / 125000000)) (hi := (4697013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976788563391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976788563391) = 1/(976788563391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9772 : Bounds (-4697013 / 200000000) (-2935633 / 125000000) (Real.log (976788563391 / 1000000000000)) := by
  have h := reflection_log_9772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9773_neg : (153548471 / 500000000) ≤ -Real.log (500000000000 / 679736376109) ∧
    -Real.log (500000000000 / 679736376109) ≤ (307096943 / 1000000000) := by
  have h := checkLog_sound (w := (179736376109 / 1179736376109)) (n := 12)
    (lo := (153548471 / 500000000)) (hi := (307096943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679736376109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679736376109 / 500000000000) = 1/(500000000000 / 679736376109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9773 : Bounds (153548471 / 500000000) (307096943 / 1000000000) (Real.log (679736376109 / 500000000000)) := by
  have h := reflection_log_9773_neg
  have he : Real.log (679736376109 / 500000000000) = -Real.log (500000000000 / 679736376109) := by
    rw [show ((679736376109 / 500000000000) : ℝ) = ((500000000000 / 679736376109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9774_neg : (4824691 / 15625000) ≤ -Real.log (500000000000 / 680881528061) ∧
    -Real.log (500000000000 / 680881528061) ≤ (12351209 / 40000000) := by
  have h := checkLog_sound (w := (180881528061 / 1180881528061)) (n := 12)
    (lo := (4824691 / 15625000)) (hi := (12351209 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680881528061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680881528061 / 500000000000) = 1/(500000000000 / 680881528061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9774 : Bounds (4824691 / 15625000) (12351209 / 40000000) (Real.log (680881528061 / 500000000000)) := by
  have h := reflection_log_9774_neg
  have he : Real.log (680881528061 / 500000000000) = -Real.log (500000000000 / 680881528061) := by
    rw [show ((680881528061 / 500000000000) : ℝ) = ((500000000000 / 680881528061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9775_neg : (77379901 / 125000000) ≤ -Real.log (500000000000 / 928571428571) ∧
    -Real.log (500000000000 / 928571428571) ≤ (619039209 / 1000000000) := by
  have h := checkLog_sound (w := (428571428571 / 1428571428571)) (n := 12)
    (lo := (77379901 / 125000000)) (hi := (619039209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928571428571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928571428571 / 500000000000) = 1/(500000000000 / 928571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9775 : Bounds (77379901 / 125000000) (619039209 / 1000000000) (Real.log (928571428571 / 500000000000)) := by
  have h := reflection_log_9775_neg
  have he : Real.log (928571428571 / 500000000000) = -Real.log (500000000000 / 928571428571) := by
    rw [show ((928571428571 / 500000000000) : ℝ) = ((500000000000 / 928571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9776_neg : (77654717 / 125000000) ≤ -Real.log (500000000000 / 930615164521) ∧
    -Real.log (500000000000 / 930615164521) ≤ (621237737 / 1000000000) := by
  have h := checkLog_sound (w := (430615164521 / 1430615164521)) (n := 12)
    (lo := (77654717 / 125000000)) (hi := (621237737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930615164521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930615164521 / 500000000000) = 1/(500000000000 / 930615164521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9776 : Bounds (77654717 / 125000000) (621237737 / 1000000000) (Real.log (930615164521 / 500000000000)) := by
  have h := reflection_log_9776_neg
  have he : Real.log (930615164521 / 500000000000) = -Real.log (500000000000 / 930615164521) := by
    rw [show ((930615164521 / 500000000000) : ℝ) = ((500000000000 / 930615164521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9777_neg : (263901543 / 1000000000) ≤ -Real.log (500 / 651) ∧
    -Real.log (500 / 651) ≤ (32987693 / 125000000) := by
  have h := checkLog_sound (w := (151 / 1151)) (n := 12)
    (lo := (263901543 / 1000000000)) (hi := (32987693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 500) = 1/(500 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9777 : Bounds (263901543 / 1000000000) (32987693 / 125000000) (Real.log (651 / 500)) := by
  have h := reflection_log_9777_neg
  have he : Real.log (651 / 500) = -Real.log (500 / 651) := by
    rw [show ((651 / 500) : ℝ) = ((500 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9778_neg : (22471011 / 62500000) ≤ -Real.log (349 / 500) ∧
    -Real.log (349 / 500) ≤ (359536177 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 849)) (n := 12)
    (lo := (22471011 / 62500000)) (hi := (359536177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 349) = 1/(349 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9778 : Bounds (-359536177 / 1000000000) (-22471011 / 62500000) (Real.log (349 / 500)) := by
  have h := reflection_log_9778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9779_neg : (150977 / 500000000) ≤ -Real.log (500000 / 500151) ∧
    -Real.log (500000 / 500151) ≤ (60391 / 200000000) := by
  have h := checkLog_sound (w := (151 / 1000151)) (n := 12)
    (lo := (150977 / 500000000)) (hi := (60391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500151 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500151 / 500000) = 1/(500000 / 500151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9779 : Bounds (150977 / 500000000) (60391 / 200000000) (Real.log (500151 / 500000)) := by
  have h := reflection_log_9779_neg
  have he : Real.log (500151 / 500000) = -Real.log (500000 / 500151) := by
    rw [show ((500151 / 500000) : ℝ) = ((500000 / 500151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9780_neg : (60409 / 200000000) ≤ -Real.log (499849 / 500000) ∧
    -Real.log (499849 / 500000) ≤ (151023 / 500000000) := by
  have h := checkLog_sound (w := (151 / 999849)) (n := 12)
    (lo := (60409 / 200000000)) (hi := (151023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499849) = 1/(499849 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9780 : Bounds (-151023 / 500000000) (-60409 / 200000000) (Real.log (499849 / 500000)) := by
  have h := reflection_log_9780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9781_neg : (8891339 / 62500000) ≤ -Real.log (500000 / 576439) ∧
    -Real.log (500000 / 576439) ≤ (5690457 / 40000000) := by
  have h := checkLog_sound (w := (76439 / 1076439)) (n := 12)
    (lo := (8891339 / 62500000)) (hi := (5690457 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576439 / 500000) = 1/(500000 / 576439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9781 : Bounds (8891339 / 62500000) (5690457 / 40000000) (Real.log (576439 / 500000)) := by
  have h := reflection_log_9781_neg
  have he : Real.log (576439 / 500000) = -Real.log (500000 / 576439) := by
    rw [show ((576439 / 500000) : ℝ) = ((500000 / 576439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9782_neg : (41477639 / 250000000) ≤ -Real.log (423561 / 500000) ∧
    -Real.log (423561 / 500000) ≤ (165910557 / 1000000000) := by
  have h := checkLog_sound (w := (76439 / 923561)) (n := 12)
    (lo := (41477639 / 250000000)) (hi := (165910557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423561) = 1/(423561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9782 : Bounds (-165910557 / 1000000000) (-41477639 / 250000000) (Real.log (423561 / 500000)) := by
  have h := reflection_log_9782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9783_neg : (28595007 / 200000000) ≤ -Real.log (1000000 / 1153701) ∧
    -Real.log (1000000 / 1153701) ≤ (35743759 / 250000000) := by
  have h := checkLog_sound (w := (153701 / 2153701)) (n := 12)
    (lo := (28595007 / 200000000)) (hi := (35743759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153701 / 1000000) = 1/(1000000 / 1153701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9783 : Bounds (28595007 / 200000000) (35743759 / 250000000) (Real.log (1153701 / 1000000)) := by
  have h := reflection_log_9783_neg
  have he : Real.log (1153701 / 1000000) = -Real.log (1000000 / 1153701) := by
    rw [show ((1153701 / 1000000) : ℝ) = ((1000000 / 1153701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9784_neg : (166882553 / 1000000000) ≤ -Real.log (846299 / 1000000) ∧
    -Real.log (846299 / 1000000) ≤ (83441277 / 500000000) := by
  have h := checkLog_sound (w := (153701 / 1846299)) (n := 12)
    (lo := (166882553 / 1000000000)) (hi := (83441277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846299) = 1/(846299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9784 : Bounds (-83441277 / 500000000) (-166882553 / 1000000000) (Real.log (846299 / 1000000)) := by
  have h := reflection_log_9784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9785_neg : (11953759 / 500000000) ≤ -Real.log (976376002599 / 1000000000000) ∧
    -Real.log (976376002599 / 1000000000000) ≤ (23907519 / 1000000000) := by
  have h := checkLog_sound (w := (23623997401 / 1976376002599)) (n := 12)
    (lo := (11953759 / 500000000)) (hi := (23907519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976376002599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976376002599) = 1/(976376002599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9785 : Bounds (-23907519 / 1000000000) (-11953759 / 500000000) (Real.log (976376002599 / 1000000000000)) := by
  have h := reflection_log_9785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9786_neg : (5912283 / 250000000) ≤ -Real.log (244157079279 / 250000000000) ∧
    -Real.log (244157079279 / 250000000000) ≤ (23649133 / 1000000000) := by
  have h := checkLog_sound (w := (5842920721 / 494157079279)) (n := 12)
    (lo := (5912283 / 250000000)) (hi := (23649133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244157079279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244157079279) = 1/(244157079279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9786 : Bounds (-23649133 / 1000000000) (-5912283 / 250000000) (Real.log (244157079279 / 250000000000)) := by
  have h := reflection_log_9786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9787_neg : (308171981 / 1000000000) ≤ -Real.log (500000000000 / 680467512353) ∧
    -Real.log (500000000000 / 680467512353) ≤ (154085991 / 500000000) := by
  have h := checkLog_sound (w := (180467512353 / 1180467512353)) (n := 12)
    (lo := (308171981 / 1000000000)) (hi := (154085991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680467512353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680467512353 / 500000000000) = 1/(500000000000 / 680467512353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9787 : Bounds (308171981 / 1000000000) (154085991 / 500000000) (Real.log (680467512353 / 500000000000)) := by
  have h := reflection_log_9787_neg
  have he : Real.log (680467512353 / 500000000000) = -Real.log (500000000000 / 680467512353) := by
    rw [show ((680467512353 / 500000000000) : ℝ) = ((500000000000 / 680467512353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9788_neg : (309857589 / 1000000000) ≤ -Real.log (250000000000 / 340807740527) ∧
    -Real.log (250000000000 / 340807740527) ≤ (30985759 / 100000000) := by
  have h := checkLog_sound (w := (90807740527 / 590807740527)) (n := 12)
    (lo := (309857589 / 1000000000)) (hi := (30985759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340807740527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340807740527 / 250000000000) = 1/(250000000000 / 340807740527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9788 : Bounds (309857589 / 1000000000) (30985759 / 100000000) (Real.log (340807740527 / 250000000000)) := by
  have h := reflection_log_9788_neg
  have he : Real.log (340807740527 / 250000000000) = -Real.log (250000000000 / 340807740527) := by
    rw [show ((340807740527 / 250000000000) : ℝ) = ((250000000000 / 340807740527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9789_neg : (77654717 / 125000000) ≤ -Real.log (12500000000 / 23265379113) ∧
    -Real.log (12500000000 / 23265379113) ≤ (621237737 / 1000000000) := by
  have h := checkLog_sound (w := (10765379113 / 35765379113)) (n := 12)
    (lo := (77654717 / 125000000)) (hi := (621237737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23265379113 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23265379113 / 12500000000) = 1/(12500000000 / 23265379113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9789 : Bounds (77654717 / 125000000) (621237737 / 1000000000) (Real.log (23265379113 / 12500000000)) := by
  have h := reflection_log_9789_neg
  have he : Real.log (23265379113 / 12500000000) = -Real.log (12500000000 / 23265379113) := by
    rw [show ((23265379113 / 12500000000) : ℝ) = ((12500000000 / 23265379113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9790_neg : (15585943 / 25000000) ≤ -Real.log (500000000000 / 932664756447) ∧
    -Real.log (500000000000 / 932664756447) ≤ (623437721 / 1000000000) := by
  have h := checkLog_sound (w := (432664756447 / 1432664756447)) (n := 12)
    (lo := (15585943 / 25000000)) (hi := (623437721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932664756447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932664756447 / 500000000000) = 1/(500000000000 / 932664756447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9790 : Bounds (15585943 / 25000000) (623437721 / 1000000000) (Real.log (932664756447 / 500000000000)) := by
  have h := reflection_log_9790_neg
  have he : Real.log (932664756447 / 500000000000) = -Real.log (500000000000 / 932664756447) := by
    rw [show ((932664756447 / 500000000000) : ℝ) = ((500000000000 / 932664756447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9791_neg : (132334649 / 500000000) ≤ -Real.log (1000 / 1303) ∧
    -Real.log (1000 / 1303) ≤ (264669299 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 2303)) (n := 12)
    (lo := (132334649 / 500000000)) (hi := (264669299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303 / 1000) = 1/(1000 / 1303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9791 : Bounds (132334649 / 500000000) (264669299 / 1000000000) (Real.log (1303 / 1000)) := by
  have h := reflection_log_9791_neg
  have he : Real.log (1303 / 1000) = -Real.log (1000 / 1303) := by
    rw [show ((1303 / 1000) : ℝ) = ((1000 / 1303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
