import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7104_neg : (10650899 / 1000000000) ≤ -Real.log (989405620959 / 1000000000000) ∧
    -Real.log (989405620959 / 1000000000000) ≤ (106509 / 10000000) := by
  have h := checkLog_sound (w := (10594379041 / 1989405620959)) (n := 12)
    (lo := (10650899 / 1000000000)) (hi := (106509 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989405620959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989405620959) = 1/(989405620959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7104 : Bounds (-106509 / 10000000) (-10650899 / 1000000000) (Real.log (989405620959 / 1000000000000)) := by
  have h := reflection_log_7104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7105_neg : (41317927 / 200000000) ≤ -Real.log (500000000000 / 614738967149) ∧
    -Real.log (500000000000 / 614738967149) ≤ (51647409 / 250000000) := by
  have h := checkLog_sound (w := (114738967149 / 1114738967149)) (n := 12)
    (lo := (41317927 / 200000000)) (hi := (51647409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614738967149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614738967149 / 500000000000) = 1/(500000000000 / 614738967149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7105 : Bounds (41317927 / 200000000) (51647409 / 250000000) (Real.log (614738967149 / 500000000000)) := by
  have h := reflection_log_7105_neg
  have he : Real.log (614738967149 / 500000000000) = -Real.log (500000000000 / 614738967149) := by
    rw [show ((614738967149 / 500000000000) : ℝ) = ((500000000000 / 614738967149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7106_neg : (207519531 / 1000000000) ≤ -Real.log (250000000000 / 307655438089) ∧
    -Real.log (250000000000 / 307655438089) ≤ (51879883 / 250000000) := by
  have h := checkLog_sound (w := (57655438089 / 557655438089)) (n := 12)
    (lo := (207519531 / 1000000000)) (hi := (51879883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307655438089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307655438089 / 250000000000) = 1/(250000000000 / 307655438089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7106 : Bounds (207519531 / 1000000000) (51879883 / 250000000) (Real.log (307655438089 / 250000000000)) := by
  have h := reflection_log_7106_neg
  have he : Real.log (307655438089 / 250000000000) = -Real.log (250000000000 / 307655438089) := by
    rw [show ((307655438089 / 250000000000) : ℝ) = ((250000000000 / 307655438089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7107_neg : (207424487 / 500000000) ≤ -Real.log (3906250000 / 5914617379) ∧
    -Real.log (3906250000 / 5914617379) ≤ (16593959 / 40000000) := by
  have h := checkLog_sound (w := (2008367379 / 9820867379)) (n := 12)
    (lo := (207424487 / 500000000)) (hi := (16593959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5914617379 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5914617379 / 3906250000) = 1/(3906250000 / 5914617379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7107 : Bounds (207424487 / 500000000) (16593959 / 40000000) (Real.log (5914617379 / 3906250000)) := by
  have h := reflection_log_7107_neg
  have he : Real.log (5914617379 / 3906250000) = -Real.log (3906250000 / 5914617379) := by
    rw [show ((5914617379 / 3906250000) : ℝ) = ((3906250000 / 5914617379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7108_neg : (415892731 / 1000000000) ≤ -Real.log (500000000000 / 757861635221) ∧
    -Real.log (500000000000 / 757861635221) ≤ (103973183 / 250000000) := by
  have h := checkLog_sound (w := (257861635221 / 1257861635221)) (n := 12)
    (lo := (415892731 / 1000000000)) (hi := (103973183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757861635221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757861635221 / 500000000000) = 1/(500000000000 / 757861635221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7108 : Bounds (415892731 / 1000000000) (103973183 / 250000000) (Real.log (757861635221 / 500000000000)) := by
  have h := reflection_log_7108_neg
  have he : Real.log (757861635221 / 500000000000) = -Real.log (500000000000 / 757861635221) := by
    rw [show ((757861635221 / 500000000000) : ℝ) = ((500000000000 / 757861635221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7109_neg : (93447209 / 500000000) ≤ -Real.log (2000 / 2411) ∧
    -Real.log (2000 / 2411) ≤ (186894419 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 4411)) (n := 12)
    (lo := (93447209 / 500000000)) (hi := (186894419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2411 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2411 / 2000) = 1/(2000 / 2411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7109 : Bounds (93447209 / 500000000) (186894419 / 1000000000) (Real.log (2411 / 2000)) := by
  have h := reflection_log_7109_neg
  have he : Real.log (2411 / 2000) = -Real.log (2000 / 2411) := by
    rw [show ((2411 / 2000) : ℝ) = ((2000 / 2411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7110_neg : (230042293 / 1000000000) ≤ -Real.log (1589 / 2000) ∧
    -Real.log (1589 / 2000) ≤ (115021147 / 500000000) := by
  have h := checkLog_sound (w := (411 / 3589)) (n := 12)
    (lo := (230042293 / 1000000000)) (hi := (115021147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1589) = 1/(1589 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7110 : Bounds (-115021147 / 500000000) (-230042293 / 1000000000) (Real.log (1589 / 2000)) := by
  have h := reflection_log_7110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7111_neg : (102739 / 500000000) ≤ -Real.log (2000000 / 2000411) ∧
    -Real.log (2000000 / 2000411) ≤ (205479 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 4000411)) (n := 12)
    (lo := (102739 / 500000000)) (hi := (205479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000411 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000411 / 2000000) = 1/(2000000 / 2000411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7111 : Bounds (102739 / 500000000) (205479 / 1000000000) (Real.log (2000411 / 2000000)) := by
  have h := reflection_log_7111_neg
  have he : Real.log (2000411 / 2000000) = -Real.log (2000000 / 2000411) := by
    rw [show ((2000411 / 2000000) : ℝ) = ((2000000 / 2000411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7112_neg : (205521 / 1000000000) ≤ -Real.log (1999589 / 2000000) ∧
    -Real.log (1999589 / 2000000) ≤ (102761 / 500000000) := by
  have h := checkLog_sound (w := (411 / 3999589)) (n := 12)
    (lo := (205521 / 1000000000)) (hi := (102761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999589) = 1/(1999589 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7112 : Bounds (-102761 / 500000000) (-205521 / 1000000000) (Real.log (1999589 / 2000000)) := by
  have h := reflection_log_7112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7113_neg : (3068767 / 31250000) ≤ -Real.log (62500 / 68949) ∧
    -Real.log (62500 / 68949) ≤ (19640109 / 200000000) := by
  have h := checkLog_sound (w := (6449 / 131449)) (n := 12)
    (lo := (3068767 / 31250000)) (hi := (19640109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68949 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68949 / 62500) = 1/(62500 / 68949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7113 : Bounds (3068767 / 31250000) (19640109 / 200000000) (Real.log (68949 / 62500)) := by
  have h := reflection_log_7113_neg
  have he : Real.log (68949 / 62500) = -Real.log (62500 / 68949) := by
    rw [show ((68949 / 62500) : ℝ) = ((62500 / 68949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7114_neg : (54452283 / 500000000) ≤ -Real.log (56051 / 62500) ∧
    -Real.log (56051 / 62500) ≤ (108904567 / 1000000000) := by
  have h := checkLog_sound (w := (6449 / 118551)) (n := 12)
    (lo := (54452283 / 500000000)) (hi := (108904567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56051) = 1/(56051 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7114 : Bounds (-108904567 / 1000000000) (-54452283 / 500000000) (Real.log (56051 / 62500)) := by
  have h := reflection_log_7114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7115_neg : (49309169 / 500000000) ≤ -Real.log (200000 / 220729) ∧
    -Real.log (200000 / 220729) ≤ (98618339 / 1000000000) := by
  have h := checkLog_sound (w := (20729 / 420729)) (n := 12)
    (lo := (49309169 / 500000000)) (hi := (98618339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220729 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220729 / 200000) = 1/(200000 / 220729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7115 : Bounds (49309169 / 500000000) (98618339 / 1000000000) (Real.log (220729 / 200000)) := by
  have h := reflection_log_7115_neg
  have he : Real.log (220729 / 200000) = -Real.log (200000 / 220729) := by
    rw [show ((220729 / 200000) : ℝ) = ((200000 / 220729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7116_neg : (109418739 / 1000000000) ≤ -Real.log (179271 / 200000) ∧
    -Real.log (179271 / 200000) ≤ (5470937 / 50000000) := by
  have h := checkLog_sound (w := (20729 / 379271)) (n := 12)
    (lo := (109418739 / 1000000000)) (hi := (5470937 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179271) = 1/(179271 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7116 : Bounds (-5470937 / 50000000) (-109418739 / 1000000000) (Real.log (179271 / 200000)) := by
  have h := reflection_log_7116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7117_neg : (27001 / 2500000) ≤ -Real.log (39570308559 / 40000000000) ∧
    -Real.log (39570308559 / 40000000000) ≤ (10800401 / 1000000000) := by
  have h := checkLog_sound (w := (429691441 / 79570308559)) (n := 12)
    (lo := (27001 / 2500000)) (hi := (10800401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39570308559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39570308559) = 1/(39570308559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7117 : Bounds (-10800401 / 1000000000) (-27001 / 2500000) (Real.log (39570308559 / 40000000000)) := by
  have h := reflection_log_7117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7118_neg : (5352011 / 500000000) ≤ -Real.log (3864660399 / 3906250000) ∧
    -Real.log (3864660399 / 3906250000) ≤ (10704023 / 1000000000) := by
  have h := checkLog_sound (w := (41589601 / 7770910399)) (n := 12)
    (lo := (5352011 / 500000000)) (hi := (10704023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3864660399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3864660399) = 1/(3864660399 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7118 : Bounds (-10704023 / 1000000000) (-5352011 / 500000000) (Real.log (3864660399 / 3906250000)) := by
  have h := reflection_log_7118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7119_neg : (20710511 / 100000000) ≤ -Real.log (100000000000 / 123011186241) ∧
    -Real.log (100000000000 / 123011186241) ≤ (207105111 / 1000000000) := by
  have h := checkLog_sound (w := (23011186241 / 223011186241)) (n := 12)
    (lo := (20710511 / 100000000)) (hi := (207105111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123011186241 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123011186241 / 100000000000) = 1/(100000000000 / 123011186241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7119 : Bounds (20710511 / 100000000) (207105111 / 1000000000) (Real.log (123011186241 / 100000000000)) := by
  have h := reflection_log_7119_neg
  have he : Real.log (123011186241 / 100000000000) = -Real.log (100000000000 / 123011186241) := by
    rw [show ((123011186241 / 100000000000) : ℝ) = ((100000000000 / 123011186241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7120_neg : (208037077 / 1000000000) ≤ -Real.log (500000000000 / 615629410223) ∧
    -Real.log (500000000000 / 615629410223) ≤ (104018539 / 500000000) := by
  have h := checkLog_sound (w := (115629410223 / 1115629410223)) (n := 12)
    (lo := (208037077 / 1000000000)) (hi := (104018539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615629410223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615629410223 / 500000000000) = 1/(500000000000 / 615629410223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7120 : Bounds (208037077 / 1000000000) (104018539 / 500000000) (Real.log (615629410223 / 500000000000)) := by
  have h := reflection_log_7120_neg
  have he : Real.log (615629410223 / 500000000000) = -Real.log (500000000000 / 615629410223) := by
    rw [show ((615629410223 / 500000000000) : ℝ) = ((500000000000 / 615629410223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7121_neg : (415892731 / 1000000000) ≤ -Real.log (25000000000 / 37893081761) ∧
    -Real.log (25000000000 / 37893081761) ≤ (103973183 / 250000000) := by
  have h := checkLog_sound (w := (12893081761 / 62893081761)) (n := 12)
    (lo := (415892731 / 1000000000)) (hi := (103973183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37893081761 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37893081761 / 25000000000) = 1/(25000000000 / 37893081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7121 : Bounds (415892731 / 1000000000) (103973183 / 250000000) (Real.log (37893081761 / 25000000000)) := by
  have h := reflection_log_7121_neg
  have he : Real.log (37893081761 / 25000000000) = -Real.log (25000000000 / 37893081761) := by
    rw [show ((37893081761 / 25000000000) : ℝ) = ((25000000000 / 37893081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7122_neg : (416936711 / 1000000000) ≤ -Real.log (500000000000 / 758653241033) ∧
    -Real.log (500000000000 / 758653241033) ≤ (52117089 / 125000000) := by
  have h := checkLog_sound (w := (258653241033 / 1258653241033)) (n := 12)
    (lo := (416936711 / 1000000000)) (hi := (52117089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758653241033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758653241033 / 500000000000) = 1/(500000000000 / 758653241033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7122 : Bounds (416936711 / 1000000000) (52117089 / 125000000) (Real.log (758653241033 / 500000000000)) := by
  have h := reflection_log_7122_neg
  have he : Real.log (758653241033 / 500000000000) = -Real.log (500000000000 / 758653241033) := by
    rw [show ((758653241033 / 500000000000) : ℝ) = ((500000000000 / 758653241033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7123_neg : (93654549 / 500000000) ≤ -Real.log (500 / 603) ∧
    -Real.log (500 / 603) ≤ (187309099 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1103)) (n := 12)
    (lo := (93654549 / 500000000)) (hi := (187309099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603 / 500) = 1/(500 / 603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7123 : Bounds (93654549 / 500000000) (187309099 / 1000000000) (Real.log (603 / 500)) := by
  have h := reflection_log_7123_neg
  have he : Real.log (603 / 500) = -Real.log (500 / 603) := by
    rw [show ((603 / 500) : ℝ) = ((500 / 603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7124_neg : (230671817 / 1000000000) ≤ -Real.log (397 / 500) ∧
    -Real.log (397 / 500) ≤ (115335909 / 500000000) := by
  have h := checkLog_sound (w := (103 / 897)) (n := 12)
    (lo := (230671817 / 1000000000)) (hi := (115335909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 397) = 1/(397 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7124 : Bounds (-115335909 / 500000000) (-230671817 / 1000000000) (Real.log (397 / 500)) := by
  have h := reflection_log_7124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7125_neg : (102989 / 500000000) ≤ -Real.log (500000 / 500103) ∧
    -Real.log (500000 / 500103) ≤ (205979 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1000103)) (n := 12)
    (lo := (102989 / 500000000)) (hi := (205979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500103 / 500000) = 1/(500000 / 500103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7125 : Bounds (102989 / 500000000) (205979 / 1000000000) (Real.log (500103 / 500000)) := by
  have h := reflection_log_7125_neg
  have he : Real.log (500103 / 500000) = -Real.log (500000 / 500103) := by
    rw [show ((500103 / 500000) : ℝ) = ((500000 / 500103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7126_neg : (206021 / 1000000000) ≤ -Real.log (499897 / 500000) ∧
    -Real.log (499897 / 500000) ≤ (103011 / 500000000) := by
  have h := checkLog_sound (w := (103 / 999897)) (n := 12)
    (lo := (206021 / 1000000000)) (hi := (103011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499897) = 1/(499897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7126 : Bounds (-103011 / 500000000) (-206021 / 1000000000) (Real.log (499897 / 500000)) := by
  have h := reflection_log_7126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7127_neg : (24608143 / 250000000) ≤ -Real.log (12500 / 13793) ∧
    -Real.log (12500 / 13793) ≤ (98432573 / 1000000000) := by
  have h := checkLog_sound (w := (1293 / 26293)) (n := 12)
    (lo := (24608143 / 250000000)) (hi := (98432573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13793 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13793 / 12500) = 1/(12500 / 13793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7127 : Bounds (24608143 / 250000000) (98432573 / 1000000000) (Real.log (13793 / 12500)) := by
  have h := reflection_log_7127_neg
  have he : Real.log (13793 / 12500) = -Real.log (12500 / 13793) := by
    rw [show ((13793 / 12500) : ℝ) = ((12500 / 13793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7128_neg : (109190061 / 1000000000) ≤ -Real.log (11207 / 12500) ∧
    -Real.log (11207 / 12500) ≤ (54595031 / 500000000) := by
  have h := checkLog_sound (w := (1293 / 23707)) (n := 12)
    (lo := (109190061 / 1000000000)) (hi := (54595031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11207) = 1/(11207 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7128 : Bounds (-54595031 / 500000000) (-109190061 / 1000000000) (Real.log (11207 / 12500)) := by
  have h := reflection_log_7128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7129_neg : (98850269 / 1000000000) ≤ -Real.log (1000000 / 1103901) ∧
    -Real.log (1000000 / 1103901) ≤ (9885027 / 100000000) := by
  have h := checkLog_sound (w := (103901 / 2103901)) (n := 12)
    (lo := (98850269 / 1000000000)) (hi := (9885027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103901 / 1000000) = 1/(1000000 / 1103901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7129 : Bounds (98850269 / 1000000000) (9885027 / 100000000) (Real.log (1103901 / 1000000)) := by
  have h := reflection_log_7129_neg
  have he : Real.log (1103901 / 1000000) = -Real.log (1000000 / 1103901) := by
    rw [show ((1103901 / 1000000) : ℝ) = ((1000000 / 1103901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7130_neg : (109704381 / 1000000000) ≤ -Real.log (896099 / 1000000) ∧
    -Real.log (896099 / 1000000) ≤ (54852191 / 500000000) := by
  have h := checkLog_sound (w := (103901 / 1896099)) (n := 12)
    (lo := (109704381 / 1000000000)) (hi := (54852191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896099) = 1/(896099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7130 : Bounds (-54852191 / 500000000) (-109704381 / 1000000000) (Real.log (896099 / 1000000)) := by
  have h := reflection_log_7130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7131_neg : (10854111 / 1000000000) ≤ -Real.log (989204582199 / 1000000000000) ∧
    -Real.log (989204582199 / 1000000000000) ≤ (339191 / 31250000) := by
  have h := checkLog_sound (w := (10795417801 / 1989204582199)) (n := 12)
    (lo := (10854111 / 1000000000)) (hi := (339191 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989204582199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989204582199) = 1/(989204582199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7131 : Bounds (-339191 / 31250000) (-10854111 / 1000000000) (Real.log (989204582199 / 1000000000000)) := by
  have h := reflection_log_7131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7132_neg : (672343 / 62500000) ≤ -Real.log (154578151 / 156250000) ∧
    -Real.log (154578151 / 156250000) ≤ (10757489 / 1000000000) := by
  have h := checkLog_sound (w := (1671849 / 310828151)) (n := 12)
    (lo := (672343 / 62500000)) (hi := (10757489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 154578151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 154578151) = 1/(154578151 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7132 : Bounds (-10757489 / 1000000000) (-672343 / 62500000) (Real.log (154578151 / 156250000)) := by
  have h := reflection_log_7132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7133_neg : (103811317 / 500000000) ≤ -Real.log (500000000000 / 615374319621) ∧
    -Real.log (500000000000 / 615374319621) ≤ (41524527 / 200000000) := by
  have h := checkLog_sound (w := (115374319621 / 1115374319621)) (n := 12)
    (lo := (103811317 / 500000000)) (hi := (41524527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615374319621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615374319621 / 500000000000) = 1/(500000000000 / 615374319621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7133 : Bounds (103811317 / 500000000) (41524527 / 200000000) (Real.log (615374319621 / 500000000000)) := by
  have h := reflection_log_7133_neg
  have he : Real.log (615374319621 / 500000000000) = -Real.log (500000000000 / 615374319621) := by
    rw [show ((615374319621 / 500000000000) : ℝ) = ((500000000000 / 615374319621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7134_neg : (4171093 / 20000000) ≤ -Real.log (125000000000 / 153987031567) ∧
    -Real.log (125000000000 / 153987031567) ≤ (208554651 / 1000000000) := by
  have h := checkLog_sound (w := (28987031567 / 278987031567)) (n := 12)
    (lo := (4171093 / 20000000)) (hi := (208554651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153987031567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153987031567 / 125000000000) = 1/(125000000000 / 153987031567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7134 : Bounds (4171093 / 20000000) (208554651 / 1000000000) (Real.log (153987031567 / 125000000000)) := by
  have h := reflection_log_7134_neg
  have he : Real.log (153987031567 / 125000000000) = -Real.log (125000000000 / 153987031567) := by
    rw [show ((153987031567 / 125000000000) : ℝ) = ((125000000000 / 153987031567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7135_neg : (416936711 / 1000000000) ≤ -Real.log (62500000000 / 94831655129) ∧
    -Real.log (62500000000 / 94831655129) ≤ (52117089 / 125000000) := by
  have h := checkLog_sound (w := (32331655129 / 157331655129)) (n := 12)
    (lo := (416936711 / 1000000000)) (hi := (52117089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94831655129 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94831655129 / 62500000000) = 1/(62500000000 / 94831655129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7135 : Bounds (416936711 / 1000000000) (52117089 / 125000000) (Real.log (94831655129 / 62500000000)) := by
  have h := reflection_log_7135_neg
  have he : Real.log (94831655129 / 62500000000) = -Real.log (62500000000 / 94831655129) := by
    rw [show ((94831655129 / 62500000000) : ℝ) = ((62500000000 / 94831655129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7136_neg : (104495229 / 250000000) ≤ -Real.log (500000000000 / 759445843829) ∧
    -Real.log (500000000000 / 759445843829) ≤ (417980917 / 1000000000) := by
  have h := checkLog_sound (w := (259445843829 / 1259445843829)) (n := 12)
    (lo := (104495229 / 250000000)) (hi := (417980917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759445843829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759445843829 / 500000000000) = 1/(500000000000 / 759445843829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7136 : Bounds (104495229 / 250000000) (417980917 / 1000000000) (Real.log (759445843829 / 500000000000)) := by
  have h := reflection_log_7136_neg
  have he : Real.log (759445843829 / 500000000000) = -Real.log (500000000000 / 759445843829) := by
    rw [show ((759445843829 / 500000000000) : ℝ) = ((500000000000 / 759445843829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7137_neg : (93861803 / 500000000) ≤ -Real.log (2000 / 2413) ∧
    -Real.log (2000 / 2413) ≤ (187723607 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 4413)) (n := 12)
    (lo := (93861803 / 500000000)) (hi := (187723607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2413 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2413 / 2000) = 1/(2000 / 2413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7137 : Bounds (93861803 / 500000000) (187723607 / 1000000000) (Real.log (2413 / 2000)) := by
  have h := reflection_log_7137_neg
  have he : Real.log (2413 / 2000) = -Real.log (2000 / 2413) := by
    rw [show ((2413 / 2000) : ℝ) = ((2000 / 2413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7138_neg : (231301739 / 1000000000) ≤ -Real.log (1587 / 2000) ∧
    -Real.log (1587 / 2000) ≤ (11565087 / 50000000) := by
  have h := checkLog_sound (w := (413 / 3587)) (n := 12)
    (lo := (231301739 / 1000000000)) (hi := (11565087 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1587) = 1/(1587 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7138 : Bounds (-11565087 / 50000000) (-231301739 / 1000000000) (Real.log (1587 / 2000)) := by
  have h := reflection_log_7138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7139_neg : (103239 / 500000000) ≤ -Real.log (2000000 / 2000413) ∧
    -Real.log (2000000 / 2000413) ≤ (206479 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 4000413)) (n := 12)
    (lo := (103239 / 500000000)) (hi := (206479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000413 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000413 / 2000000) = 1/(2000000 / 2000413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7139 : Bounds (103239 / 500000000) (206479 / 1000000000) (Real.log (2000413 / 2000000)) := by
  have h := reflection_log_7139_neg
  have he : Real.log (2000413 / 2000000) = -Real.log (2000000 / 2000413) := by
    rw [show ((2000413 / 2000000) : ℝ) = ((2000000 / 2000413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7140_neg : (206521 / 1000000000) ≤ -Real.log (1999587 / 2000000) ∧
    -Real.log (1999587 / 2000000) ≤ (103261 / 500000000) := by
  have h := checkLog_sound (w := (413 / 3999587)) (n := 12)
    (lo := (206521 / 1000000000)) (hi := (103261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999587) = 1/(1999587 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7140 : Bounds (-103261 / 500000000) (-206521 / 1000000000) (Real.log (1999587 / 2000000)) := by
  have h := reflection_log_7140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7141_neg : (98663641 / 1000000000) ≤ -Real.log (200000 / 220739) ∧
    -Real.log (200000 / 220739) ≤ (49331821 / 500000000) := by
  have h := checkLog_sound (w := (20739 / 420739)) (n := 12)
    (lo := (98663641 / 1000000000)) (hi := (49331821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220739 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220739 / 200000) = 1/(200000 / 220739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7141 : Bounds (98663641 / 1000000000) (49331821 / 500000000) (Real.log (220739 / 200000)) := by
  have h := reflection_log_7141_neg
  have he : Real.log (220739 / 200000) = -Real.log (200000 / 220739) := by
    rw [show ((220739 / 200000) : ℝ) = ((200000 / 220739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7142_neg : (54737261 / 500000000) ≤ -Real.log (179261 / 200000) ∧
    -Real.log (179261 / 200000) ≤ (109474523 / 1000000000) := by
  have h := checkLog_sound (w := (20739 / 379261)) (n := 12)
    (lo := (54737261 / 500000000)) (hi := (109474523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179261) = 1/(179261 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7142 : Bounds (-109474523 / 1000000000) (-54737261 / 500000000) (Real.log (179261 / 200000)) := by
  have h := reflection_log_7142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7143_neg : (99082147 / 1000000000) ≤ -Real.log (1000000 / 1104157) ∧
    -Real.log (1000000 / 1104157) ≤ (24770537 / 250000000) := by
  have h := checkLog_sound (w := (104157 / 2104157)) (n := 12)
    (lo := (99082147 / 1000000000)) (hi := (24770537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104157 / 1000000) = 1/(1000000 / 1104157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7143 : Bounds (99082147 / 1000000000) (24770537 / 250000000) (Real.log (1104157 / 1000000)) := by
  have h := reflection_log_7143_neg
  have he : Real.log (1104157 / 1000000) = -Real.log (1000000 / 1104157) := by
    rw [show ((1104157 / 1000000) : ℝ) = ((1000000 / 1104157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7144_neg : (13748763 / 125000000) ≤ -Real.log (895843 / 1000000) ∧
    -Real.log (895843 / 1000000) ≤ (21998021 / 200000000) := by
  have h := checkLog_sound (w := (104157 / 1895843)) (n := 12)
    (lo := (13748763 / 125000000)) (hi := (21998021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895843) = 1/(895843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7144 : Bounds (-21998021 / 200000000) (-13748763 / 125000000) (Real.log (895843 / 1000000)) := by
  have h := reflection_log_7144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7145_neg : (2726989 / 250000000) ≤ -Real.log (989151319351 / 1000000000000) ∧
    -Real.log (989151319351 / 1000000000000) ≤ (10907957 / 1000000000) := by
  have h := checkLog_sound (w := (10848680649 / 1989151319351)) (n := 12)
    (lo := (2726989 / 250000000)) (hi := (10907957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989151319351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989151319351) = 1/(989151319351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7145 : Bounds (-10907957 / 1000000000) (-2726989 / 250000000) (Real.log (989151319351 / 1000000000000)) := by
  have h := reflection_log_7145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7146_neg : (4223 / 390625) ≤ -Real.log (39569893879 / 40000000000) ∧
    -Real.log (39569893879 / 40000000000) ≤ (10810881 / 1000000000) := by
  have h := checkLog_sound (w := (430106121 / 79569893879)) (n := 12)
    (lo := (4223 / 390625)) (hi := (10810881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39569893879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39569893879) = 1/(39569893879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7146 : Bounds (-10810881 / 1000000000) (-4223 / 390625) (Real.log (39569893879 / 40000000000)) := by
  have h := reflection_log_7146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7147_neg : (208138163 / 1000000000) ≤ -Real.log (500000000000 / 615691645143) ∧
    -Real.log (500000000000 / 615691645143) ≤ (52034541 / 250000000) := by
  have h := checkLog_sound (w := (115691645143 / 1115691645143)) (n := 12)
    (lo := (208138163 / 1000000000)) (hi := (52034541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615691645143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615691645143 / 500000000000) = 1/(500000000000 / 615691645143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7147 : Bounds (208138163 / 1000000000) (52034541 / 250000000) (Real.log (615691645143 / 500000000000)) := by
  have h := reflection_log_7147_neg
  have he : Real.log (615691645143 / 500000000000) = -Real.log (500000000000 / 615691645143) := by
    rw [show ((615691645143 / 500000000000) : ℝ) = ((500000000000 / 615691645143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7148_neg : (52268063 / 250000000) ≤ -Real.log (125000000000 / 154066756117) ∧
    -Real.log (125000000000 / 154066756117) ≤ (209072253 / 1000000000) := by
  have h := checkLog_sound (w := (29066756117 / 279066756117)) (n := 12)
    (lo := (52268063 / 250000000)) (hi := (209072253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154066756117 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154066756117 / 125000000000) = 1/(125000000000 / 154066756117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7148 : Bounds (52268063 / 250000000) (209072253 / 1000000000) (Real.log (154066756117 / 125000000000)) := by
  have h := reflection_log_7148_neg
  have he : Real.log (154066756117 / 125000000000) = -Real.log (125000000000 / 154066756117) := by
    rw [show ((154066756117 / 125000000000) : ℝ) = ((125000000000 / 154066756117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7149_neg : (104495229 / 250000000) ≤ -Real.log (125000000000 / 189861460957) ∧
    -Real.log (125000000000 / 189861460957) ≤ (417980917 / 1000000000) := by
  have h := checkLog_sound (w := (64861460957 / 314861460957)) (n := 12)
    (lo := (104495229 / 250000000)) (hi := (417980917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189861460957 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189861460957 / 125000000000) = 1/(125000000000 / 189861460957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7149 : Bounds (104495229 / 250000000) (417980917 / 1000000000) (Real.log (189861460957 / 125000000000)) := by
  have h := reflection_log_7149_neg
  have he : Real.log (189861460957 / 125000000000) = -Real.log (125000000000 / 189861460957) := by
    rw [show ((189861460957 / 125000000000) : ℝ) = ((125000000000 / 189861460957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7150_neg : (83805069 / 200000000) ≤ -Real.log (100000000000 / 152047889099) ∧
    -Real.log (100000000000 / 152047889099) ≤ (209512673 / 500000000) := by
  have h := checkLog_sound (w := (52047889099 / 252047889099)) (n := 12)
    (lo := (83805069 / 200000000)) (hi := (209512673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152047889099 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152047889099 / 100000000000) = 1/(100000000000 / 152047889099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7150 : Bounds (83805069 / 200000000) (209512673 / 500000000) (Real.log (152047889099 / 100000000000)) := by
  have h := reflection_log_7150_neg
  have he : Real.log (152047889099 / 100000000000) = -Real.log (100000000000 / 152047889099) := by
    rw [show ((152047889099 / 100000000000) : ℝ) = ((100000000000 / 152047889099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7151_neg : (94068971 / 500000000) ≤ -Real.log (1000 / 1207) ∧
    -Real.log (1000 / 1207) ≤ (188137943 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 2207)) (n := 12)
    (lo := (94068971 / 500000000)) (hi := (188137943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 1000) = 1/(1000 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7151 : Bounds (94068971 / 500000000) (188137943 / 1000000000) (Real.log (1207 / 1000)) := by
  have h := reflection_log_7151_neg
  have he : Real.log (1207 / 1000) = -Real.log (1000 / 1207) := by
    rw [show ((1207 / 1000) : ℝ) = ((1000 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7152_neg : (231932057 / 1000000000) ≤ -Real.log (793 / 1000) ∧
    -Real.log (793 / 1000) ≤ (115966029 / 500000000) := by
  have h := checkLog_sound (w := (207 / 1793)) (n := 12)
    (lo := (231932057 / 1000000000)) (hi := (115966029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 793) = 1/(793 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7152 : Bounds (-115966029 / 500000000) (-231932057 / 1000000000) (Real.log (793 / 1000)) := by
  have h := reflection_log_7152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7153_neg : (103489 / 500000000) ≤ -Real.log (1000000 / 1000207) ∧
    -Real.log (1000000 / 1000207) ≤ (206979 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 2000207)) (n := 12)
    (lo := (103489 / 500000000)) (hi := (206979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000207 / 1000000) = 1/(1000000 / 1000207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7153 : Bounds (103489 / 500000000) (206979 / 1000000000) (Real.log (1000207 / 1000000)) := by
  have h := reflection_log_7153_neg
  have he : Real.log (1000207 / 1000000) = -Real.log (1000000 / 1000207) := by
    rw [show ((1000207 / 1000000) : ℝ) = ((1000000 / 1000207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7154_neg : (207021 / 1000000000) ≤ -Real.log (999793 / 1000000) ∧
    -Real.log (999793 / 1000000) ≤ (103511 / 500000000) := by
  have h := checkLog_sound (w := (207 / 1999793)) (n := 12)
    (lo := (207021 / 1000000000)) (hi := (103511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999793) = 1/(999793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7154 : Bounds (-103511 / 500000000) (-207021 / 1000000000) (Real.log (999793 / 1000000)) := by
  have h := reflection_log_7154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7155_neg : (49447781 / 500000000) ≤ -Real.log (1000000 / 1103951) ∧
    -Real.log (1000000 / 1103951) ≤ (98895563 / 1000000000) := by
  have h := checkLog_sound (w := (103951 / 2103951)) (n := 12)
    (lo := (49447781 / 500000000)) (hi := (98895563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103951 / 1000000) = 1/(1000000 / 1103951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7155 : Bounds (49447781 / 500000000) (98895563 / 1000000000) (Real.log (1103951 / 1000000)) := by
  have h := reflection_log_7155_neg
  have he : Real.log (1103951 / 1000000) = -Real.log (1000000 / 1103951) := by
    rw [show ((1103951 / 1000000) : ℝ) = ((1000000 / 1103951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7156_neg : (5488009 / 50000000) ≤ -Real.log (896049 / 1000000) ∧
    -Real.log (896049 / 1000000) ≤ (109760181 / 1000000000) := by
  have h := checkLog_sound (w := (103951 / 1896049)) (n := 12)
    (lo := (5488009 / 50000000)) (hi := (109760181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896049) = 1/(896049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7156 : Bounds (-109760181 / 1000000000) (-5488009 / 50000000) (Real.log (896049 / 1000000)) := by
  have h := reflection_log_7156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7157_neg : (24828493 / 250000000) ≤ -Real.log (1000000 / 1104413) ∧
    -Real.log (1000000 / 1104413) ≤ (99313973 / 1000000000) := by
  have h := checkLog_sound (w := (104413 / 2104413)) (n := 12)
    (lo := (24828493 / 250000000)) (hi := (99313973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104413 / 1000000) = 1/(1000000 / 1104413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7157 : Bounds (24828493 / 250000000) (99313973 / 1000000000) (Real.log (1104413 / 1000000)) := by
  have h := reflection_log_7157_neg
  have he : Real.log (1104413 / 1000000) = -Real.log (1000000 / 1104413) := by
    rw [show ((1104413 / 1000000) : ℝ) = ((1000000 / 1104413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7158_neg : (110275909 / 1000000000) ≤ -Real.log (895587 / 1000000) ∧
    -Real.log (895587 / 1000000) ≤ (11027591 / 100000000) := by
  have h := checkLog_sound (w := (104413 / 1895587)) (n := 12)
    (lo := (110275909 / 1000000000)) (hi := (11027591 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895587) = 1/(895587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7158 : Bounds (-11027591 / 100000000) (-110275909 / 1000000000) (Real.log (895587 / 1000000)) := by
  have h := reflection_log_7158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7159_neg : (10961937 / 1000000000) ≤ -Real.log (989097925431 / 1000000000000) ∧
    -Real.log (989097925431 / 1000000000000) ≤ (5480969 / 500000000) := by
  have h := checkLog_sound (w := (10902074569 / 1989097925431)) (n := 12)
    (lo := (10961937 / 1000000000)) (hi := (5480969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989097925431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989097925431) = 1/(989097925431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7159 : Bounds (-5480969 / 500000000) (-10961937 / 1000000000) (Real.log (989097925431 / 1000000000000)) := by
  have h := reflection_log_7159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7160_neg : (10864617 / 1000000000) ≤ -Real.log (989194189599 / 1000000000000) ∧
    -Real.log (989194189599 / 1000000000000) ≤ (5432309 / 500000000) := by
  have h := checkLog_sound (w := (10805810401 / 1989194189599)) (n := 12)
    (lo := (10864617 / 1000000000)) (hi := (5432309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989194189599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989194189599) = 1/(989194189599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7160 : Bounds (-5432309 / 500000000) (-10864617 / 1000000000) (Real.log (989194189599 / 1000000000000)) := by
  have h := reflection_log_7160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7161_neg : (104327871 / 500000000) ≤ -Real.log (31250000000 / 38500649797) ∧
    -Real.log (31250000000 / 38500649797) ≤ (208655743 / 1000000000) := by
  have h := checkLog_sound (w := (7250649797 / 69750649797)) (n := 12)
    (lo := (104327871 / 500000000)) (hi := (208655743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38500649797 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38500649797 / 31250000000) = 1/(31250000000 / 38500649797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7161 : Bounds (104327871 / 500000000) (208655743 / 1000000000) (Real.log (38500649797 / 31250000000)) := by
  have h := reflection_log_7161_neg
  have he : Real.log (38500649797 / 31250000000) = -Real.log (31250000000 / 38500649797) := by
    rw [show ((38500649797 / 31250000000) : ℝ) = ((31250000000 / 38500649797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7162_neg : (209589881 / 1000000000) ≤ -Real.log (25000000000 / 30829305249) ∧
    -Real.log (25000000000 / 30829305249) ≤ (104794941 / 500000000) := by
  have h := checkLog_sound (w := (5829305249 / 55829305249)) (n := 12)
    (lo := (209589881 / 1000000000)) (hi := (104794941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30829305249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30829305249 / 25000000000) = 1/(25000000000 / 30829305249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7162 : Bounds (209589881 / 1000000000) (104794941 / 500000000) (Real.log (30829305249 / 25000000000)) := by
  have h := reflection_log_7162_neg
  have he : Real.log (30829305249 / 25000000000) = -Real.log (25000000000 / 30829305249) := by
    rw [show ((30829305249 / 25000000000) : ℝ) = ((25000000000 / 30829305249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7163_neg : (83805069 / 200000000) ≤ -Real.log (250000000000 / 380119722747) ∧
    -Real.log (250000000000 / 380119722747) ≤ (209512673 / 500000000) := by
  have h := checkLog_sound (w := (130119722747 / 630119722747)) (n := 12)
    (lo := (83805069 / 200000000)) (hi := (209512673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380119722747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380119722747 / 250000000000) = 1/(250000000000 / 380119722747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7163 : Bounds (83805069 / 200000000) (209512673 / 500000000) (Real.log (380119722747 / 250000000000)) := by
  have h := reflection_log_7163_neg
  have he : Real.log (380119722747 / 250000000000) = -Real.log (250000000000 / 380119722747) := by
    rw [show ((380119722747 / 250000000000) : ℝ) = ((250000000000 / 380119722747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7164_neg : (420069999 / 1000000000) ≤ -Real.log (6250000000 / 9512925599) ∧
    -Real.log (6250000000 / 9512925599) ≤ (42007 / 100000) := by
  have h := checkLog_sound (w := (3262925599 / 15762925599)) (n := 12)
    (lo := (420069999 / 1000000000)) (hi := (42007 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9512925599 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9512925599 / 6250000000) = 1/(6250000000 / 9512925599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7164 : Bounds (420069999 / 1000000000) (42007 / 100000) (Real.log (9512925599 / 6250000000)) := by
  have h := reflection_log_7164_neg
  have he : Real.log (9512925599 / 6250000000) = -Real.log (6250000000 / 9512925599) := by
    rw [show ((9512925599 / 6250000000) : ℝ) = ((6250000000 / 9512925599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7165_neg : (94276053 / 500000000) ≤ -Real.log (400 / 483) ∧
    -Real.log (400 / 483) ≤ (188552107 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 883)) (n := 12)
    (lo := (94276053 / 500000000)) (hi := (188552107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483 / 400) = 1/(400 / 483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7165 : Bounds (94276053 / 500000000) (188552107 / 1000000000) (Real.log (483 / 400)) := by
  have h := reflection_log_7165_neg
  have he : Real.log (483 / 400) = -Real.log (400 / 483) := by
    rw [show ((483 / 400) : ℝ) = ((400 / 483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7166_neg : (232562773 / 1000000000) ≤ -Real.log (317 / 400) ∧
    -Real.log (317 / 400) ≤ (116281387 / 500000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 317) = 1/(317 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7166 : Bounds (-116281387 / 500000000) (-232562773 / 1000000000) (Real.log (317 / 400)) := by
  have h := reflection_log_7166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7167_neg : (103739 / 500000000) ≤ -Real.log (400000 / 400083) ∧
    -Real.log (400000 / 400083) ≤ (207479 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 800083)) (n := 12)
    (lo := (103739 / 500000000)) (hi := (207479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400083 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400083 / 400000) = 1/(400000 / 400083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7167 : Bounds (103739 / 500000000) (207479 / 1000000000) (Real.log (400083 / 400000)) := by
  have h := reflection_log_7167_neg
  have he : Real.log (400083 / 400000) = -Real.log (400000 / 400083) := by
    rw [show ((400083 / 400000) : ℝ) = ((400000 / 400083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
