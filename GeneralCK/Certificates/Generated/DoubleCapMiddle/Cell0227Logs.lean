import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0227
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

theorem reflection_log_1_neg : (253460561 / 1000000000) ≤ -Real.log (5120 / 6597) ∧
    -Real.log (5120 / 6597) ≤ (126730281 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 11717)) (n := 12)
    (lo := (253460561 / 1000000000)) (hi := (126730281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6597 / 5120) = 1/(5120 / 6597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253460561 / 1000000000) (126730281 / 500000000) (Real.log (6597 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6597 / 5120) = -Real.log (5120 / 6597) := by
    rw [show ((6597 / 5120) : ℝ) = ((5120 / 6597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (340346921 / 1000000000) ≤ -Real.log (3643 / 5120) ∧
    -Real.log (3643 / 5120) ≤ (170173461 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 8763)) (n := 12)
    (lo := (340346921 / 1000000000)) (hi := (170173461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3643) = 1/(3643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170173461 / 500000000) (-340346921 / 1000000000) (Real.log (3643 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50601141 / 200000000) ≤ -Real.log (2560 / 3297) ∧
    -Real.log (2560 / 3297) ≤ (126502853 / 500000000) := by
  have h := checkLog_sound (w := (737 / 5857)) (n := 12)
    (lo := (50601141 / 200000000)) (hi := (126502853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3297 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3297 / 2560) = 1/(2560 / 3297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50601141 / 200000000) (126502853 / 500000000) (Real.log (3297 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3297 / 2560) = -Real.log (2560 / 3297) := by
    rw [show ((3297 / 2560) : ℝ) = ((2560 / 3297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (169761881 / 500000000) ≤ -Real.log (1823 / 2560) ∧
    -Real.log (1823 / 2560) ≤ (339523763 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 4383)) (n := 12)
    (lo := (169761881 / 500000000)) (hi := (339523763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1823) = 1/(1823 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-339523763 / 1000000000) (-169761881 / 500000000) (Real.log (1823 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (455494583 / 1000000000) ≤ -Real.log (2560 / 4037) ∧
    -Real.log (2560 / 4037) ≤ (56936823 / 125000000) := by
  have h := checkLog_sound (w := (1477 / 6597)) (n := 12)
    (lo := (455494583 / 1000000000)) (hi := (56936823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4037 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4037 / 2560) = 1/(2560 / 4037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (455494583 / 1000000000) (56936823 / 125000000) (Real.log (4037 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4037 / 2560) = -Real.log (2560 / 4037) := by
    rw [show ((4037 / 2560) : ℝ) = ((2560 / 4037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (860272289 / 1000000000) ≤ -Real.log (1083 / 2560) ∧
    -Real.log (1083 / 2560) ≤ (860272291 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2363)) (n := 12)
    (lo := (167125109 / 1000000000)) (hi := (16712511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1083) = 1/(1083 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-860272291 / 1000000000) (-860272289 / 1000000000) (Real.log (1083 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (454751181 / 1000000000) ≤ -Real.log (1280 / 2017) ∧
    -Real.log (1280 / 2017) ≤ (227375591 / 500000000) := by
  have h := checkLog_sound (w := (737 / 3297)) (n := 12)
    (lo := (454751181 / 1000000000)) (hi := (227375591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2017 / 1280) = 1/(1280 / 2017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (454751181 / 1000000000) (227375591 / 500000000) (Real.log (2017 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2017 / 1280) = -Real.log (1280 / 2017) := by
    rw [show ((2017 / 1280) : ℝ) = ((1280 / 2017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (214376509 / 250000000) ≤ -Real.log (543 / 1280) ∧
    -Real.log (543 / 1280) ≤ (428753019 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1183)) (n := 12)
    (lo := (20544857 / 125000000)) (hi := (164358857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 543) = 1/(543 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428753019 / 500000000) (-214376509 / 250000000) (Real.log (543 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (346218869 / 1000000000) ≤ -Real.log (62500 / 88357) ∧
    -Real.log (62500 / 88357) ≤ (34621887 / 100000000) := by
  have h := checkLog_sound (w := (25857 / 150857)) (n := 12)
    (lo := (346218869 / 1000000000)) (hi := (34621887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88357 / 62500) = 1/(62500 / 88357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (346218869 / 1000000000) (34621887 / 100000000) (Real.log (88357 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (88357 / 62500) = -Real.log (62500 / 88357) := by
    rw [show ((88357 / 62500) : ℝ) = ((62500 / 88357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (266972071 / 500000000) ≤ -Real.log (36643 / 62500) ∧
    -Real.log (36643 / 62500) ≤ (533944143 / 1000000000) := by
  have h := checkLog_sound (w := (25857 / 99143)) (n := 12)
    (lo := (266972071 / 500000000)) (hi := (533944143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 36643) = 1/(36643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-533944143 / 1000000000) (-266972071 / 500000000) (Real.log (36643 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69367523 / 200000000) ≤ -Real.log (1000000 / 1414587) ∧
    -Real.log (1000000 / 1414587) ≤ (21677351 / 62500000) := by
  have h := checkLog_sound (w := (414587 / 2414587)) (n := 12)
    (lo := (69367523 / 200000000)) (hi := (21677351 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1414587 / 1000000) = 1/(1000000 / 1414587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69367523 / 200000000) (21677351 / 62500000) (Real.log (1414587 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1414587 / 1000000) = -Real.log (1000000 / 1414587) := by
    rw [show ((1414587 / 1000000) : ℝ) = ((1000000 / 1414587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (535437697 / 1000000000) ≤ -Real.log (585413 / 1000000) ∧
    -Real.log (585413 / 1000000) ≤ (267718849 / 500000000) := by
  have h := checkLog_sound (w := (414587 / 1585413)) (n := 12)
    (lo := (535437697 / 1000000000)) (hi := (267718849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 585413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 585413) = 1/(585413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-267718849 / 500000000) (-535437697 / 1000000000) (Real.log (585413 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1338917 / 5000000) ≤ -Real.log (125000 / 163383) ∧
    -Real.log (125000 / 163383) ≤ (267783401 / 1000000000) := by
  have h := checkLog_sound (w := (38383 / 288383)) (n := 12)
    (lo := (1338917 / 5000000)) (hi := (267783401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163383 / 125000) = 1/(125000 / 163383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1338917 / 5000000) (267783401 / 1000000000) (Real.log (163383 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (163383 / 125000) = -Real.log (125000 / 163383) := by
    rw [show ((163383 / 125000) : ℝ) = ((125000 / 163383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91704409 / 250000000) ≤ -Real.log (86617 / 125000) ∧
    -Real.log (86617 / 125000) ≤ (366817637 / 1000000000) := by
  have h := checkLog_sound (w := (38383 / 211617)) (n := 12)
    (lo := (91704409 / 250000000)) (hi := (366817637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 86617) = 1/(86617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-366817637 / 1000000000) (-91704409 / 250000000) (Real.log (86617 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (268329513 / 1000000000) ≤ -Real.log (500000 / 653889) ∧
    -Real.log (500000 / 653889) ≤ (134164757 / 500000000) := by
  have h := checkLog_sound (w := (153889 / 1153889)) (n := 12)
    (lo := (268329513 / 1000000000)) (hi := (134164757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653889 / 500000) = 1/(500000 / 653889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (268329513 / 1000000000) (134164757 / 500000000) (Real.log (653889 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (653889 / 500000) = -Real.log (500000 / 653889) := by
    rw [show ((653889 / 500000) : ℝ) = ((500000 / 653889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73569713 / 200000000) ≤ -Real.log (346111 / 500000) ∧
    -Real.log (346111 / 500000) ≤ (183924283 / 500000000) := by
  have h := checkLog_sound (w := (153889 / 846111)) (n := 12)
    (lo := (73569713 / 200000000)) (hi := (183924283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 346111) = 1/(346111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-183924283 / 500000000) (-73569713 / 200000000) (Real.log (346111 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (880163011 / 1000000000) ≤ -Real.log (500000000000 / 1205646371749) ∧
    -Real.log (500000000000 / 1205646371749) ≤ (880163013 / 1000000000) := by
  have h := checkLog_sound (w := (205646371749 / 2205646371749)) (n := 12)
    (lo := (187015831 / 1000000000)) (hi := (23376979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205646371749 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1205646371749 / 1000000000000) = 1/(500000000000 / 1205646371749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (880163011 / 1000000000) (880163013 / 1000000000) (Real.log (1205646371749 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1205646371749 / 500000000000) = -Real.log (500000000000 / 1205646371749) := by
    rw [show ((1205646371749 / 500000000000) : ℝ) = ((500000000000 / 1205646371749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (882275313 / 1000000000) ≤ -Real.log (500000000000 / 1208195752401) ∧
    -Real.log (500000000000 / 1208195752401) ≤ (176455063 / 200000000) := by
  have h := checkLog_sound (w := (208195752401 / 2208195752401)) (n := 12)
    (lo := (189128133 / 1000000000)) (hi := (94564067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208195752401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1208195752401 / 1000000000000) = 1/(500000000000 / 1208195752401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (882275313 / 1000000000) (176455063 / 200000000) (Real.log (1208195752401 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1208195752401 / 500000000000) = -Real.log (500000000000 / 1208195752401) := by
    rw [show ((1208195752401 / 500000000000) : ℝ) = ((500000000000 / 1208195752401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (158650259 / 250000000) ≤ -Real.log (62500000000 / 117891839939) ∧
    -Real.log (62500000000 / 117891839939) ≤ (634601037 / 1000000000) := by
  have h := checkLog_sound (w := (55391839939 / 180391839939)) (n := 12)
    (lo := (158650259 / 250000000)) (hi := (634601037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117891839939 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117891839939 / 62500000000) = 1/(62500000000 / 117891839939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (158650259 / 250000000) (634601037 / 1000000000) (Real.log (117891839939 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (117891839939 / 62500000000) = -Real.log (62500000000 / 117891839939) := by
    rw [show ((117891839939 / 62500000000) : ℝ) = ((62500000000 / 117891839939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (636178079 / 1000000000) ≤ -Real.log (500000000000 / 944623256701) ∧
    -Real.log (500000000000 / 944623256701) ≤ (3976113 / 6250000) := by
  have h := checkLog_sound (w := (444623256701 / 1444623256701)) (n := 12)
    (lo := (636178079 / 1000000000)) (hi := (3976113 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((944623256701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(944623256701 / 500000000000) = 1/(500000000000 / 944623256701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (636178079 / 1000000000) (3976113 / 6250000) (Real.log (944623256701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (944623256701 / 500000000000) = -Real.log (500000000000 / 944623256701) := by
    rw [show ((944623256701 / 500000000000) : ℝ) = ((500000000000 / 944623256701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0227
