import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0179
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

theorem reflection_log_1_neg : (137526921 / 500000000) ≤ -Real.log (5120 / 6741) ∧
    -Real.log (5120 / 6741) ≤ (275053843 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 11861)) (n := 12)
    (lo := (137526921 / 500000000)) (hi := (275053843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6741 / 5120) = 1/(5120 / 6741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137526921 / 500000000) (275053843 / 1000000000) (Real.log (6741 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6741 / 5120) = -Real.log (5120 / 6741) := by
    rw [show ((6741 / 5120) : ℝ) = ((5120 / 6741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15227089 / 40000000) ≤ -Real.log (3499 / 5120) ∧
    -Real.log (3499 / 5120) ≤ (190338613 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 8619)) (n := 12)
    (lo := (15227089 / 40000000)) (hi := (190338613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3499) = 1/(3499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190338613 / 500000000) (-15227089 / 40000000) (Real.log (3499 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54921741 / 200000000) ≤ -Real.log (2560 / 3369) ∧
    -Real.log (2560 / 3369) ≤ (137304353 / 500000000) := by
  have h := checkLog_sound (w := (809 / 5929)) (n := 12)
    (lo := (54921741 / 200000000)) (hi := (137304353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3369 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3369 / 2560) = 1/(2560 / 3369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (54921741 / 200000000) (137304353 / 500000000) (Real.log (3369 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3369 / 2560) = -Real.log (2560 / 3369) := by
    rw [show ((3369 / 2560) : ℝ) = ((2560 / 3369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75964041 / 200000000) ≤ -Real.log (1751 / 2560) ∧
    -Real.log (1751 / 2560) ≤ (189910103 / 500000000) := by
  have h := checkLog_sound (w := (809 / 4311)) (n := 12)
    (lo := (75964041 / 200000000)) (hi := (189910103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1751) = 1/(1751 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-189910103 / 500000000) (-75964041 / 200000000) (Real.log (1751 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (490543193 / 1000000000) ≤ -Real.log (2560 / 4181) ∧
    -Real.log (2560 / 4181) ≤ (245271597 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 6741)) (n := 12)
    (lo := (490543193 / 1000000000)) (hi := (245271597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4181 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4181 / 2560) = 1/(2560 / 4181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (490543193 / 1000000000) (245271597 / 500000000) (Real.log (4181 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4181 / 2560) = -Real.log (2560 / 4181) := by
    rw [show ((4181 / 2560) : ℝ) = ((2560 / 4181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1002947057 / 1000000000) ≤ -Real.log (939 / 2560) ∧
    -Real.log (939 / 2560) ≤ (1002947059 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 939) = 1/(939 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1002947059 / 1000000000) (-1002947057 / 1000000000) (Real.log (939 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122456351 / 250000000) ≤ -Real.log (1280 / 2089) ∧
    -Real.log (1280 / 2089) ≤ (97965081 / 200000000) := by
  have h := checkLog_sound (w := (809 / 3369)) (n := 12)
    (lo := (122456351 / 250000000)) (hi := (97965081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2089 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2089 / 1280) = 1/(1280 / 2089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122456351 / 250000000) (97965081 / 200000000) (Real.log (2089 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2089 / 1280) = -Real.log (1280 / 2089) := by
    rw [show ((2089 / 1280) : ℝ) = ((1280 / 2089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (499878631 / 500000000) ≤ -Real.log (471 / 1280) ∧
    -Real.log (471 / 1280) ≤ (62484829 / 62500000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 471) = 1/(471 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62484829 / 62500000) (-499878631 / 500000000) (Real.log (471 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (375655861 / 1000000000) ≤ -Real.log (500000 / 727973) ∧
    -Real.log (500000 / 727973) ≤ (187827931 / 500000000) := by
  have h := checkLog_sound (w := (227973 / 1227973)) (n := 12)
    (lo := (375655861 / 1000000000)) (hi := (187827931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727973 / 500000) = 1/(500000 / 727973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (375655861 / 1000000000) (187827931 / 500000000) (Real.log (727973 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (727973 / 500000) = -Real.log (500000 / 727973) := by
    rw [show ((727973 / 500000) : ℝ) = ((500000 / 727973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (152176693 / 250000000) ≤ -Real.log (272027 / 500000) ∧
    -Real.log (272027 / 500000) ≤ (608706773 / 1000000000) := by
  have h := checkLog_sound (w := (227973 / 772027)) (n := 12)
    (lo := (152176693 / 250000000)) (hi := (608706773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 272027) = 1/(272027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-608706773 / 1000000000) (-152176693 / 250000000) (Real.log (272027 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (376265587 / 1000000000) ≤ -Real.log (500000 / 728417) ∧
    -Real.log (500000 / 728417) ≤ (94066397 / 250000000) := by
  have h := checkLog_sound (w := (228417 / 1228417)) (n := 12)
    (lo := (376265587 / 1000000000)) (hi := (94066397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728417 / 500000) = 1/(500000 / 728417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (376265587 / 1000000000) (94066397 / 250000000) (Real.log (728417 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (728417 / 500000) = -Real.log (500000 / 728417) := by
    rw [show ((728417 / 500000) : ℝ) = ((500000 / 728417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (76292537 / 125000000) ≤ -Real.log (271583 / 500000) ∧
    -Real.log (271583 / 500000) ≤ (610340297 / 1000000000) := by
  have h := checkLog_sound (w := (228417 / 771583)) (n := 12)
    (lo := (76292537 / 125000000)) (hi := (610340297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 271583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 271583) = 1/(271583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-610340297 / 1000000000) (-76292537 / 125000000) (Real.log (271583 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (294187863 / 1000000000) ≤ -Real.log (250000 / 335509) ∧
    -Real.log (250000 / 335509) ≤ (36773483 / 125000000) := by
  have h := checkLog_sound (w := (85509 / 585509)) (n := 12)
    (lo := (294187863 / 1000000000)) (hi := (36773483 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335509 / 250000) = 1/(250000 / 335509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (294187863 / 1000000000) (36773483 / 125000000) (Real.log (335509 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (335509 / 250000) = -Real.log (250000 / 335509) := by
    rw [show ((335509 / 250000) : ℝ) = ((250000 / 335509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20930253 / 50000000) ≤ -Real.log (164491 / 250000) ∧
    -Real.log (164491 / 250000) ≤ (418605061 / 1000000000) := by
  have h := checkLog_sound (w := (85509 / 414491)) (n := 12)
    (lo := (20930253 / 50000000)) (hi := (418605061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164491) = 1/(164491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-418605061 / 1000000000) (-20930253 / 50000000) (Real.log (164491 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11789773 / 40000000) ≤ -Real.log (1000000 / 1342783) ∧
    -Real.log (1000000 / 1342783) ≤ (147372163 / 500000000) := by
  have h := checkLog_sound (w := (342783 / 2342783)) (n := 12)
    (lo := (11789773 / 40000000)) (hi := (147372163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1342783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1342783 / 1000000) = 1/(1000000 / 1342783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11789773 / 40000000) (147372163 / 500000000) (Real.log (1342783 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1342783 / 1000000) = -Real.log (1000000 / 1342783) := by
    rw [show ((1342783 / 1000000) : ℝ) = ((1000000 / 1342783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16789641 / 40000000) ≤ -Real.log (657217 / 1000000) ∧
    -Real.log (657217 / 1000000) ≤ (209870513 / 500000000) := by
  have h := checkLog_sound (w := (342783 / 1657217)) (n := 12)
    (lo := (16789641 / 40000000)) (hi := (209870513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 657217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 657217) = 1/(657217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-209870513 / 500000000) (-16789641 / 40000000) (Real.log (657217 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (123045329 / 125000000) ≤ -Real.log (500000000000 / 1338052840343) ∧
    -Real.log (500000000000 / 1338052840343) ≤ (492181317 / 500000000) := by
  have h := checkLog_sound (w := (338052840343 / 2338052840343)) (n := 12)
    (lo := (72803863 / 250000000)) (hi := (291215453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338052840343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1338052840343 / 1000000000000) = 1/(500000000000 / 1338052840343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (123045329 / 125000000) (492181317 / 500000000) (Real.log (1338052840343 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1338052840343 / 500000000000) = -Real.log (500000000000 / 1338052840343) := by
    rw [show ((1338052840343 / 500000000000) : ℝ) = ((500000000000 / 1338052840343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (246651471 / 250000000) ≤ -Real.log (500000000000 / 1341057798169) ∧
    -Real.log (500000000000 / 1341057798169) ≤ (493302943 / 500000000) := by
  have h := checkLog_sound (w := (341057798169 / 2341057798169)) (n := 12)
    (lo := (18341169 / 62500000)) (hi := (58691741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341057798169 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1341057798169 / 1000000000000) = 1/(500000000000 / 1341057798169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (246651471 / 250000000) (493302943 / 500000000) (Real.log (1341057798169 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1341057798169 / 500000000000) = -Real.log (500000000000 / 1341057798169) := by
    rw [show ((1341057798169 / 500000000000) : ℝ) = ((500000000000 / 1341057798169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (712792923 / 1000000000) ≤ -Real.log (100000000000 / 203967998249) ∧
    -Real.log (100000000000 / 203967998249) ≤ (28511717 / 40000000) := by
  have h := checkLog_sound (w := (3967998249 / 403967998249)) (n := 12)
    (lo := (19645743 / 1000000000)) (hi := (1227859 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203967998249 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(203967998249 / 200000000000) = 1/(100000000000 / 203967998249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (712792923 / 1000000000) (28511717 / 40000000) (Real.log (203967998249 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (203967998249 / 100000000000) = -Real.log (100000000000 / 203967998249) := by
    rw [show ((203967998249 / 100000000000) : ℝ) = ((100000000000 / 203967998249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (714485351 / 1000000000) ≤ -Real.log (500000000000 / 1021567457933) ∧
    -Real.log (500000000000 / 1021567457933) ≤ (714485353 / 1000000000) := by
  have h := checkLog_sound (w := (21567457933 / 2021567457933)) (n := 12)
    (lo := (21338171 / 1000000000)) (hi := (5334543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021567457933 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021567457933 / 1000000000000) = 1/(500000000000 / 1021567457933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (714485351 / 1000000000) (714485353 / 1000000000) (Real.log (1021567457933 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1021567457933 / 500000000000) = -Real.log (500000000000 / 1021567457933) := by
    rw [show ((1021567457933 / 500000000000) : ℝ) = ((500000000000 / 1021567457933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0179
