import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0148
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

theorem reflection_log_1_neg : (146130707 / 500000000) ≤ -Real.log (2560 / 3429) ∧
    -Real.log (2560 / 3429) ≤ (58452283 / 200000000) := by
  have h := checkLog_sound (w := (869 / 5989)) (n := 12)
    (lo := (146130707 / 500000000)) (hi := (58452283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3429 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3429 / 2560) = 1/(2560 / 3429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (146130707 / 500000000) (58452283 / 200000000) (Real.log (3429 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3429 / 2560) = -Real.log (2560 / 3429) := by
    rw [show ((3429 / 2560) : ℝ) = ((2560 / 3429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (103671797 / 250000000) ≤ -Real.log (1691 / 2560) ∧
    -Real.log (1691 / 2560) ≤ (414687189 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 4251)) (n := 12)
    (lo := (103671797 / 250000000)) (hi := (414687189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1691) = 1/(1691 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-414687189 / 1000000000) (-103671797 / 250000000) (Real.log (1691 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291386141 / 1000000000) ≤ -Real.log (1280 / 1713) ∧
    -Real.log (1280 / 1713) ≤ (145693071 / 500000000) := by
  have h := checkLog_sound (w := (433 / 2993)) (n := 12)
    (lo := (291386141 / 1000000000)) (hi := (145693071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1280) = 1/(1280 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291386141 / 1000000000) (145693071 / 500000000) (Real.log (1713 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1713 / 1280) = -Real.log (1280 / 1713) := by
    rw [show ((1713 / 1280) : ℝ) = ((1280 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (206457331 / 500000000) ≤ -Real.log (847 / 1280) ∧
    -Real.log (847 / 1280) ≤ (412914663 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2127)) (n := 12)
    (lo := (206457331 / 500000000)) (hi := (412914663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 847) = 1/(847 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-412914663 / 1000000000) (-206457331 / 500000000) (Real.log (847 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (518142539 / 1000000000) ≤ -Real.log (1280 / 2149) ∧
    -Real.log (1280 / 2149) ≤ (25907127 / 50000000) := by
  have h := checkLog_sound (w := (869 / 3429)) (n := 12)
    (lo := (518142539 / 1000000000)) (hi := (25907127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2149 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2149 / 1280) = 1/(1280 / 2149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (518142539 / 1000000000) (25907127 / 50000000) (Real.log (2149 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2149 / 1280) = -Real.log (1280 / 2149) := by
    rw [show ((2149 / 1280) : ℝ) = ((1280 / 2149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1136022141 / 1000000000) ≤ -Real.log (411 / 1280) ∧
    -Real.log (411 / 1280) ≤ (1136022143 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 411) = 1/(411 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1136022143 / 1000000000) (-1136022141 / 1000000000) (Real.log (411 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (258372783 / 500000000) ≤ -Real.log (640 / 1073) ∧
    -Real.log (640 / 1073) ≤ (516745567 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1713)) (n := 12)
    (lo := (258372783 / 500000000)) (hi := (516745567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1073 / 640) = 1/(640 / 1073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (258372783 / 500000000) (516745567 / 1000000000) (Real.log (1073 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1073 / 640) = -Real.log (640 / 1073) := by
    rw [show ((1073 / 640) : ℝ) = ((640 / 1073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (564374691 / 500000000) ≤ -Real.log (207 / 640) ∧
    -Real.log (207 / 640) ≤ (141093673 / 125000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 207) = 1/(207 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-141093673 / 125000000) (-564374691 / 500000000) (Real.log (207 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79738579 / 200000000) ≤ -Real.log (250000 / 372469) ∧
    -Real.log (250000 / 372469) ≤ (12459153 / 31250000) := by
  have h := checkLog_sound (w := (122469 / 622469)) (n := 12)
    (lo := (79738579 / 200000000)) (hi := (12459153 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372469 / 250000) = 1/(250000 / 372469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79738579 / 200000000) (12459153 / 31250000) (Real.log (372469 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (372469 / 250000) = -Real.log (250000 / 372469) := by
    rw [show ((372469 / 250000) : ℝ) = ((250000 / 372469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (134620289 / 200000000) ≤ -Real.log (127531 / 250000) ∧
    -Real.log (127531 / 250000) ≤ (336550723 / 500000000) := by
  have h := checkLog_sound (w := (122469 / 377531)) (n := 12)
    (lo := (134620289 / 200000000)) (hi := (336550723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127531) = 1/(127531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-336550723 / 500000000) (-134620289 / 200000000) (Real.log (127531 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39990099 / 100000000) ≤ -Real.log (1000000 / 1491677) ∧
    -Real.log (1000000 / 1491677) ≤ (399900991 / 1000000000) := by
  have h := checkLog_sound (w := (491677 / 2491677)) (n := 12)
    (lo := (39990099 / 100000000)) (hi := (399900991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491677 / 1000000) = 1/(1000000 / 1491677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39990099 / 100000000) (399900991 / 1000000000) (Real.log (1491677 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1491677 / 1000000) = -Real.log (1000000 / 1491677) := by
    rw [show ((1491677 / 1000000) : ℝ) = ((1000000 / 1491677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (338319103 / 500000000) ≤ -Real.log (508323 / 1000000) ∧
    -Real.log (508323 / 1000000) ≤ (676638207 / 1000000000) := by
  have h := checkLog_sound (w := (491677 / 1508323)) (n := 12)
    (lo := (338319103 / 500000000)) (hi := (676638207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 508323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 508323) = 1/(508323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-676638207 / 1000000000) (-338319103 / 500000000) (Real.log (508323 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315506847 / 1000000000) ≤ -Real.log (500000 / 685477) ∧
    -Real.log (500000 / 685477) ≤ (9859589 / 31250000) := by
  have h := checkLog_sound (w := (185477 / 1185477)) (n := 12)
    (lo := (315506847 / 1000000000)) (hi := (9859589 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685477 / 500000) = 1/(500000 / 685477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315506847 / 1000000000) (9859589 / 31250000) (Real.log (685477 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (685477 / 500000) = -Real.log (500000 / 685477) := by
    rw [show ((685477 / 500000) : ℝ) = ((500000 / 685477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (463550893 / 1000000000) ≤ -Real.log (314523 / 500000) ∧
    -Real.log (314523 / 500000) ≤ (231775447 / 500000000) := by
  have h := checkLog_sound (w := (185477 / 814523)) (n := 12)
    (lo := (463550893 / 1000000000)) (hi := (231775447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314523) = 1/(314523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231775447 / 500000000) (-463550893 / 1000000000) (Real.log (314523 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (79160477 / 250000000) ≤ -Real.log (1000000 / 1372511) ∧
    -Real.log (1000000 / 1372511) ≤ (316641909 / 1000000000) := by
  have h := checkLog_sound (w := (372511 / 2372511)) (n := 12)
    (lo := (79160477 / 250000000)) (hi := (316641909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372511 / 1000000) = 1/(1000000 / 1372511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (79160477 / 250000000) (316641909 / 1000000000) (Real.log (1372511 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1372511 / 1000000) = -Real.log (1000000 / 1372511) := by
    rw [show ((1372511 / 1000000) : ℝ) = ((1000000 / 1372511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (233014569 / 500000000) ≤ -Real.log (627489 / 1000000) ∧
    -Real.log (627489 / 1000000) ≤ (466029139 / 1000000000) := by
  have h := checkLog_sound (w := (372511 / 1627489)) (n := 12)
    (lo := (233014569 / 500000000)) (hi := (466029139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627489) = 1/(627489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-466029139 / 1000000000) (-233014569 / 500000000) (Real.log (627489 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (53589717 / 50000000) ≤ -Real.log (100000000000 / 292061537979) ∧
    -Real.log (100000000000 / 292061537979) ≤ (535897171 / 500000000) := by
  have h := checkLog_sound (w := (92061537979 / 492061537979)) (n := 12)
    (lo := (9466179 / 25000000)) (hi := (378647161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292061537979 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292061537979 / 200000000000) = 1/(100000000000 / 292061537979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (53589717 / 50000000) (535897171 / 500000000) (Real.log (292061537979 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (292061537979 / 100000000000) = -Real.log (100000000000 / 292061537979) := by
    rw [show ((292061537979 / 100000000000) : ℝ) = ((100000000000 / 292061537979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269134799 / 250000000) ≤ -Real.log (250000000000 / 733626552409) ∧
    -Real.log (250000000000 / 733626552409) ≤ (538269599 / 500000000) := by
  have h := checkLog_sound (w := (233626552409 / 1233626552409)) (n := 12)
    (lo := (23962001 / 62500000)) (hi := (383392017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733626552409 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(733626552409 / 500000000000) = 1/(250000000000 / 733626552409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269134799 / 250000000) (538269599 / 500000000) (Real.log (733626552409 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (733626552409 / 250000000000) = -Real.log (250000000000 / 733626552409) := by
    rw [show ((733626552409 / 250000000000) : ℝ) = ((250000000000 / 733626552409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38952887 / 50000000) ≤ -Real.log (500000000000 / 1089708860719) ∧
    -Real.log (500000000000 / 1089708860719) ≤ (389528871 / 500000000) := by
  have h := checkLog_sound (w := (89708860719 / 2089708860719)) (n := 12)
    (lo := (536941 / 6250000)) (hi := (85910561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089708860719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089708860719 / 1000000000000) = 1/(500000000000 / 1089708860719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (38952887 / 50000000) (389528871 / 500000000) (Real.log (1089708860719 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1089708860719 / 500000000000) = -Real.log (500000000000 / 1089708860719) := by
    rw [show ((1089708860719 / 500000000000) : ℝ) = ((500000000000 / 1089708860719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (391335523 / 500000000) ≤ -Real.log (500000000000 / 1093653434563) ∧
    -Real.log (500000000000 / 1093653434563) ≤ (97833881 / 125000000) := by
  have h := checkLog_sound (w := (93653434563 / 2093653434563)) (n := 12)
    (lo := (44761933 / 500000000)) (hi := (89523867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093653434563 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1093653434563 / 1000000000000) = 1/(500000000000 / 1093653434563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (391335523 / 500000000) (97833881 / 125000000) (Real.log (1093653434563 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1093653434563 / 500000000000) = -Real.log (500000000000 / 1093653434563) := by
    rw [show ((1093653434563 / 500000000000) : ℝ) = ((500000000000 / 1093653434563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0148
