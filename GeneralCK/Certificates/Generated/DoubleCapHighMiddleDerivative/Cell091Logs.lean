import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell091
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (132682283 / 500000000) ≤ -Real.log (1280 / 1669) ∧
    -Real.log (1280 / 1669) ≤ (265364567 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2949)) (n := 12)
    (lo := (132682283 / 500000000)) (hi := (265364567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1669 / 1280) = 1/(1280 / 1669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132682283 / 500000000) (265364567 / 1000000000) (Real.log (1669 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1669 / 1280) = -Real.log (1280 / 1669) := by
    rw [show ((1669 / 1280) : ℝ) = ((1280 / 1669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (362270929 / 1000000000) ≤ -Real.log (891 / 1280) ∧
    -Real.log (891 / 1280) ≤ (36227093 / 100000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 891) = 1/(891 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-36227093 / 100000000) (-362270929 / 1000000000) (Real.log (891 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132457547 / 500000000) ≤ -Real.log (5120 / 6673) ∧
    -Real.log (5120 / 6673) ≤ (52983019 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 11793)) (n := 12)
    (lo := (132457547 / 500000000)) (hi := (52983019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6673 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6673 / 5120) = 1/(5120 / 6673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132457547 / 500000000) (52983019 / 200000000) (Real.log (6673 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6673 / 5120) = -Real.log (5120 / 6673) := by
    rw [show ((6673 / 5120) : ℝ) = ((5120 / 6673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (90357383 / 250000000) ≤ -Real.log (3567 / 5120) ∧
    -Real.log (3567 / 5120) ≤ (361429533 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 8687)) (n := 12)
    (lo := (90357383 / 250000000)) (hi := (361429533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3567) = 1/(3567 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-361429533 / 1000000000) (-90357383 / 250000000) (Real.log (3567 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24377367 / 125000000) ≤ -Real.log (500000 / 607667) ∧
    -Real.log (500000 / 607667) ≤ (195018937 / 1000000000) := by
  have h := checkLog_sound (w := (107667 / 1107667)) (n := 12)
    (lo := (24377367 / 125000000)) (hi := (195018937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607667 / 500000) = 1/(500000 / 607667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24377367 / 125000000) (195018937 / 1000000000) (Real.log (607667 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607667 / 500000) = -Real.log (500000 / 607667) := by
    rw [show ((607667 / 500000) : ℝ) = ((500000 / 607667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (242497129 / 1000000000) ≤ -Real.log (392333 / 500000) ∧
    -Real.log (392333 / 500000) ≤ (24249713 / 100000000) := by
  have h := checkLog_sound (w := (107667 / 892333)) (n := 12)
    (lo := (242497129 / 1000000000)) (hi := (24249713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392333) = 1/(392333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24249713 / 100000000) (-242497129 / 1000000000) (Real.log (392333 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97682641 / 500000000) ≤ -Real.log (200000 / 243151) ∧
    -Real.log (200000 / 243151) ≤ (195365283 / 1000000000) := by
  have h := checkLog_sound (w := (43151 / 443151)) (n := 12)
    (lo := (97682641 / 500000000)) (hi := (195365283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243151 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243151 / 200000) = 1/(200000 / 243151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97682641 / 500000000) (195365283 / 1000000000) (Real.log (243151 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (243151 / 200000) = -Real.log (200000 / 243151) := by
    rw [show ((243151 / 200000) : ℝ) = ((200000 / 243151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (243033807 / 1000000000) ≤ -Real.log (156849 / 200000) ∧
    -Real.log (156849 / 200000) ≤ (15189613 / 62500000) := by
  have h := checkLog_sound (w := (43151 / 356849)) (n := 12)
    (lo := (243033807 / 1000000000)) (hi := (15189613 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 156849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 156849) = 1/(156849 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15189613 / 62500000) (-243033807 / 1000000000) (Real.log (156849 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35861829 / 250000000) ≤ -Real.log (500000 / 577123) ∧
    -Real.log (500000 / 577123) ≤ (143447317 / 1000000000) := by
  have h := checkLog_sound (w := (77123 / 1077123)) (n := 12)
    (lo := (35861829 / 250000000)) (hi := (143447317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577123 / 500000) = 1/(500000 / 577123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35861829 / 250000000) (143447317 / 1000000000) (Real.log (577123 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (577123 / 500000) = -Real.log (500000 / 577123) := by
    rw [show ((577123 / 500000) : ℝ) = ((500000 / 577123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167526741 / 1000000000) ≤ -Real.log (422877 / 500000) ∧
    -Real.log (422877 / 500000) ≤ (83763371 / 500000000) := by
  have h := checkLog_sound (w := (77123 / 922877)) (n := 12)
    (lo := (167526741 / 1000000000)) (hi := (83763371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422877) = 1/(422877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83763371 / 500000000) (-167526741 / 1000000000) (Real.log (422877 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (71857927 / 500000000) ≤ -Real.log (250000 / 288639) ∧
    -Real.log (250000 / 288639) ≤ (28743171 / 200000000) := by
  have h := checkLog_sound (w := (38639 / 538639)) (n := 12)
    (lo := (71857927 / 500000000)) (hi := (28743171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288639 / 250000) = 1/(250000 / 288639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (71857927 / 500000000) (28743171 / 200000000) (Real.log (288639 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (288639 / 250000) = -Real.log (250000 / 288639) := by
    rw [show ((288639 / 250000) : ℝ) = ((250000 / 288639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33578669 / 200000000) ≤ -Real.log (211361 / 250000) ∧
    -Real.log (211361 / 250000) ≤ (83946673 / 500000000) := by
  have h := checkLog_sound (w := (38639 / 461361)) (n := 12)
    (lo := (33578669 / 200000000)) (hi := (83946673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211361) = 1/(211361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83946673 / 500000000) (-33578669 / 200000000) (Real.log (211361 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (626344627 / 1000000000) ≤ -Real.log (1562500000 / 2923062097) ∧
    -Real.log (1562500000 / 2923062097) ≤ (156586157 / 250000000) := by
  have h := checkLog_sound (w := (1360562097 / 4485562097)) (n := 12)
    (lo := (626344627 / 1000000000)) (hi := (156586157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2923062097 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2923062097 / 1562500000) = 1/(1562500000 / 2923062097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (626344627 / 1000000000) (156586157 / 250000000) (Real.log (2923062097 / 1562500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2923062097 / 1562500000) = -Real.log (1562500000 / 2923062097) := by
    rw [show ((2923062097 / 1562500000) : ℝ) = ((1562500000 / 2923062097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (78454437 / 125000000) ≤ -Real.log (100000000000 / 187317620651) ∧
    -Real.log (100000000000 / 187317620651) ≤ (627635497 / 1000000000) := by
  have h := checkLog_sound (w := (87317620651 / 287317620651)) (n := 12)
    (lo := (78454437 / 125000000)) (hi := (627635497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187317620651 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187317620651 / 100000000000) = 1/(100000000000 / 187317620651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (78454437 / 125000000) (627635497 / 1000000000) (Real.log (187317620651 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (187317620651 / 100000000000) = -Real.log (100000000000 / 187317620651) := by
    rw [show ((187317620651 / 100000000000) : ℝ) = ((100000000000 / 187317620651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (87503213 / 200000000) ≤ -Real.log (500000000000 / 774427590847) ∧
    -Real.log (500000000000 / 774427590847) ≤ (218758033 / 500000000) := by
  have h := checkLog_sound (w := (274427590847 / 1274427590847)) (n := 12)
    (lo := (87503213 / 200000000)) (hi := (218758033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774427590847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774427590847 / 500000000000) = 1/(500000000000 / 774427590847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (87503213 / 200000000) (218758033 / 500000000) (Real.log (774427590847 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (774427590847 / 500000000000) = -Real.log (500000000000 / 774427590847) := by
    rw [show ((774427590847 / 500000000000) : ℝ) = ((500000000000 / 774427590847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (43839909 / 100000000) ≤ -Real.log (250000000000 / 387555865833) ∧
    -Real.log (250000000000 / 387555865833) ≤ (438399091 / 1000000000) := by
  have h := checkLog_sound (w := (137555865833 / 637555865833)) (n := 12)
    (lo := (43839909 / 100000000)) (hi := (438399091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387555865833 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387555865833 / 250000000000) = 1/(250000000000 / 387555865833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (43839909 / 100000000) (438399091 / 1000000000) (Real.log (387555865833 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (387555865833 / 250000000000) = -Real.log (250000000000 / 387555865833) := by
    rw [show ((387555865833 / 250000000000) : ℝ) = ((250000000000 / 387555865833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (155487029 / 500000000) ≤ -Real.log (500000000000 / 682376908651) ∧
    -Real.log (500000000000 / 682376908651) ≤ (310974059 / 1000000000) := by
  have h := checkLog_sound (w := (182376908651 / 1182376908651)) (n := 12)
    (lo := (155487029 / 500000000)) (hi := (310974059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682376908651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682376908651 / 500000000000) = 1/(500000000000 / 682376908651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (155487029 / 500000000) (310974059 / 1000000000) (Real.log (682376908651 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (682376908651 / 500000000000) = -Real.log (500000000000 / 682376908651) := by
    rw [show ((682376908651 / 500000000000) : ℝ) = ((500000000000 / 682376908651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (779023 / 2500000) ≤ -Real.log (25000000000 / 34140522613) ∧
    -Real.log (25000000000 / 34140522613) ≤ (311609201 / 1000000000) := by
  have h := checkLog_sound (w := (9140522613 / 59140522613)) (n := 12)
    (lo := (779023 / 2500000)) (hi := (311609201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34140522613 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34140522613 / 25000000000) = 1/(25000000000 / 34140522613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (779023 / 2500000) (311609201 / 1000000000) (Real.log (34140522613 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34140522613 / 25000000000) = -Real.log (25000000000 / 34140522613) := by
    rw [show ((34140522613 / 25000000000) : ℝ) = ((25000000000 / 34140522613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24177491 / 1000000000) ≤ -Real.log (61007027679 / 62500000000) ∧
    -Real.log (61007027679 / 62500000000) ≤ (6044373 / 250000000) := by
  have h := checkLog_sound (w := (1492972321 / 123507027679)) (n := 12)
    (lo := (24177491 / 1000000000)) (hi := (6044373 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61007027679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61007027679) = 1/(61007027679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6044373 / 250000000) (-24177491 / 1000000000) (Real.log (61007027679 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (376241 / 15625000) ≤ -Real.log (244052042871 / 250000000000) ∧
    -Real.log (244052042871 / 250000000000) ≤ (963177 / 40000000) := by
  have h := checkLog_sound (w := (5947957129 / 494052042871)) (n := 12)
    (lo := (376241 / 15625000)) (hi := (963177 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244052042871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244052042871) = 1/(244052042871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-963177 / 40000000) (-376241 / 15625000) (Real.log (244052042871 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell091
