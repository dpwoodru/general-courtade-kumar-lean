import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell092
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

theorem reflection_log_1_neg : (66453459 / 250000000) ≤ -Real.log (5120 / 6679) ∧
    -Real.log (5120 / 6679) ≤ (265813837 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 11799)) (n := 12)
    (lo := (66453459 / 250000000)) (hi := (265813837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6679 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6679 / 5120) = 1/(5120 / 6679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66453459 / 250000000) (265813837 / 1000000000) (Real.log (6679 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6679 / 5120) = -Real.log (5120 / 6679) := by
    rw [show ((6679 / 5120) : ℝ) = ((5120 / 6679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (181556517 / 500000000) ≤ -Real.log (3561 / 5120) ∧
    -Real.log (3561 / 5120) ≤ (72622607 / 200000000) := by
  have h := checkLog_sound (w := (1559 / 8681)) (n := 12)
    (lo := (181556517 / 500000000)) (hi := (72622607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3561) = 1/(3561 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72622607 / 200000000) (-181556517 / 500000000) (Real.log (3561 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132682283 / 500000000) ≤ -Real.log (1280 / 1669) ∧
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


theorem reflection_log_3 : Bounds (132682283 / 500000000) (265364567 / 1000000000) (Real.log (1669 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1669 / 1280) = -Real.log (1280 / 1669) := by
    rw [show ((1669 / 1280) : ℝ) = ((1280 / 1669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (362270929 / 1000000000) ≤ -Real.log (891 / 1280) ∧
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


theorem reflection_log_4 : Bounds (-36227093 / 100000000) (-362270929 / 1000000000) (Real.log (891 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9768223 / 50000000) ≤ -Real.log (500000 / 607877) ∧
    -Real.log (500000 / 607877) ≤ (195364461 / 1000000000) := by
  have h := checkLog_sound (w := (107877 / 1107877)) (n := 12)
    (lo := (9768223 / 50000000)) (hi := (195364461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607877 / 500000) = 1/(500000 / 607877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9768223 / 50000000) (195364461 / 1000000000) (Real.log (607877 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607877 / 500000) = -Real.log (500000 / 607877) := by
    rw [show ((607877 / 500000) : ℝ) = ((500000 / 607877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60758133 / 250000000) ≤ -Real.log (392123 / 500000) ∧
    -Real.log (392123 / 500000) ≤ (243032533 / 1000000000) := by
  have h := checkLog_sound (w := (107877 / 892123)) (n := 12)
    (lo := (60758133 / 250000000)) (hi := (243032533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392123) = 1/(392123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-243032533 / 1000000000) (-60758133 / 250000000) (Real.log (392123 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39141973 / 200000000) ≤ -Real.log (500000 / 608087) ∧
    -Real.log (500000 / 608087) ≤ (97854933 / 500000000) := by
  have h := checkLog_sound (w := (108087 / 1108087)) (n := 12)
    (lo := (39141973 / 200000000)) (hi := (97854933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608087 / 500000) = 1/(500000 / 608087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39141973 / 200000000) (97854933 / 500000000) (Real.log (608087 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (608087 / 500000) = -Real.log (500000 / 608087) := by
    rw [show ((608087 / 500000) : ℝ) = ((500000 / 608087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (121784111 / 500000000) ≤ -Real.log (391913 / 500000) ∧
    -Real.log (391913 / 500000) ≤ (243568223 / 1000000000) := by
  have h := checkLog_sound (w := (108087 / 891913)) (n := 12)
    (lo := (121784111 / 500000000)) (hi := (243568223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391913) = 1/(391913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-243568223 / 1000000000) (-121784111 / 500000000) (Real.log (391913 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35928747 / 250000000) ≤ -Real.log (200000 / 230911) ∧
    -Real.log (200000 / 230911) ≤ (143714989 / 1000000000) := by
  have h := checkLog_sound (w := (30911 / 430911)) (n := 12)
    (lo := (35928747 / 250000000)) (hi := (143714989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230911 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230911 / 200000) = 1/(200000 / 230911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35928747 / 250000000) (143714989 / 1000000000) (Real.log (230911 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (230911 / 200000) = -Real.log (200000 / 230911) := by
    rw [show ((230911 / 200000) : ℝ) = ((200000 / 230911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167892163 / 1000000000) ≤ -Real.log (169089 / 200000) ∧
    -Real.log (169089 / 200000) ≤ (41973041 / 250000000) := by
  have h := checkLog_sound (w := (30911 / 369089)) (n := 12)
    (lo := (167892163 / 1000000000)) (hi := (41973041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169089) = 1/(169089 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41973041 / 250000000) (-167892163 / 1000000000) (Real.log (169089 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35995647 / 250000000) ≤ -Real.log (62500 / 72179) ∧
    -Real.log (62500 / 72179) ≤ (143982589 / 1000000000) := by
  have h := checkLog_sound (w := (9679 / 134679)) (n := 12)
    (lo := (35995647 / 250000000)) (hi := (143982589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72179 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72179 / 62500) = 1/(62500 / 72179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35995647 / 250000000) (143982589 / 1000000000) (Real.log (72179 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (72179 / 62500) = -Real.log (62500 / 72179) := by
    rw [show ((72179 / 62500) : ℝ) = ((62500 / 72179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (168257717 / 1000000000) ≤ -Real.log (52821 / 62500) ∧
    -Real.log (52821 / 62500) ≤ (84128859 / 500000000) := by
  have h := checkLog_sound (w := (9679 / 115321)) (n := 12)
    (lo := (168257717 / 1000000000)) (hi := (84128859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 52821) = 1/(52821 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84128859 / 500000000) (-168257717 / 1000000000) (Real.log (52821 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (78454437 / 125000000) ≤ -Real.log (250000000000 / 468294051627) ∧
    -Real.log (250000000000 / 468294051627) ≤ (627635497 / 1000000000) := by
  have h := checkLog_sound (w := (218294051627 / 718294051627)) (n := 12)
    (lo := (78454437 / 125000000)) (hi := (627635497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468294051627 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468294051627 / 250000000000) = 1/(250000000000 / 468294051627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (78454437 / 125000000) (627635497 / 1000000000) (Real.log (468294051627 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (468294051627 / 250000000000) = -Real.log (250000000000 / 468294051627) := by
    rw [show ((468294051627 / 250000000000) : ℝ) = ((250000000000 / 468294051627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (628926871 / 1000000000) ≤ -Real.log (100000000000 / 187559674249) ∧
    -Real.log (100000000000 / 187559674249) ≤ (78615859 / 125000000) := by
  have h := checkLog_sound (w := (87559674249 / 287559674249)) (n := 12)
    (lo := (628926871 / 1000000000)) (hi := (78615859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187559674249 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187559674249 / 100000000000) = 1/(100000000000 / 187559674249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (628926871 / 1000000000) (78615859 / 125000000) (Real.log (187559674249 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (187559674249 / 100000000000) = -Real.log (100000000000 / 187559674249) := by
    rw [show ((187559674249 / 100000000000) : ℝ) = ((100000000000 / 187559674249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (6849953 / 15625000) ≤ -Real.log (500000000000 / 775110105757) ∧
    -Real.log (500000000000 / 775110105757) ≤ (438396993 / 1000000000) := by
  have h := checkLog_sound (w := (275110105757 / 1275110105757)) (n := 12)
    (lo := (6849953 / 15625000)) (hi := (438396993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775110105757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775110105757 / 500000000000) = 1/(500000000000 / 775110105757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6849953 / 15625000) (438396993 / 1000000000) (Real.log (775110105757 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (775110105757 / 500000000000) = -Real.log (500000000000 / 775110105757) := by
    rw [show ((775110105757 / 500000000000) : ℝ) = ((500000000000 / 775110105757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (439278087 / 1000000000) ≤ -Real.log (500000000000 / 775793352097) ∧
    -Real.log (500000000000 / 775793352097) ≤ (54909761 / 125000000) := by
  have h := checkLog_sound (w := (275793352097 / 1275793352097)) (n := 12)
    (lo := (439278087 / 1000000000)) (hi := (54909761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775793352097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775793352097 / 500000000000) = 1/(500000000000 / 775793352097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (439278087 / 1000000000) (54909761 / 125000000) (Real.log (775793352097 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (775793352097 / 500000000000) = -Real.log (500000000000 / 775793352097) := by
    rw [show ((775793352097 / 500000000000) : ℝ) = ((500000000000 / 775793352097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (311607151 / 1000000000) ≤ -Real.log (25000000000 / 34140452661) ∧
    -Real.log (25000000000 / 34140452661) ≤ (19475447 / 62500000) := by
  have h := checkLog_sound (w := (9140452661 / 59140452661)) (n := 12)
    (lo := (311607151 / 1000000000)) (hi := (19475447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34140452661 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34140452661 / 25000000000) = 1/(25000000000 / 34140452661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (311607151 / 1000000000) (19475447 / 62500000) (Real.log (34140452661 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (34140452661 / 25000000000) = -Real.log (25000000000 / 34140452661) := by
    rw [show ((34140452661 / 25000000000) : ℝ) = ((25000000000 / 34140452661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (62448061 / 200000000) ≤ -Real.log (7812500000 / 10675648653) ∧
    -Real.log (7812500000 / 10675648653) ≤ (156120153 / 500000000) := by
  have h := checkLog_sound (w := (2863148653 / 18488148653)) (n := 12)
    (lo := (62448061 / 200000000)) (hi := (156120153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10675648653 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10675648653 / 7812500000) = 1/(7812500000 / 10675648653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (62448061 / 200000000) (156120153 / 500000000) (Real.log (10675648653 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10675648653 / 7812500000) = -Real.log (7812500000 / 10675648653) := by
    rw [show ((10675648653 / 7812500000) : ℝ) = ((7812500000 / 10675648653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24275129 / 1000000000) ≤ -Real.log (3812566959 / 3906250000) ∧
    -Real.log (3812566959 / 3906250000) ≤ (2427513 / 100000000) := by
  have h := checkLog_sound (w := (93683041 / 7718816959)) (n := 12)
    (lo := (24275129 / 1000000000)) (hi := (2427513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3812566959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3812566959) = 1/(3812566959 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2427513 / 100000000) (-24275129 / 1000000000) (Real.log (3812566959 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12088587 / 500000000) ≤ -Real.log (39044510079 / 40000000000) ∧
    -Real.log (39044510079 / 40000000000) ≤ (967087 / 40000000) := by
  have h := checkLog_sound (w := (955489921 / 79044510079)) (n := 12)
    (lo := (12088587 / 500000000)) (hi := (967087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39044510079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39044510079) = 1/(39044510079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-967087 / 40000000) (-12088587 / 500000000) (Real.log (39044510079 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell092
