import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell109
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

theorem reflection_log_1_neg : (8544397 / 31250000) ≤ -Real.log (512 / 673) ∧
    -Real.log (512 / 673) ≤ (54684141 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1185)) (n := 12)
    (lo := (8544397 / 31250000)) (hi := (54684141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 512) = 1/(512 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8544397 / 31250000) (54684141 / 200000000) (Real.log (673 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (673 / 512) = -Real.log (512 / 673) := by
    rw [show ((673 / 512) : ℝ) = ((512 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (377538401 / 1000000000) ≤ -Real.log (351 / 512) ∧
    -Real.log (351 / 512) ≤ (188769201 / 500000000) := by
  have h := checkLog_sound (w := (161 / 863)) (n := 12)
    (lo := (377538401 / 1000000000)) (hi := (188769201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 351) = 1/(351 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188769201 / 500000000) (-377538401 / 1000000000) (Real.log (351 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272974839 / 1000000000) ≤ -Real.log (5120 / 6727) ∧
    -Real.log (5120 / 6727) ≤ (6824371 / 25000000) := by
  have h := checkLog_sound (w := (1607 / 11847)) (n := 12)
    (lo := (272974839 / 1000000000)) (hi := (6824371 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6727 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6727 / 5120) = 1/(5120 / 6727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272974839 / 1000000000) (6824371 / 25000000) (Real.log (6727 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6727 / 5120) = -Real.log (5120 / 6727) := by
    rw [show ((6727 / 5120) : ℝ) = ((5120 / 6727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75336813 / 200000000) ≤ -Real.log (3513 / 5120) ∧
    -Real.log (3513 / 5120) ≤ (188342033 / 500000000) := by
  have h := checkLog_sound (w := (1607 / 8633)) (n := 12)
    (lo := (75336813 / 200000000)) (hi := (188342033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3513) = 1/(3513 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-188342033 / 500000000) (-75336813 / 200000000) (Real.log (3513 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25151807 / 125000000) ≤ -Real.log (1000000 / 1222887) ∧
    -Real.log (1000000 / 1222887) ≤ (201214457 / 1000000000) := by
  have h := checkLog_sound (w := (222887 / 2222887)) (n := 12)
    (lo := (25151807 / 125000000)) (hi := (201214457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222887 / 1000000) = 1/(1000000 / 1222887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25151807 / 125000000) (201214457 / 1000000000) (Real.log (1222887 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1222887 / 1000000) = -Real.log (1000000 / 1222887) := by
    rw [show ((1222887 / 1000000) : ℝ) = ((1000000 / 1222887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63042377 / 250000000) ≤ -Real.log (777113 / 1000000) ∧
    -Real.log (777113 / 1000000) ≤ (252169509 / 1000000000) := by
  have h := checkLog_sound (w := (222887 / 1777113)) (n := 12)
    (lo := (63042377 / 250000000)) (hi := (252169509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777113) = 1/(777113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-252169509 / 1000000000) (-63042377 / 250000000) (Real.log (777113 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25194833 / 125000000) ≤ -Real.log (250000 / 305827) ∧
    -Real.log (250000 / 305827) ≤ (40311733 / 200000000) := by
  have h := checkLog_sound (w := (55827 / 555827)) (n := 12)
    (lo := (25194833 / 125000000)) (hi := (40311733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305827 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305827 / 250000) = 1/(250000 / 305827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25194833 / 125000000) (40311733 / 200000000) (Real.log (305827 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (305827 / 250000) = -Real.log (250000 / 305827) := by
    rw [show ((305827 / 250000) : ℝ) = ((250000 / 305827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (252711403 / 1000000000) ≤ -Real.log (194173 / 250000) ∧
    -Real.log (194173 / 250000) ≤ (63177851 / 250000000) := by
  have h := checkLog_sound (w := (55827 / 444173)) (n := 12)
    (lo := (252711403 / 1000000000)) (hi := (63177851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194173) = 1/(194173 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63177851 / 250000000) (-252711403 / 1000000000) (Real.log (194173 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148251887 / 1000000000) ≤ -Real.log (200000 / 231961) ∧
    -Real.log (200000 / 231961) ≤ (9265743 / 62500000) := by
  have h := checkLog_sound (w := (31961 / 431961)) (n := 12)
    (lo := (148251887 / 1000000000)) (hi := (9265743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231961 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231961 / 200000) = 1/(200000 / 231961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148251887 / 1000000000) (9265743 / 62500000) (Real.log (231961 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (231961 / 200000) = -Real.log (200000 / 231961) := by
    rw [show ((231961 / 200000) : ℝ) = ((200000 / 231961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (174121271 / 1000000000) ≤ -Real.log (168039 / 200000) ∧
    -Real.log (168039 / 200000) ≤ (21765159 / 125000000) := by
  have h := checkLog_sound (w := (31961 / 368039)) (n := 12)
    (lo := (174121271 / 1000000000)) (hi := (21765159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168039) = 1/(168039 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21765159 / 125000000) (-174121271 / 1000000000) (Real.log (168039 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74259569 / 500000000) ≤ -Real.log (200000 / 232023) ∧
    -Real.log (200000 / 232023) ≤ (148519139 / 1000000000) := by
  have h := checkLog_sound (w := (32023 / 432023)) (n := 12)
    (lo := (74259569 / 500000000)) (hi := (148519139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232023 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232023 / 200000) = 1/(200000 / 232023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74259569 / 500000000) (148519139 / 1000000000) (Real.log (232023 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (232023 / 200000) = -Real.log (200000 / 232023) := by
    rw [show ((232023 / 200000) : ℝ) = ((200000 / 232023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174490301 / 1000000000) ≤ -Real.log (167977 / 200000) ∧
    -Real.log (167977 / 200000) ≤ (87245151 / 500000000) := by
  have h := checkLog_sound (w := (32023 / 367977)) (n := 12)
    (lo := (174490301 / 1000000000)) (hi := (87245151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 167977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 167977) = 1/(167977 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87245151 / 500000000) (-174490301 / 1000000000) (Real.log (167977 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129931781 / 200000000) ≤ -Real.log (125000000000 / 239360945061) ∧
    -Real.log (125000000000 / 239360945061) ≤ (324829453 / 500000000) := by
  have h := checkLog_sound (w := (114360945061 / 364360945061)) (n := 12)
    (lo := (129931781 / 200000000)) (hi := (324829453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239360945061 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239360945061 / 125000000000) = 1/(125000000000 / 239360945061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129931781 / 200000000) (324829453 / 500000000) (Real.log (239360945061 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (239360945061 / 125000000000) = -Real.log (125000000000 / 239360945061) := by
    rw [show ((239360945061 / 125000000000) : ℝ) = ((125000000000 / 239360945061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (325479553 / 500000000) ≤ -Real.log (50000000000 / 95868945869) ∧
    -Real.log (50000000000 / 95868945869) ≤ (650959107 / 1000000000) := by
  have h := checkLog_sound (w := (45868945869 / 145868945869)) (n := 12)
    (lo := (325479553 / 500000000)) (hi := (650959107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95868945869 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95868945869 / 50000000000) = 1/(50000000000 / 95868945869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (325479553 / 500000000) (650959107 / 1000000000) (Real.log (95868945869 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (95868945869 / 50000000000) = -Real.log (50000000000 / 95868945869) := by
    rw [show ((95868945869 / 50000000000) : ℝ) = ((50000000000 / 95868945869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (113345991 / 250000000) ≤ -Real.log (250000000000 / 393407072073) ∧
    -Real.log (250000000000 / 393407072073) ≤ (90676793 / 200000000) := by
  have h := checkLog_sound (w := (143407072073 / 643407072073)) (n := 12)
    (lo := (113345991 / 250000000)) (hi := (90676793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393407072073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393407072073 / 250000000000) = 1/(250000000000 / 393407072073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (113345991 / 250000000) (90676793 / 200000000) (Real.log (393407072073 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393407072073 / 250000000000) = -Real.log (250000000000 / 393407072073) := by
    rw [show ((393407072073 / 250000000000) : ℝ) = ((250000000000 / 393407072073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113567517 / 250000000) ≤ -Real.log (500000000000 / 787511651981) ∧
    -Real.log (500000000000 / 787511651981) ≤ (454270069 / 1000000000) := by
  have h := checkLog_sound (w := (287511651981 / 1287511651981)) (n := 12)
    (lo := (113567517 / 250000000)) (hi := (454270069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787511651981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787511651981 / 500000000000) = 1/(500000000000 / 787511651981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (113567517 / 250000000) (454270069 / 1000000000) (Real.log (787511651981 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (787511651981 / 500000000000) = -Real.log (500000000000 / 787511651981) := by
    rw [show ((787511651981 / 500000000000) : ℝ) = ((500000000000 / 787511651981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (161186579 / 500000000) ≤ -Real.log (62500000000 / 86274986759) ∧
    -Real.log (62500000000 / 86274986759) ≤ (322373159 / 1000000000) := by
  have h := checkLog_sound (w := (23774986759 / 148774986759)) (n := 12)
    (lo := (161186579 / 500000000)) (hi := (322373159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86274986759 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86274986759 / 62500000000) = 1/(62500000000 / 86274986759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161186579 / 500000000) (322373159 / 1000000000) (Real.log (86274986759 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (86274986759 / 62500000000) = -Real.log (62500000000 / 86274986759) := by
    rw [show ((86274986759 / 62500000000) : ℝ) = ((62500000000 / 86274986759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (323009439 / 1000000000) ≤ -Real.log (125000000000 / 172659798663) ∧
    -Real.log (125000000000 / 172659798663) ≤ (2018809 / 6250000) := by
  have h := checkLog_sound (w := (47659798663 / 297659798663)) (n := 12)
    (lo := (323009439 / 1000000000)) (hi := (2018809 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172659798663 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172659798663 / 125000000000) = 1/(125000000000 / 172659798663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (323009439 / 1000000000) (2018809 / 6250000) (Real.log (172659798663 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172659798663 / 125000000000) = -Real.log (125000000000 / 172659798663) := by
    rw [show ((172659798663 / 125000000000) : ℝ) = ((125000000000 / 172659798663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25971163 / 1000000000) ≤ -Real.log (38974527471 / 40000000000) ∧
    -Real.log (38974527471 / 40000000000) ≤ (6492791 / 250000000) := by
  have h := checkLog_sound (w := (1025472529 / 78974527471)) (n := 12)
    (lo := (25971163 / 1000000000)) (hi := (6492791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38974527471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38974527471) = 1/(38974527471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6492791 / 250000000) (-25971163 / 1000000000) (Real.log (38974527471 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25869383 / 1000000000) ≤ -Real.log (38978494479 / 40000000000) ∧
    -Real.log (38978494479 / 40000000000) ≤ (3233673 / 125000000) := by
  have h := checkLog_sound (w := (1021505521 / 78978494479)) (n := 12)
    (lo := (25869383 / 1000000000)) (hi := (3233673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38978494479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38978494479) = 1/(38978494479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3233673 / 125000000) (-25869383 / 1000000000) (Real.log (38978494479 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell109
