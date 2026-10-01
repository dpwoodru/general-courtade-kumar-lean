import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0431
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

theorem reflection_log_1_neg : (192764881 / 1000000000) ≤ -Real.log (10240 / 12417) ∧
    -Real.log (10240 / 12417) ≤ (96382441 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 22657)) (n := 12)
    (lo := (192764881 / 1000000000)) (hi := (96382441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12417 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12417 / 10240) = 1/(10240 / 12417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (192764881 / 1000000000) (96382441 / 500000000) (Real.log (12417 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12417 / 10240) = -Real.log (10240 / 12417) := by
    rw [show ((12417 / 10240) : ℝ) = ((10240 / 12417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (239015923 / 1000000000) ≤ -Real.log (8063 / 10240) ∧
    -Real.log (8063 / 10240) ≤ (59753981 / 250000000) := by
  have h := checkLog_sound (w := (2177 / 18303)) (n := 12)
    (lo := (239015923 / 1000000000)) (hi := (59753981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8063) = 1/(8063 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59753981 / 250000000) (-239015923 / 1000000000) (Real.log (8063 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12032703 / 62500000) ≤ -Real.log (5120 / 6207) ∧
    -Real.log (5120 / 6207) ≤ (192523249 / 1000000000) := by
  have h := checkLog_sound (w := (1087 / 11327)) (n := 12)
    (lo := (12032703 / 62500000)) (hi := (192523249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6207 / 5120) = 1/(5120 / 6207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12032703 / 62500000) (192523249 / 1000000000) (Real.log (6207 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6207 / 5120) = -Real.log (5120 / 6207) := by
    rw [show ((6207 / 5120) : ℝ) = ((5120 / 6207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (238643923 / 1000000000) ≤ -Real.log (4033 / 5120) ∧
    -Real.log (4033 / 5120) ≤ (59660981 / 250000000) := by
  have h := checkLog_sound (w := (1087 / 9153)) (n := 12)
    (lo := (238643923 / 1000000000)) (hi := (59660981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4033) = 1/(4033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59660981 / 250000000) (-238643923 / 1000000000) (Real.log (4033 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (70861773 / 200000000) ≤ -Real.log (5120 / 7297) ∧
    -Real.log (5120 / 7297) ≤ (177154433 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 12417)) (n := 12)
    (lo := (70861773 / 200000000)) (hi := (177154433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7297 / 5120) = 1/(5120 / 7297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (70861773 / 200000000) (177154433 / 500000000) (Real.log (7297 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7297 / 5120) = -Real.log (5120 / 7297) := by
    rw [show ((7297 / 5120) : ℝ) = ((5120 / 7297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (553724969 / 1000000000) ≤ -Real.log (2943 / 5120) ∧
    -Real.log (2943 / 5120) ≤ (55372497 / 100000000) := by
  have h := checkLog_sound (w := (2177 / 8063)) (n := 12)
    (lo := (553724969 / 1000000000)) (hi := (55372497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2943) = 1/(2943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55372497 / 100000000) (-553724969 / 1000000000) (Real.log (2943 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (353897653 / 1000000000) ≤ -Real.log (2560 / 3647) ∧
    -Real.log (2560 / 3647) ≤ (176948827 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 6207)) (n := 12)
    (lo := (353897653 / 1000000000)) (hi := (176948827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3647 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3647 / 2560) = 1/(2560 / 3647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (353897653 / 1000000000) (176948827 / 500000000) (Real.log (3647 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3647 / 2560) = -Real.log (2560 / 3647) := by
    rw [show ((3647 / 2560) : ℝ) = ((2560 / 3647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (552706121 / 1000000000) ≤ -Real.log (1473 / 2560) ∧
    -Real.log (1473 / 2560) ≤ (276353061 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 4033)) (n := 12)
    (lo := (552706121 / 1000000000)) (hi := (276353061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1473) = 1/(1473 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-276353061 / 500000000) (-552706121 / 1000000000) (Real.log (1473 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132214143 / 500000000) ≤ -Real.log (500000 / 651343) ∧
    -Real.log (500000 / 651343) ≤ (264428287 / 1000000000) := by
  have h := checkLog_sound (w := (151343 / 1151343)) (n := 12)
    (lo := (132214143 / 500000000)) (hi := (264428287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651343 / 500000) = 1/(500000 / 651343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132214143 / 500000000) (264428287 / 1000000000) (Real.log (651343 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (651343 / 500000) = -Real.log (500000 / 651343) := by
    rw [show ((651343 / 500000) : ℝ) = ((500000 / 651343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (360519467 / 1000000000) ≤ -Real.log (348657 / 500000) ∧
    -Real.log (348657 / 500000) ≤ (90129867 / 250000000) := by
  have h := checkLog_sound (w := (151343 / 848657)) (n := 12)
    (lo := (360519467 / 1000000000)) (hi := (90129867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348657) = 1/(348657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-90129867 / 250000000) (-360519467 / 1000000000) (Real.log (348657 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (264755249 / 1000000000) ≤ -Real.log (125000 / 162889) ∧
    -Real.log (125000 / 162889) ≤ (1059021 / 4000000) := by
  have h := checkLog_sound (w := (37889 / 287889)) (n := 12)
    (lo := (264755249 / 1000000000)) (hi := (1059021 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162889 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162889 / 125000) = 1/(125000 / 162889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (264755249 / 1000000000) (1059021 / 4000000) (Real.log (162889 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (162889 / 125000) = -Real.log (125000 / 162889) := by
    rw [show ((162889 / 125000) : ℝ) = ((125000 / 162889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (361130569 / 1000000000) ≤ -Real.log (87111 / 125000) ∧
    -Real.log (87111 / 125000) ≤ (36113057 / 100000000) := by
  have h := checkLog_sound (w := (37889 / 212111)) (n := 12)
    (lo := (361130569 / 1000000000)) (hi := (36113057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 87111) = 1/(87111 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36113057 / 100000000) (-361130569 / 1000000000) (Real.log (87111 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6203893 / 31250000) ≤ -Real.log (500000 / 609801) ∧
    -Real.log (500000 / 609801) ≤ (198524577 / 1000000000) := by
  have h := checkLog_sound (w := (109801 / 1109801)) (n := 12)
    (lo := (6203893 / 31250000)) (hi := (198524577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609801 / 500000) = 1/(500000 / 609801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6203893 / 31250000) (198524577 / 1000000000) (Real.log (609801 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (609801 / 500000) = -Real.log (500000 / 609801) := by
    rw [show ((609801 / 500000) : ℝ) = ((500000 / 609801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247951233 / 1000000000) ≤ -Real.log (390199 / 500000) ∧
    -Real.log (390199 / 500000) ≤ (123975617 / 500000000) := by
  have h := checkLog_sound (w := (109801 / 890199)) (n := 12)
    (lo := (247951233 / 1000000000)) (hi := (123975617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390199) = 1/(390199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-123975617 / 500000000) (-247951233 / 1000000000) (Real.log (390199 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9939551 / 50000000) ≤ -Real.log (1000000 / 1219927) ∧
    -Real.log (1000000 / 1219927) ≤ (198791021 / 1000000000) := by
  have h := checkLog_sound (w := (219927 / 2219927)) (n := 12)
    (lo := (9939551 / 50000000)) (hi := (198791021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219927 / 1000000) = 1/(1000000 / 1219927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9939551 / 50000000) (198791021 / 1000000000) (Real.log (1219927 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1219927 / 1000000) = -Real.log (1000000 / 1219927) := by
    rw [show ((1219927 / 1000000) : ℝ) = ((1000000 / 1219927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248367773 / 1000000000) ≤ -Real.log (780073 / 1000000) ∧
    -Real.log (780073 / 1000000) ≤ (124183887 / 500000000) := by
  have h := checkLog_sound (w := (219927 / 1780073)) (n := 12)
    (lo := (248367773 / 1000000000)) (hi := (124183887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780073) = 1/(780073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-124183887 / 500000000) (-248367773 / 1000000000) (Real.log (780073 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (312473877 / 500000000) ≤ -Real.log (125000000000 / 233518544013) ∧
    -Real.log (125000000000 / 233518544013) ≤ (124989551 / 200000000) := by
  have h := checkLog_sound (w := (108518544013 / 358518544013)) (n := 12)
    (lo := (312473877 / 500000000)) (hi := (124989551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233518544013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233518544013 / 125000000000) = 1/(125000000000 / 233518544013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (312473877 / 500000000) (124989551 / 200000000) (Real.log (233518544013 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233518544013 / 125000000000) = -Real.log (125000000000 / 233518544013) := by
    rw [show ((233518544013 / 125000000000) : ℝ) = ((125000000000 / 233518544013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (625885819 / 1000000000) ≤ -Real.log (500000000000 / 934950809887) ∧
    -Real.log (500000000000 / 934950809887) ≤ (31294291 / 50000000) := by
  have h := checkLog_sound (w := (434950809887 / 1434950809887)) (n := 12)
    (lo := (625885819 / 1000000000)) (hi := (31294291 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((934950809887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(934950809887 / 500000000000) = 1/(500000000000 / 934950809887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (625885819 / 1000000000) (31294291 / 50000000) (Real.log (934950809887 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (934950809887 / 500000000000) = -Real.log (500000000000 / 934950809887) := by
    rw [show ((934950809887 / 500000000000) : ℝ) = ((500000000000 / 934950809887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (446475809 / 1000000000) ≤ -Real.log (500000000000 / 781397440793) ∧
    -Real.log (500000000000 / 781397440793) ≤ (44647581 / 100000000) := by
  have h := checkLog_sound (w := (281397440793 / 1281397440793)) (n := 12)
    (lo := (446475809 / 1000000000)) (hi := (44647581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781397440793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781397440793 / 500000000000) = 1/(500000000000 / 781397440793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (446475809 / 1000000000) (44647581 / 100000000) (Real.log (781397440793 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (781397440793 / 500000000000) = -Real.log (500000000000 / 781397440793) := by
    rw [show ((781397440793 / 500000000000) : ℝ) = ((500000000000 / 781397440793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (223579397 / 500000000) ≤ -Real.log (50000000000 / 78193130643) ∧
    -Real.log (50000000000 / 78193130643) ≤ (89431759 / 200000000) := by
  have h := checkLog_sound (w := (28193130643 / 128193130643)) (n := 12)
    (lo := (223579397 / 500000000)) (hi := (89431759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78193130643 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78193130643 / 50000000000) = 1/(50000000000 / 78193130643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (223579397 / 500000000) (89431759 / 200000000) (Real.log (78193130643 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (78193130643 / 50000000000) = -Real.log (50000000000 / 78193130643) := by
    rw [show ((78193130643 / 50000000000) : ℝ) = ((50000000000 / 78193130643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0431
