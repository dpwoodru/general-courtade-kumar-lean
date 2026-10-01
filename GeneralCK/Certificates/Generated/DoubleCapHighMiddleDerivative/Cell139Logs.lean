import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell139
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

theorem reflection_log_1_neg : (35838129 / 125000000) ≤ -Real.log (256 / 341) ∧
    -Real.log (256 / 341) ≤ (286705033 / 1000000000) := by
  have h := checkLog_sound (w := (85 / 597)) (n := 12)
    (lo := (35838129 / 125000000)) (hi := (286705033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 256) = 1/(256 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (35838129 / 125000000) (286705033 / 1000000000) (Real.log (341 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (341 / 256) = -Real.log (256 / 341) := by
    rw [show ((341 / 256) : ℝ) = ((256 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (403513887 / 1000000000) ≤ -Real.log (171 / 256) ∧
    -Real.log (171 / 256) ≤ (12609809 / 31250000) := by
  have h := checkLog_sound (w := (85 / 427)) (n := 12)
    (lo := (403513887 / 1000000000)) (hi := (12609809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 171) = 1/(171 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12609809 / 31250000) (-403513887 / 1000000000) (Real.log (171 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (286265053 / 1000000000) ≤ -Real.log (5120 / 6817) ∧
    -Real.log (5120 / 6817) ≤ (143132527 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 11937)) (n := 12)
    (lo := (286265053 / 1000000000)) (hi := (143132527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6817 / 5120) = 1/(5120 / 6817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (286265053 / 1000000000) (143132527 / 500000000) (Real.log (6817 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6817 / 5120) = -Real.log (5120 / 6817) := by
    rw [show ((6817 / 5120) : ℝ) = ((5120 / 6817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (402637079 / 1000000000) ≤ -Real.log (3423 / 5120) ∧
    -Real.log (3423 / 5120) ≤ (10065927 / 25000000) := by
  have h := checkLog_sound (w := (1697 / 8543)) (n := 12)
    (lo := (402637079 / 1000000000)) (hi := (10065927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3423) = 1/(3423 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10065927 / 25000000) (-402637079 / 1000000000) (Real.log (3423 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (211468461 / 1000000000) ≤ -Real.log (1000000 / 1235491) ∧
    -Real.log (1000000 / 1235491) ≤ (105734231 / 500000000) := by
  have h := checkLog_sound (w := (235491 / 2235491)) (n := 12)
    (lo := (211468461 / 1000000000)) (hi := (105734231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235491 / 1000000) = 1/(1000000 / 1235491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (211468461 / 1000000000) (105734231 / 500000000) (Real.log (1235491 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1235491 / 1000000) = -Real.log (1000000 / 1235491) := by
    rw [show ((1235491 / 1000000) : ℝ) = ((1000000 / 1235491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (268521481 / 1000000000) ≤ -Real.log (764509 / 1000000) ∧
    -Real.log (764509 / 1000000) ≤ (134260741 / 500000000) := by
  have h := checkLog_sound (w := (235491 / 1764509)) (n := 12)
    (lo := (268521481 / 1000000000)) (hi := (134260741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764509) = 1/(764509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134260741 / 500000000) (-268521481 / 1000000000) (Real.log (764509 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13238123 / 62500000) ≤ -Real.log (1000000 / 1235913) ∧
    -Real.log (1000000 / 1235913) ≤ (211809969 / 1000000000) := by
  have h := checkLog_sound (w := (235913 / 2235913)) (n := 12)
    (lo := (13238123 / 62500000)) (hi := (211809969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235913 / 1000000) = 1/(1000000 / 1235913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13238123 / 62500000) (211809969 / 1000000000) (Real.log (1235913 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1235913 / 1000000) = -Real.log (1000000 / 1235913) := by
    rw [show ((1235913 / 1000000) : ℝ) = ((1000000 / 1235913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (269073621 / 1000000000) ≤ -Real.log (764087 / 1000000) ∧
    -Real.log (764087 / 1000000) ≤ (134536811 / 500000000) := by
  have h := checkLog_sound (w := (235913 / 1764087)) (n := 12)
    (lo := (269073621 / 1000000000)) (hi := (134536811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764087) = 1/(764087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-134536811 / 500000000) (-269073621 / 1000000000) (Real.log (764087 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156247907 / 1000000000) ≤ -Real.log (250000 / 292279) ∧
    -Real.log (250000 / 292279) ≤ (39061977 / 250000000) := by
  have h := checkLog_sound (w := (42279 / 542279)) (n := 12)
    (lo := (156247907 / 1000000000)) (hi := (39061977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292279 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292279 / 250000) = 1/(250000 / 292279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156247907 / 1000000000) (39061977 / 250000000) (Real.log (292279 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (292279 / 250000) = -Real.log (250000 / 292279) := by
    rw [show ((292279 / 250000) : ℝ) = ((250000 / 292279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46316271 / 250000000) ≤ -Real.log (207721 / 250000) ∧
    -Real.log (207721 / 250000) ≤ (37053017 / 200000000) := by
  have h := checkLog_sound (w := (42279 / 457721)) (n := 12)
    (lo := (46316271 / 250000000)) (hi := (37053017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 207721) = 1/(207721 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37053017 / 200000000) (-46316271 / 250000000) (Real.log (207721 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7825737 / 50000000) ≤ -Real.log (250000 / 292357) ∧
    -Real.log (250000 / 292357) ≤ (156514741 / 1000000000) := by
  have h := checkLog_sound (w := (42357 / 542357)) (n := 12)
    (lo := (7825737 / 50000000)) (hi := (156514741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292357 / 250000) = 1/(250000 / 292357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7825737 / 50000000) (156514741 / 1000000000) (Real.log (292357 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (292357 / 250000) = -Real.log (250000 / 292357) := by
    rw [show ((292357 / 250000) : ℝ) = ((250000 / 292357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (92820329 / 500000000) ≤ -Real.log (207643 / 250000) ∧
    -Real.log (207643 / 250000) ≤ (185640659 / 1000000000) := by
  have h := checkLog_sound (w := (42357 / 457643)) (n := 12)
    (lo := (92820329 / 500000000)) (hi := (185640659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 207643) = 1/(207643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-185640659 / 1000000000) (-92820329 / 500000000) (Real.log (207643 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (172225533 / 250000000) ≤ -Real.log (500000000000 / 995763949751) ∧
    -Real.log (500000000000 / 995763949751) ≤ (688902133 / 1000000000) := by
  have h := checkLog_sound (w := (495763949751 / 1495763949751)) (n := 12)
    (lo := (172225533 / 250000000)) (hi := (688902133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((995763949751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(995763949751 / 500000000000) = 1/(500000000000 / 995763949751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (172225533 / 250000000) (688902133 / 1000000000) (Real.log (995763949751 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (995763949751 / 500000000000) = -Real.log (500000000000 / 995763949751) := by
    rw [show ((995763949751 / 500000000000) : ℝ) = ((500000000000 / 995763949751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17255473 / 25000000) ≤ -Real.log (15625000000 / 31158625731) ∧
    -Real.log (15625000000 / 31158625731) ≤ (690218921 / 1000000000) := by
  have h := checkLog_sound (w := (15533625731 / 46783625731)) (n := 12)
    (lo := (17255473 / 25000000)) (hi := (690218921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31158625731 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31158625731 / 15625000000) = 1/(15625000000 / 31158625731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (17255473 / 25000000) (690218921 / 1000000000) (Real.log (31158625731 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (31158625731 / 15625000000) = -Real.log (15625000000 / 31158625731) := by
    rw [show ((31158625731 / 15625000000) : ℝ) = ((15625000000 / 31158625731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (479989943 / 1000000000) ≤ -Real.log (50000000000 / 80802907487) ∧
    -Real.log (50000000000 / 80802907487) ≤ (59998743 / 125000000) := by
  have h := checkLog_sound (w := (30802907487 / 130802907487)) (n := 12)
    (lo := (479989943 / 1000000000)) (hi := (59998743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80802907487 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80802907487 / 50000000000) = 1/(50000000000 / 80802907487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (479989943 / 1000000000) (59998743 / 125000000) (Real.log (80802907487 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80802907487 / 50000000000) = -Real.log (50000000000 / 80802907487) := by
    rw [show ((80802907487 / 50000000000) : ℝ) = ((50000000000 / 80802907487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48088359 / 100000000) ≤ -Real.log (500000000000 / 808751490341) ∧
    -Real.log (500000000000 / 808751490341) ≤ (480883591 / 1000000000) := by
  have h := checkLog_sound (w := (308751490341 / 1308751490341)) (n := 12)
    (lo := (48088359 / 100000000)) (hi := (480883591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808751490341 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808751490341 / 500000000000) = 1/(500000000000 / 808751490341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (48088359 / 100000000) (480883591 / 1000000000) (Real.log (808751490341 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (808751490341 / 500000000000) = -Real.log (500000000000 / 808751490341) := by
    rw [show ((808751490341 / 500000000000) : ℝ) = ((500000000000 / 808751490341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (10672281 / 31250000) ≤ -Real.log (100000000000 / 140707487447) ∧
    -Real.log (100000000000 / 140707487447) ≤ (341512993 / 1000000000) := by
  have h := checkLog_sound (w := (40707487447 / 240707487447)) (n := 12)
    (lo := (10672281 / 31250000)) (hi := (341512993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140707487447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140707487447 / 100000000000) = 1/(100000000000 / 140707487447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (10672281 / 31250000) (341512993 / 1000000000) (Real.log (140707487447 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140707487447 / 100000000000) = -Real.log (100000000000 / 140707487447) := by
    rw [show ((140707487447 / 100000000000) : ℝ) = ((100000000000 / 140707487447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (342155399 / 1000000000) ≤ -Real.log (500000000000 / 703989539739) ∧
    -Real.log (500000000000 / 703989539739) ≤ (1710777 / 5000000) := by
  have h := checkLog_sound (w := (203989539739 / 1203989539739)) (n := 12)
    (lo := (342155399 / 1000000000)) (hi := (1710777 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703989539739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703989539739 / 500000000000) = 1/(500000000000 / 703989539739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (342155399 / 1000000000) (1710777 / 5000000) (Real.log (703989539739 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (703989539739 / 500000000000) = -Real.log (500000000000 / 703989539739) := by
    rw [show ((703989539739 / 500000000000) : ℝ) = ((500000000000 / 703989539739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14562959 / 500000000) ≤ -Real.log (60705884551 / 62500000000) ∧
    -Real.log (60705884551 / 62500000000) ≤ (29125919 / 1000000000) := by
  have h := checkLog_sound (w := (1794115449 / 123205884551)) (n := 12)
    (lo := (14562959 / 500000000)) (hi := (29125919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60705884551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60705884551) = 1/(60705884551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29125919 / 1000000000) (-14562959 / 500000000) (Real.log (60705884551 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29017177 / 1000000000) ≤ -Real.log (60712486159 / 62500000000) ∧
    -Real.log (60712486159 / 62500000000) ≤ (14508589 / 500000000) := by
  have h := checkLog_sound (w := (1787513841 / 123212486159)) (n := 12)
    (lo := (29017177 / 1000000000)) (hi := (14508589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60712486159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60712486159) = 1/(60712486159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14508589 / 500000000) (-29017177 / 1000000000) (Real.log (60712486159 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell139
