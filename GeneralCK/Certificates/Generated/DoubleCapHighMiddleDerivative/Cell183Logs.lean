import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183
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

theorem reflection_log_1_neg : (76468737 / 250000000) ≤ -Real.log (640 / 869) ∧
    -Real.log (640 / 869) ≤ (305874949 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1509)) (n := 12)
    (lo := (76468737 / 250000000)) (hi := (305874949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869 / 640) = 1/(640 / 869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (76468737 / 250000000) (305874949 / 1000000000) (Real.log (869 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (869 / 640) = -Real.log (640 / 869) := by
    rw [show ((869 / 640) : ℝ) = ((640 / 869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (442874961 / 1000000000) ≤ -Real.log (411 / 640) ∧
    -Real.log (411 / 640) ≤ (221437481 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 411) = 1/(411 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) (Real.log (411 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12217733 / 40000000) ≤ -Real.log (5120 / 6949) ∧
    -Real.log (5120 / 6949) ≤ (152721663 / 500000000) := by
  have h := checkLog_sound (w := (1829 / 12069)) (n := 12)
    (lo := (12217733 / 40000000)) (hi := (152721663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6949 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6949 / 5120) = 1/(5120 / 6949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12217733 / 40000000) (152721663 / 500000000) (Real.log (6949 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6949 / 5120) = -Real.log (5120 / 6949) := by
    rw [show ((6949 / 5120) : ℝ) = ((5120 / 6949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (441962969 / 1000000000) ≤ -Real.log (3291 / 5120) ∧
    -Real.log (3291 / 5120) ≤ (44196297 / 100000000) := by
  have h := checkLog_sound (w := (1829 / 8411)) (n := 12)
    (lo := (441962969 / 1000000000)) (hi := (44196297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3291) = 1/(3291 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44196297 / 100000000) (-441962969 / 1000000000) (Real.log (3291 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (226351201 / 1000000000) ≤ -Real.log (15625 / 19594) ∧
    -Real.log (15625 / 19594) ≤ (113175601 / 500000000) := by
  have h := checkLog_sound (w := (3969 / 35219)) (n := 12)
    (lo := (226351201 / 1000000000)) (hi := (113175601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19594 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19594 / 15625) = 1/(15625 / 19594) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (226351201 / 1000000000) (113175601 / 500000000) (Real.log (19594 / 15625)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19594 / 15625) = -Real.log (15625 / 19594) := by
    rw [show ((19594 / 15625) : ℝ) = ((15625 / 19594) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146525563 / 500000000) ≤ -Real.log (11656 / 15625) ∧
    -Real.log (11656 / 15625) ≤ (293051127 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 27281)) (n := 12)
    (lo := (146525563 / 500000000)) (hi := (293051127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11656) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11656) = 1/(11656 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-293051127 / 1000000000) (-146525563 / 500000000) (Real.log (11656 / 15625)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11334423 / 50000000) ≤ -Real.log (1000000 / 1254439) ∧
    -Real.log (1000000 / 1254439) ≤ (226688461 / 1000000000) := by
  have h := checkLog_sound (w := (254439 / 2254439)) (n := 12)
    (lo := (11334423 / 50000000)) (hi := (226688461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254439 / 1000000) = 1/(1000000 / 1254439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11334423 / 50000000) (226688461 / 1000000000) (Real.log (1254439 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1254439 / 1000000) = -Real.log (1000000 / 1254439) := by
    rw [show ((1254439 / 1000000) : ℝ) = ((1000000 / 1254439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (293618323 / 1000000000) ≤ -Real.log (745561 / 1000000) ∧
    -Real.log (745561 / 1000000) ≤ (73404581 / 250000000) := by
  have h := checkLog_sound (w := (254439 / 1745561)) (n := 12)
    (lo := (293618323 / 1000000000)) (hi := (73404581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745561) = 1/(745561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73404581 / 250000000) (-293618323 / 1000000000) (Real.log (745561 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167956369 / 1000000000) ≤ -Real.log (200000 / 236577) ∧
    -Real.log (200000 / 236577) ≤ (16795637 / 100000000) := by
  have h := checkLog_sound (w := (36577 / 436577)) (n := 12)
    (lo := (167956369 / 1000000000)) (hi := (16795637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236577 / 200000) = 1/(200000 / 236577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167956369 / 1000000000) (16795637 / 100000000) (Real.log (236577 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236577 / 200000) = -Real.log (200000 / 236577) := by
    rw [show ((236577 / 200000) : ℝ) = ((200000 / 236577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40395087 / 200000000) ≤ -Real.log (163423 / 200000) ∧
    -Real.log (163423 / 200000) ≤ (50493859 / 250000000) := by
  have h := checkLog_sound (w := (36577 / 363423)) (n := 12)
    (lo := (40395087 / 200000000)) (hi := (50493859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163423) = 1/(163423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50493859 / 250000000) (-40395087 / 200000000) (Real.log (163423 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (168223477 / 1000000000) ≤ -Real.log (1000000 / 1183201) ∧
    -Real.log (1000000 / 1183201) ≤ (84111739 / 500000000) := by
  have h := checkLog_sound (w := (183201 / 2183201)) (n := 12)
    (lo := (168223477 / 1000000000)) (hi := (84111739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183201 / 1000000) = 1/(1000000 / 1183201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (168223477 / 1000000000) (84111739 / 500000000) (Real.log (1183201 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1183201 / 1000000) = -Real.log (1000000 / 1183201) := by
    rw [show ((1183201 / 1000000) : ℝ) = ((1000000 / 1183201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50590559 / 250000000) ≤ -Real.log (816799 / 1000000) ∧
    -Real.log (816799 / 1000000) ≤ (202362237 / 1000000000) := by
  have h := checkLog_sound (w := (183201 / 1816799)) (n := 12)
    (lo := (50590559 / 250000000)) (hi := (202362237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816799) = 1/(816799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-202362237 / 1000000000) (-50590559 / 250000000) (Real.log (816799 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (747406293 / 1000000000) ≤ -Real.log (125000000000 / 263939532057) ∧
    -Real.log (125000000000 / 263939532057) ≤ (149481259 / 200000000) := by
  have h := checkLog_sound (w := (13939532057 / 513939532057)) (n := 12)
    (lo := (54259113 / 1000000000)) (hi := (27129557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263939532057 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263939532057 / 250000000000) = 1/(125000000000 / 263939532057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (747406293 / 1000000000) (149481259 / 200000000) (Real.log (263939532057 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (263939532057 / 125000000000) = -Real.log (125000000000 / 263939532057) := by
    rw [show ((263939532057 / 125000000000) : ℝ) = ((125000000000 / 263939532057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74874991 / 100000000) ≤ -Real.log (125000000000 / 264294403893) ∧
    -Real.log (125000000000 / 264294403893) ≤ (93593739 / 125000000) := by
  have h := checkLog_sound (w := (14294403893 / 514294403893)) (n := 12)
    (lo := (5560273 / 100000000)) (hi := (55602731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264294403893 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264294403893 / 250000000000) = 1/(125000000000 / 264294403893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (74874991 / 100000000) (93593739 / 125000000) (Real.log (264294403893 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (264294403893 / 125000000000) = -Real.log (125000000000 / 264294403893) := by
    rw [show ((264294403893 / 125000000000) : ℝ) = ((125000000000 / 264294403893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (64925291 / 125000000) ≤ -Real.log (500000000000 / 840511324639) ∧
    -Real.log (500000000000 / 840511324639) ≤ (519402329 / 1000000000) := by
  have h := checkLog_sound (w := (340511324639 / 1340511324639)) (n := 12)
    (lo := (64925291 / 125000000)) (hi := (519402329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840511324639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840511324639 / 500000000000) = 1/(500000000000 / 840511324639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64925291 / 125000000) (519402329 / 1000000000) (Real.log (840511324639 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (840511324639 / 500000000000) = -Real.log (500000000000 / 840511324639) := by
    rw [show ((840511324639 / 500000000000) : ℝ) = ((500000000000 / 840511324639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16259587 / 31250000) ≤ -Real.log (125000000000 / 210317968617) ∧
    -Real.log (125000000000 / 210317968617) ≤ (104061357 / 200000000) := by
  have h := checkLog_sound (w := (85317968617 / 335317968617)) (n := 12)
    (lo := (16259587 / 31250000)) (hi := (104061357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210317968617 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210317968617 / 125000000000) = 1/(125000000000 / 210317968617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (16259587 / 31250000) (104061357 / 200000000) (Real.log (210317968617 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210317968617 / 125000000000) = -Real.log (125000000000 / 210317968617) := by
    rw [show ((210317968617 / 125000000000) : ℝ) = ((125000000000 / 210317968617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (92482951 / 250000000) ≤ -Real.log (250000000000 / 361908972421) ∧
    -Real.log (250000000000 / 361908972421) ≤ (73986361 / 200000000) := by
  have h := checkLog_sound (w := (111908972421 / 611908972421)) (n := 12)
    (lo := (92482951 / 250000000)) (hi := (73986361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361908972421 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361908972421 / 250000000000) = 1/(250000000000 / 361908972421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92482951 / 250000000) (73986361 / 200000000) (Real.log (361908972421 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (361908972421 / 250000000000) = -Real.log (250000000000 / 361908972421) := by
    rw [show ((361908972421 / 250000000000) : ℝ) = ((250000000000 / 361908972421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (185292857 / 500000000) ≤ -Real.log (500000000000 / 724291410739) ∧
    -Real.log (500000000000 / 724291410739) ≤ (74117143 / 200000000) := by
  have h := checkLog_sound (w := (224291410739 / 1224291410739)) (n := 12)
    (lo := (185292857 / 500000000)) (hi := (74117143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724291410739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724291410739 / 500000000000) = 1/(500000000000 / 724291410739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (185292857 / 500000000) (74117143 / 200000000) (Real.log (724291410739 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (724291410739 / 500000000000) = -Real.log (500000000000 / 724291410739) := by
    rw [show ((724291410739 / 500000000000) : ℝ) = ((500000000000 / 724291410739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17069379 / 500000000) ≤ -Real.log (966437393599 / 1000000000000) ∧
    -Real.log (966437393599 / 1000000000000) ≤ (34138759 / 1000000000) := by
  have h := checkLog_sound (w := (33562606401 / 1966437393599)) (n := 12)
    (lo := (17069379 / 500000000)) (hi := (34138759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966437393599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966437393599) = 1/(966437393599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34138759 / 1000000000) (-17069379 / 500000000) (Real.log (966437393599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6803813 / 200000000) ≤ -Real.log (38662123071 / 40000000000) ∧
    -Real.log (38662123071 / 40000000000) ≤ (17009533 / 500000000) := by
  have h := checkLog_sound (w := (1337876929 / 78662123071)) (n := 12)
    (lo := (6803813 / 200000000)) (hi := (17009533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38662123071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38662123071) = 1/(38662123071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17009533 / 500000000) (-6803813 / 200000000) (Real.log (38662123071 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell183
