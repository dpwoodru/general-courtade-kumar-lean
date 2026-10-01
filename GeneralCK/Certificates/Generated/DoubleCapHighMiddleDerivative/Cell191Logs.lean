import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191
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

theorem reflection_log_1_neg : (309321247 / 1000000000) ≤ -Real.log (80 / 109) ∧
    -Real.log (80 / 109) ≤ (9666289 / 31250000) := by
  have h := checkLog_sound (w := (29 / 189)) (n := 12)
    (lo := (309321247 / 1000000000)) (hi := (9666289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109 / 80) = 1/(80 / 109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (309321247 / 1000000000) (9666289 / 31250000) (Real.log (109 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (109 / 80) = -Real.log (80 / 109) := by
    rw [show ((109 / 80) : ℝ) = ((80 / 109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (450201001 / 1000000000) ≤ -Real.log (51 / 80) ∧
    -Real.log (51 / 80) ≤ (225100501 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 51) = 1/(51 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-225100501 / 500000000) (-450201001 / 1000000000) (Real.log (51 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (308891109 / 1000000000) ≤ -Real.log (5120 / 6973) ∧
    -Real.log (5120 / 6973) ≤ (30889111 / 100000000) := by
  have h := checkLog_sound (w := (1853 / 12093)) (n := 12)
    (lo := (308891109 / 1000000000)) (hi := (30889111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6973 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6973 / 5120) = 1/(5120 / 6973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (308891109 / 1000000000) (30889111 / 100000000) (Real.log (6973 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6973 / 5120) = -Real.log (5120 / 6973) := by
    rw [show ((6973 / 5120) : ℝ) = ((5120 / 6973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224641153 / 500000000) ≤ -Real.log (3267 / 5120) ∧
    -Real.log (3267 / 5120) ≤ (449282307 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 8387)) (n := 12)
    (lo := (224641153 / 500000000)) (hi := (449282307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3267) = 1/(3267 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) (Real.log (3267 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (57259337 / 250000000) ≤ -Real.log (1000000 / 1257389) ∧
    -Real.log (1000000 / 1257389) ≤ (229037349 / 1000000000) := by
  have h := checkLog_sound (w := (257389 / 2257389)) (n := 12)
    (lo := (57259337 / 250000000)) (hi := (229037349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257389 / 1000000) = 1/(1000000 / 1257389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (57259337 / 250000000) (229037349 / 1000000000) (Real.log (1257389 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1257389 / 1000000) = -Real.log (1000000 / 1257389) := by
    rw [show ((1257389 / 1000000) : ℝ) = ((1000000 / 1257389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74395731 / 250000000) ≤ -Real.log (742611 / 1000000) ∧
    -Real.log (742611 / 1000000) ≤ (11903317 / 40000000) := by
  have h := checkLog_sound (w := (257389 / 1742611)) (n := 12)
    (lo := (74395731 / 250000000)) (hi := (11903317 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742611) = 1/(742611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11903317 / 40000000) (-74395731 / 250000000) (Real.log (742611 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229373703 / 1000000000) ≤ -Real.log (250000 / 314453) ∧
    -Real.log (250000 / 314453) ≤ (28671713 / 125000000) := by
  have h := checkLog_sound (w := (64453 / 564453)) (n := 12)
    (lo := (229373703 / 1000000000)) (hi := (28671713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314453 / 250000) = 1/(250000 / 314453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229373703 / 1000000000) (28671713 / 125000000) (Real.log (314453 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (314453 / 250000) = -Real.log (250000 / 314453) := by
    rw [show ((314453 / 250000) : ℝ) = ((250000 / 314453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (149076349 / 500000000) ≤ -Real.log (185547 / 250000) ∧
    -Real.log (185547 / 250000) ≤ (298152699 / 1000000000) := by
  have h := checkLog_sound (w := (64453 / 435547)) (n := 12)
    (lo := (149076349 / 500000000)) (hi := (298152699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185547) = 1/(185547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-298152699 / 1000000000) (-149076349 / 500000000) (Real.log (185547 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42520911 / 250000000) ≤ -Real.log (250000 / 296351) ∧
    -Real.log (250000 / 296351) ≤ (34016729 / 200000000) := by
  have h := checkLog_sound (w := (46351 / 546351)) (n := 12)
    (lo := (42520911 / 250000000)) (hi := (34016729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296351 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296351 / 250000) = 1/(250000 / 296351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42520911 / 250000000) (34016729 / 200000000) (Real.log (296351 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296351 / 250000) = -Real.log (250000 / 296351) := by
    rw [show ((296351 / 250000) : ℝ) = ((250000 / 296351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102531497 / 500000000) ≤ -Real.log (203649 / 250000) ∧
    -Real.log (203649 / 250000) ≤ (41012599 / 200000000) := by
  have h := checkLog_sound (w := (46351 / 453649)) (n := 12)
    (lo := (102531497 / 500000000)) (hi := (41012599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203649) = 1/(203649 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41012599 / 200000000) (-102531497 / 500000000) (Real.log (203649 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34070037 / 200000000) ≤ -Real.log (25000 / 29643) ∧
    -Real.log (25000 / 29643) ≤ (85175093 / 500000000) := by
  have h := checkLog_sound (w := (4643 / 54643)) (n := 12)
    (lo := (34070037 / 200000000)) (hi := (85175093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29643 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29643 / 25000) = 1/(25000 / 29643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34070037 / 200000000) (85175093 / 500000000) (Real.log (29643 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (29643 / 25000) = -Real.log (25000 / 29643) := by
    rw [show ((29643 / 25000) : ℝ) = ((25000 / 29643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (205450991 / 1000000000) ≤ -Real.log (20357 / 25000) ∧
    -Real.log (20357 / 25000) ≤ (12840687 / 62500000) := by
  have h := checkLog_sound (w := (4643 / 45357)) (n := 12)
    (lo := (205450991 / 1000000000)) (hi := (12840687 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20357) = 1/(20357 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12840687 / 62500000) (-205450991 / 1000000000) (Real.log (20357 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151634683 / 200000000) ≤ -Real.log (125000000000 / 266796755433) ∧
    -Real.log (125000000000 / 266796755433) ≤ (758173417 / 1000000000) := by
  have h := checkLog_sound (w := (16796755433 / 516796755433)) (n := 12)
    (lo := (13005247 / 200000000)) (hi := (16256559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266796755433 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(266796755433 / 250000000000) = 1/(125000000000 / 266796755433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151634683 / 200000000) (758173417 / 1000000000) (Real.log (266796755433 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (266796755433 / 125000000000) = -Real.log (125000000000 / 266796755433) := by
    rw [show ((266796755433 / 125000000000) : ℝ) = ((125000000000 / 266796755433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (94940281 / 125000000) ≤ -Real.log (500000000000 / 1068627450981) ∧
    -Real.log (500000000000 / 1068627450981) ≤ (3038089 / 4000000) := by
  have h := checkLog_sound (w := (68627450981 / 2068627450981)) (n := 12)
    (lo := (16593767 / 250000000)) (hi := (66375069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068627450981 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068627450981 / 1000000000000) = 1/(500000000000 / 1068627450981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (94940281 / 125000000) (3038089 / 4000000) (Real.log (1068627450981 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1068627450981 / 500000000000) = -Real.log (500000000000 / 1068627450981) := by
    rw [show ((1068627450981 / 500000000000) : ℝ) = ((500000000000 / 1068627450981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (526620273 / 1000000000) ≤ -Real.log (15625000000 / 26456251153) ∧
    -Real.log (15625000000 / 26456251153) ≤ (263310137 / 500000000) := by
  have h := checkLog_sound (w := (10831251153 / 42081251153)) (n := 12)
    (lo := (526620273 / 1000000000)) (hi := (263310137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26456251153 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26456251153 / 15625000000) = 1/(15625000000 / 26456251153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (526620273 / 1000000000) (263310137 / 500000000) (Real.log (26456251153 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (26456251153 / 15625000000) = -Real.log (15625000000 / 26456251153) := by
    rw [show ((26456251153 / 15625000000) : ℝ) = ((15625000000 / 26456251153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (263763201 / 500000000) ≤ -Real.log (500000000000 / 847367513353) ∧
    -Real.log (500000000000 / 847367513353) ≤ (527526403 / 1000000000) := by
  have h := checkLog_sound (w := (347367513353 / 1347367513353)) (n := 12)
    (lo := (263763201 / 500000000)) (hi := (527526403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847367513353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847367513353 / 500000000000) = 1/(500000000000 / 847367513353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (263763201 / 500000000) (527526403 / 1000000000) (Real.log (847367513353 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (847367513353 / 500000000000) = -Real.log (500000000000 / 847367513353) := by
    rw [show ((847367513353 / 500000000000) : ℝ) = ((500000000000 / 847367513353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (187573319 / 500000000) ≤ -Real.log (100000000000 / 145520478863) ∧
    -Real.log (100000000000 / 145520478863) ≤ (375146639 / 1000000000) := by
  have h := checkLog_sound (w := (45520478863 / 245520478863)) (n := 12)
    (lo := (187573319 / 500000000)) (hi := (375146639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145520478863 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145520478863 / 100000000000) = 1/(100000000000 / 145520478863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (187573319 / 500000000) (375146639 / 1000000000) (Real.log (145520478863 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145520478863 / 100000000000) = -Real.log (100000000000 / 145520478863) := by
    rw [show ((145520478863 / 100000000000) : ℝ) = ((100000000000 / 145520478863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (46975147 / 125000000) ≤ -Real.log (7812500000 / 11376231149) ∧
    -Real.log (7812500000 / 11376231149) ≤ (375801177 / 1000000000) := by
  have h := checkLog_sound (w := (3563731149 / 19188731149)) (n := 12)
    (lo := (46975147 / 125000000)) (hi := (375801177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11376231149 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11376231149 / 7812500000) = 1/(7812500000 / 11376231149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (46975147 / 125000000) (375801177 / 1000000000) (Real.log (11376231149 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11376231149 / 7812500000) = -Real.log (7812500000 / 11376231149) := by
    rw [show ((11376231149 / 7812500000) : ℝ) = ((7812500000 / 11376231149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17550403 / 500000000) ≤ -Real.log (603442551 / 625000000) ∧
    -Real.log (603442551 / 625000000) ≤ (35100807 / 1000000000) := by
  have h := checkLog_sound (w := (21557449 / 1228442551)) (n := 12)
    (lo := (17550403 / 500000000)) (hi := (35100807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 603442551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 603442551) = 1/(603442551 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35100807 / 1000000000) (-17550403 / 500000000) (Real.log (603442551 / 625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34979349 / 1000000000) ≤ -Real.log (60351584799 / 62500000000) ∧
    -Real.log (60351584799 / 62500000000) ≤ (699587 / 20000000) := by
  have h := checkLog_sound (w := (2148415201 / 122851584799)) (n := 12)
    (lo := (34979349 / 1000000000)) (hi := (699587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60351584799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60351584799) = 1/(60351584799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-699587 / 20000000) (-34979349 / 1000000000) (Real.log (60351584799 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell191
