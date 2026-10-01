import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190
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

theorem reflection_log_1_neg : (308891109 / 1000000000) ≤ -Real.log (5120 / 6973) ∧
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


theorem reflection_log_1 : Bounds (308891109 / 1000000000) (30889111 / 100000000) (Real.log (6973 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6973 / 5120) = -Real.log (5120 / 6973) := by
    rw [show ((6973 / 5120) : ℝ) = ((5120 / 6973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224641153 / 500000000) ≤ -Real.log (3267 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-449282307 / 1000000000) (-224641153 / 500000000) (Real.log (3267 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61692157 / 200000000) ≤ -Real.log (512 / 697) ∧
    -Real.log (512 / 697) ≤ (154230393 / 500000000) := by
  have h := checkLog_sound (w := (185 / 1209)) (n := 12)
    (lo := (61692157 / 200000000)) (hi := (154230393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 512) = 1/(512 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61692157 / 200000000) (154230393 / 500000000) (Real.log (697 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (697 / 512) = -Real.log (512 / 697) := by
    rw [show ((697 / 512) : ℝ) = ((512 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224182227 / 500000000) ≤ -Real.log (327 / 512) ∧
    -Real.log (327 / 512) ≤ (89672891 / 200000000) := by
  have h := checkLog_sound (w := (185 / 839)) (n := 12)
    (lo := (224182227 / 500000000)) (hi := (89672891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 327) = 1/(327 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) (Real.log (327 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (228702471 / 1000000000) ≤ -Real.log (125000 / 157121) ∧
    -Real.log (125000 / 157121) ≤ (28587809 / 125000000) := by
  have h := checkLog_sound (w := (32121 / 282121)) (n := 12)
    (lo := (228702471 / 1000000000)) (hi := (28587809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157121 / 125000) = 1/(125000 / 157121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (228702471 / 1000000000) (28587809 / 125000000) (Real.log (157121 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (157121 / 125000) = -Real.log (125000 / 157121) := by
    rw [show ((157121 / 125000) : ℝ) = ((125000 / 157121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (148508083 / 500000000) ≤ -Real.log (92879 / 125000) ∧
    -Real.log (92879 / 125000) ≤ (297016167 / 1000000000) := by
  have h := checkLog_sound (w := (32121 / 217879)) (n := 12)
    (lo := (148508083 / 500000000)) (hi := (297016167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92879) = 1/(92879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-297016167 / 1000000000) (-148508083 / 500000000) (Real.log (92879 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (229038939 / 1000000000) ≤ -Real.log (1000000 / 1257391) ∧
    -Real.log (1000000 / 1257391) ≤ (11451947 / 50000000) := by
  have h := checkLog_sound (w := (257391 / 2257391)) (n := 12)
    (lo := (229038939 / 1000000000)) (hi := (11451947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257391 / 1000000) = 1/(1000000 / 1257391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (229038939 / 1000000000) (11451947 / 50000000) (Real.log (1257391 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1257391 / 1000000) = -Real.log (1000000 / 1257391) := by
    rw [show ((1257391 / 1000000) : ℝ) = ((1000000 / 1257391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (297585617 / 1000000000) ≤ -Real.log (742609 / 1000000) ∧
    -Real.log (742609 / 1000000) ≤ (148792809 / 500000000) := by
  have h := checkLog_sound (w := (257391 / 1742609)) (n := 12)
    (lo := (297585617 / 1000000000)) (hi := (148792809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742609) = 1/(742609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-148792809 / 500000000) (-297585617 / 1000000000) (Real.log (742609 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169817877 / 1000000000) ≤ -Real.log (1000000 / 1185089) ∧
    -Real.log (1000000 / 1185089) ≤ (84908939 / 500000000) := by
  have h := checkLog_sound (w := (185089 / 2185089)) (n := 12)
    (lo := (169817877 / 1000000000)) (hi := (84908939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185089 / 1000000) = 1/(1000000 / 1185089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169817877 / 1000000000) (84908939 / 500000000) (Real.log (1185089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1185089 / 1000000) = -Real.log (1000000 / 1185089) := by
    rw [show ((1185089 / 1000000) : ℝ) = ((1000000 / 1185089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102338187 / 500000000) ≤ -Real.log (814911 / 1000000) ∧
    -Real.log (814911 / 1000000) ≤ (1637411 / 8000000) := by
  have h := checkLog_sound (w := (185089 / 1814911)) (n := 12)
    (lo := (102338187 / 500000000)) (hi := (1637411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814911) = 1/(814911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1637411 / 8000000) (-102338187 / 500000000) (Real.log (814911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21260561 / 125000000) ≤ -Real.log (200000 / 237081) ∧
    -Real.log (200000 / 237081) ≤ (170084489 / 1000000000) := by
  have h := checkLog_sound (w := (37081 / 437081)) (n := 12)
    (lo := (21260561 / 125000000)) (hi := (170084489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237081 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237081 / 200000) = 1/(200000 / 237081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21260561 / 125000000) (170084489 / 1000000000) (Real.log (237081 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (237081 / 200000) = -Real.log (200000 / 237081) := by
    rw [show ((237081 / 200000) : ℝ) = ((200000 / 237081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (205064221 / 1000000000) ≤ -Real.log (162919 / 200000) ∧
    -Real.log (162919 / 200000) ≤ (102532111 / 500000000) := by
  have h := checkLog_sound (w := (37081 / 362919)) (n := 12)
    (lo := (205064221 / 1000000000)) (hi := (102532111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162919) = 1/(162919 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-102532111 / 500000000) (-205064221 / 1000000000) (Real.log (162919 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (756825239 / 1000000000) ≤ -Real.log (250000000000 / 532874617737) ∧
    -Real.log (250000000000 / 532874617737) ≤ (756825241 / 1000000000) := by
  have h := checkLog_sound (w := (32874617737 / 1032874617737)) (n := 12)
    (lo := (63678059 / 1000000000)) (hi := (3183903 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532874617737 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532874617737 / 500000000000) = 1/(250000000000 / 532874617737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (756825239 / 1000000000) (756825241 / 1000000000) (Real.log (532874617737 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (532874617737 / 250000000000) = -Real.log (250000000000 / 532874617737) := by
    rw [show ((532874617737 / 250000000000) : ℝ) = ((250000000000 / 532874617737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151634683 / 200000000) ≤ -Real.log (500000000000 / 1067187021733) ∧
    -Real.log (500000000000 / 1067187021733) ≤ (758173417 / 1000000000) := by
  have h := checkLog_sound (w := (67187021733 / 2067187021733)) (n := 12)
    (lo := (13005247 / 200000000)) (hi := (16256559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067187021733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1067187021733 / 1000000000000) = 1/(500000000000 / 1067187021733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151634683 / 200000000) (758173417 / 1000000000) (Real.log (1067187021733 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1067187021733 / 500000000000) = -Real.log (500000000000 / 1067187021733) := by
    rw [show ((1067187021733 / 500000000000) : ℝ) = ((500000000000 / 1067187021733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (262859319 / 500000000) ≤ -Real.log (100000000000 / 169167411363) ∧
    -Real.log (100000000000 / 169167411363) ≤ (525718639 / 1000000000) := by
  have h := checkLog_sound (w := (69167411363 / 269167411363)) (n := 12)
    (lo := (262859319 / 500000000)) (hi := (525718639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169167411363 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169167411363 / 100000000000) = 1/(100000000000 / 169167411363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (262859319 / 500000000) (525718639 / 1000000000) (Real.log (169167411363 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (169167411363 / 100000000000) = -Real.log (100000000000 / 169167411363) := by
    rw [show ((169167411363 / 100000000000) : ℝ) = ((100000000000 / 169167411363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (526624557 / 1000000000) ≤ -Real.log (50000000000 / 84660366357) ∧
    -Real.log (50000000000 / 84660366357) ≤ (263312279 / 500000000) := by
  have h := checkLog_sound (w := (34660366357 / 134660366357)) (n := 12)
    (lo := (526624557 / 1000000000)) (hi := (263312279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84660366357 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84660366357 / 50000000000) = 1/(50000000000 / 84660366357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (526624557 / 1000000000) (263312279 / 500000000) (Real.log (84660366357 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (84660366357 / 50000000000) = -Real.log (50000000000 / 84660366357) := by
    rw [show ((84660366357 / 50000000000) : ℝ) = ((50000000000 / 84660366357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (374494251 / 1000000000) ≤ -Real.log (100000000000 / 145425574081) ∧
    -Real.log (100000000000 / 145425574081) ≤ (93623563 / 250000000) := by
  have h := checkLog_sound (w := (45425574081 / 245425574081)) (n := 12)
    (lo := (374494251 / 1000000000)) (hi := (93623563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145425574081 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145425574081 / 100000000000) = 1/(100000000000 / 145425574081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (374494251 / 1000000000) (93623563 / 250000000) (Real.log (145425574081 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145425574081 / 100000000000) = -Real.log (100000000000 / 145425574081) := by
    rw [show ((145425574081 / 100000000000) : ℝ) = ((100000000000 / 145425574081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37514871 / 100000000) ≤ -Real.log (250000000000 / 363801950663) ∧
    -Real.log (250000000000 / 363801950663) ≤ (375148711 / 1000000000) := by
  have h := checkLog_sound (w := (113801950663 / 613801950663)) (n := 12)
    (lo := (37514871 / 100000000)) (hi := (375148711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363801950663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363801950663 / 250000000000) = 1/(250000000000 / 363801950663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37514871 / 100000000) (375148711 / 1000000000) (Real.log (363801950663 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (363801950663 / 250000000000) = -Real.log (250000000000 / 363801950663) := by
    rw [show ((363801950663 / 250000000000) : ℝ) = ((250000000000 / 363801950663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34979733 / 1000000000) ≤ -Real.log (38624999439 / 40000000000) ∧
    -Real.log (38624999439 / 40000000000) ≤ (17489867 / 500000000) := by
  have h := checkLog_sound (w := (1375000561 / 78624999439)) (n := 12)
    (lo := (34979733 / 1000000000)) (hi := (17489867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38624999439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38624999439) = 1/(38624999439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17489867 / 500000000) (-34979733 / 1000000000) (Real.log (38624999439 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (68083 / 1953125) ≤ -Real.log (965742062079 / 1000000000000) ∧
    -Real.log (965742062079 / 1000000000000) ≤ (34858497 / 1000000000) := by
  have h := checkLog_sound (w := (34257937921 / 1965742062079)) (n := 12)
    (lo := (68083 / 1953125)) (hi := (34858497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965742062079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965742062079) = 1/(965742062079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34858497 / 1000000000) (-68083 / 1953125) (Real.log (965742062079 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell190
