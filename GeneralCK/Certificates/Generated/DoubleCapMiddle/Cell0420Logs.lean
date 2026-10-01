import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0420
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

theorem reflection_log_1_neg : (195419003 / 1000000000) ≤ -Real.log (1024 / 1245) ∧
    -Real.log (1024 / 1245) ≤ (48854751 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2269)) (n := 12)
    (lo := (195419003 / 1000000000)) (hi := (48854751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245 / 1024) = 1/(1024 / 1245) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (195419003 / 1000000000) (48854751 / 250000000) (Real.log (1245 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1245 / 1024) = -Real.log (1024 / 1245) := by
    rw [show ((1245 / 1024) : ℝ) = ((1024 / 1245) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (243117091 / 1000000000) ≤ -Real.log (803 / 1024) ∧
    -Real.log (803 / 1024) ≤ (60779273 / 250000000) := by
  have h := checkLog_sound (w := (221 / 1827)) (n := 12)
    (lo := (243117091 / 1000000000)) (hi := (60779273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 803) = 1/(803 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60779273 / 250000000) (-243117091 / 1000000000) (Real.log (803 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19517801 / 100000000) ≤ -Real.log (10240 / 12447) ∧
    -Real.log (10240 / 12447) ≤ (195178011 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 22687)) (n := 12)
    (lo := (19517801 / 100000000)) (hi := (195178011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12447 / 10240) = 1/(10240 / 12447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19517801 / 100000000) (195178011 / 1000000000) (Real.log (12447 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12447 / 10240) = -Real.log (10240 / 12447) := by
    rw [show ((12447 / 10240) : ℝ) = ((10240 / 12447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121371781 / 500000000) ≤ -Real.log (8033 / 10240) ∧
    -Real.log (8033 / 10240) ≤ (242743563 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 18273)) (n := 12)
    (lo := (121371781 / 500000000)) (hi := (242743563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8033) = 1/(8033 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242743563 / 1000000000) (-121371781 / 500000000) (Real.log (8033 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (89705269 / 250000000) ≤ -Real.log (512 / 733) ∧
    -Real.log (512 / 733) ≤ (358821077 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1245)) (n := 12)
    (lo := (89705269 / 250000000)) (hi := (358821077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 512) = 1/(512 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (89705269 / 250000000) (358821077 / 1000000000) (Real.log (733 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (733 / 512) = -Real.log (512 / 733) := by
    rw [show ((733 / 512) : ℝ) = ((512 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (565001357 / 1000000000) ≤ -Real.log (291 / 512) ∧
    -Real.log (291 / 512) ≤ (282500679 / 500000000) := by
  have h := checkLog_sound (w := (221 / 803)) (n := 12)
    (lo := (565001357 / 1000000000)) (hi := (282500679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 291) = 1/(291 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-282500679 / 500000000) (-565001357 / 1000000000) (Real.log (291 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (89602929 / 250000000) ≤ -Real.log (5120 / 7327) ∧
    -Real.log (5120 / 7327) ≤ (358411717 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 12447)) (n := 12)
    (lo := (89602929 / 250000000)) (hi := (358411717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7327 / 5120) = 1/(5120 / 7327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (89602929 / 250000000) (358411717 / 1000000000) (Real.log (7327 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7327 / 5120) = -Real.log (5120 / 7327) := by
    rw [show ((7327 / 5120) : ℝ) = ((5120 / 7327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (563970961 / 1000000000) ≤ -Real.log (2913 / 5120) ∧
    -Real.log (2913 / 5120) ≤ (281985481 / 500000000) := by
  have h := checkLog_sound (w := (2207 / 8033)) (n := 12)
    (lo := (563970961 / 1000000000)) (hi := (281985481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2913) = 1/(2913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-281985481 / 500000000) (-563970961 / 1000000000) (Real.log (2913 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (268010601 / 1000000000) ≤ -Real.log (1000000 / 1307361) ∧
    -Real.log (1000000 / 1307361) ≤ (134005301 / 500000000) := by
  have h := checkLog_sound (w := (307361 / 2307361)) (n := 12)
    (lo := (268010601 / 1000000000)) (hi := (134005301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307361 / 1000000) = 1/(1000000 / 1307361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (268010601 / 1000000000) (134005301 / 500000000) (Real.log (1307361 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1307361 / 1000000) = -Real.log (1000000 / 1307361) := by
    rw [show ((1307361 / 1000000) : ℝ) = ((1000000 / 1307361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367246339 / 1000000000) ≤ -Real.log (692639 / 1000000) ∧
    -Real.log (692639 / 1000000) ≤ (18362317 / 50000000) := by
  have h := checkLog_sound (w := (307361 / 1692639)) (n := 12)
    (lo := (367246339 / 1000000000)) (hi := (18362317 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692639) = 1/(692639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18362317 / 50000000) (-367246339 / 1000000000) (Real.log (692639 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10733517 / 40000000) ≤ -Real.log (1000000 / 1307789) ∧
    -Real.log (1000000 / 1307789) ≤ (134168963 / 500000000) := by
  have h := checkLog_sound (w := (307789 / 2307789)) (n := 12)
    (lo := (10733517 / 40000000)) (hi := (134168963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307789 / 1000000) = 1/(1000000 / 1307789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10733517 / 40000000) (134168963 / 500000000) (Real.log (1307789 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1307789 / 1000000) = -Real.log (1000000 / 1307789) := by
    rw [show ((1307789 / 1000000) : ℝ) = ((1000000 / 1307789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45983057 / 125000000) ≤ -Real.log (692211 / 1000000) ∧
    -Real.log (692211 / 1000000) ≤ (367864457 / 1000000000) := by
  have h := checkLog_sound (w := (307789 / 1692211)) (n := 12)
    (lo := (45983057 / 125000000)) (hi := (367864457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692211) = 1/(692211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367864457 / 1000000000) (-45983057 / 125000000) (Real.log (692211 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (100725377 / 500000000) ≤ -Real.log (125000 / 152897) ∧
    -Real.log (125000 / 152897) ≤ (40290151 / 200000000) := by
  have h := checkLog_sound (w := (27897 / 277897)) (n := 12)
    (lo := (100725377 / 500000000)) (hi := (40290151 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152897 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152897 / 125000) = 1/(125000 / 152897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (100725377 / 500000000) (40290151 / 200000000) (Real.log (152897 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (152897 / 125000) = -Real.log (125000 / 152897) := by
    rw [show ((152897 / 125000) : ℝ) = ((125000 / 152897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (126270733 / 500000000) ≤ -Real.log (97103 / 125000) ∧
    -Real.log (97103 / 125000) ≤ (252541467 / 1000000000) := by
  have h := checkLog_sound (w := (27897 / 222103)) (n := 12)
    (lo := (126270733 / 500000000)) (hi := (252541467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97103) = 1/(97103 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-252541467 / 1000000000) (-126270733 / 500000000) (Real.log (97103 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100858619 / 500000000) ≤ -Real.log (500000 / 611751) ∧
    -Real.log (500000 / 611751) ≤ (201717239 / 1000000000) := by
  have h := checkLog_sound (w := (111751 / 1111751)) (n := 12)
    (lo := (100858619 / 500000000)) (hi := (201717239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611751 / 500000) = 1/(500000 / 611751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100858619 / 500000000) (201717239 / 1000000000) (Real.log (611751 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (611751 / 500000) = -Real.log (500000 / 611751) := by
    rw [show ((611751 / 500000) : ℝ) = ((500000 / 611751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (63240303 / 250000000) ≤ -Real.log (388249 / 500000) ∧
    -Real.log (388249 / 500000) ≤ (252961213 / 1000000000) := by
  have h := checkLog_sound (w := (111751 / 888249)) (n := 12)
    (lo := (63240303 / 250000000)) (hi := (252961213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388249) = 1/(388249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-252961213 / 1000000000) (-63240303 / 250000000) (Real.log (388249 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (31762847 / 50000000) ≤ -Real.log (125000000000 / 235938382043) ∧
    -Real.log (125000000000 / 235938382043) ≤ (635256941 / 1000000000) := by
  have h := checkLog_sound (w := (110938382043 / 360938382043)) (n := 12)
    (lo := (31762847 / 50000000)) (hi := (635256941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235938382043 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235938382043 / 125000000000) = 1/(125000000000 / 235938382043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (31762847 / 50000000) (635256941 / 1000000000) (Real.log (235938382043 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (235938382043 / 125000000000) = -Real.log (125000000000 / 235938382043) := by
    rw [show ((235938382043 / 125000000000) : ℝ) = ((125000000000 / 235938382043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (636202381 / 1000000000) ≤ -Real.log (250000000000 / 472323106683) ∧
    -Real.log (250000000000 / 472323106683) ≤ (318101191 / 500000000) := by
  have h := checkLog_sound (w := (222323106683 / 722323106683)) (n := 12)
    (lo := (636202381 / 1000000000)) (hi := (318101191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472323106683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472323106683 / 250000000000) = 1/(250000000000 / 472323106683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (636202381 / 1000000000) (318101191 / 500000000) (Real.log (472323106683 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (472323106683 / 250000000000) = -Real.log (250000000000 / 472323106683) := by
    rw [show ((472323106683 / 250000000000) : ℝ) = ((250000000000 / 472323106683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (453992221 / 1000000000) ≤ -Real.log (31250000000 / 49205804661) ∧
    -Real.log (31250000000 / 49205804661) ≤ (226996111 / 500000000) := by
  have h := checkLog_sound (w := (17955804661 / 80455804661)) (n := 12)
    (lo := (453992221 / 1000000000)) (hi := (226996111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49205804661 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49205804661 / 31250000000) = 1/(31250000000 / 49205804661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (453992221 / 1000000000) (226996111 / 500000000) (Real.log (49205804661 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49205804661 / 31250000000) = -Real.log (31250000000 / 49205804661) := by
    rw [show ((49205804661 / 31250000000) : ℝ) = ((31250000000 / 49205804661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (9093569 / 20000000) ≤ -Real.log (25000000000 / 39391666173) ∧
    -Real.log (25000000000 / 39391666173) ≤ (454678451 / 1000000000) := by
  have h := checkLog_sound (w := (14391666173 / 64391666173)) (n := 12)
    (lo := (9093569 / 20000000)) (hi := (454678451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39391666173 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39391666173 / 25000000000) = 1/(25000000000 / 39391666173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (9093569 / 20000000) (454678451 / 1000000000) (Real.log (39391666173 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39391666173 / 25000000000) = -Real.log (25000000000 / 39391666173) := by
    rw [show ((39391666173 / 25000000000) : ℝ) = ((25000000000 / 39391666173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0420
