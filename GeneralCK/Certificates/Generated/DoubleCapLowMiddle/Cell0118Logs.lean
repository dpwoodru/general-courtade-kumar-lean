import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0118
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

theorem reflection_log_1_neg : (16671183 / 25000000) ≤ -Real.log (25600 / 49871) ∧
    -Real.log (25600 / 49871) ≤ (666847321 / 1000000000) := by
  have h := checkLog_sound (w := (24271 / 75471)) (n := 12)
    (lo := (16671183 / 25000000)) (hi := (666847321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49871 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49871 / 25600) = 1/(25600 / 49871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16671183 / 25000000) (666847321 / 1000000000) (Real.log (49871 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49871 / 25600) = -Real.log (25600 / 49871) := by
    rw [show ((49871 / 25600) : ℝ) = ((25600 / 49871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2958165569 / 1000000000) ≤ -Real.log (1329 / 25600) ∧
    -Real.log (1329 / 25600) ≤ (1479082787 / 500000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1329) = 1/(1329 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1479082787 / 500000000) (-2958165569 / 1000000000) (Real.log (1329 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (83308283 / 125000000) ≤ -Real.log (6400 / 12463) ∧
    -Real.log (6400 / 12463) ≤ (133293253 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 18863)) (n := 12)
    (lo := (83308283 / 125000000)) (hi := (133293253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12463 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12463 / 6400) = 1/(6400 / 12463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (83308283 / 125000000) (133293253 / 200000000) (Real.log (12463 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12463 / 6400) = -Real.log (6400 / 12463) := by
    rw [show ((12463 / 6400) : ℝ) = ((6400 / 12463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (91999073 / 31250000) ≤ -Real.log (337 / 6400) ∧
    -Real.log (337 / 6400) ≤ (2943970341 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 337) = 1/(337 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2943970341 / 1000000000) (-91999073 / 31250000) (Real.log (337 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (639837051 / 1000000000) ≤ -Real.log (12800 / 24271) ∧
    -Real.log (12800 / 24271) ≤ (159959263 / 250000000) := by
  have h := checkLog_sound (w := (11471 / 37071)) (n := 12)
    (lo := (639837051 / 1000000000)) (hi := (159959263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24271 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24271 / 12800) = 1/(12800 / 24271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (639837051 / 1000000000) (159959263 / 250000000) (Real.log (24271 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24271 / 12800) = -Real.log (12800 / 24271) := by
    rw [show ((24271 / 12800) : ℝ) = ((12800 / 24271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2265018389 / 1000000000) ≤ -Real.log (1329 / 12800) ∧
    -Real.log (1329 / 12800) ≤ (2265018393 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1329) = 1/(1329 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2265018393 / 1000000000) (-2265018389 / 1000000000) (Real.log (1329 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (639053917 / 1000000000) ≤ -Real.log (3200 / 6063) ∧
    -Real.log (3200 / 6063) ≤ (319526959 / 500000000) := by
  have h := checkLog_sound (w := (2863 / 9263)) (n := 12)
    (lo := (639053917 / 1000000000)) (hi := (319526959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6063 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6063 / 3200) = 1/(3200 / 6063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (639053917 / 1000000000) (319526959 / 500000000) (Real.log (6063 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6063 / 3200) = -Real.log (3200 / 6063) := by
    rw [show ((6063 / 3200) : ℝ) = ((3200 / 6063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (562705789 / 250000000) ≤ -Real.log (337 / 3200) ∧
    -Real.log (337 / 3200) ≤ (56270579 / 25000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 337) = 1/(337 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56270579 / 25000000) (-562705789 / 250000000) (Real.log (337 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335798313 / 500000000) ≤ -Real.log (12500 / 24467) ∧
    -Real.log (12500 / 24467) ≤ (671596627 / 1000000000) := by
  have h := checkLog_sound (w := (11967 / 36967)) (n := 12)
    (lo := (335798313 / 500000000)) (hi := (671596627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24467 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24467 / 12500) = 1/(12500 / 24467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335798313 / 500000000) (671596627 / 1000000000) (Real.log (24467 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (24467 / 12500) = -Real.log (12500 / 24467) := by
    rw [show ((24467 / 12500) : ℝ) = ((12500 / 24467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (49296289 / 15625000) ≤ -Real.log (533 / 12500) ∧
    -Real.log (533 / 12500) ≤ (3154962501 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 5257)) (n := 12)
    (lo := (23898361 / 62500000)) (hi := (382373777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2132) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2132) = 1/(533 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3154962501 / 1000000000) (-49296289 / 15625000) (Real.log (533 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (335941853 / 500000000) ≤ -Real.log (500000 / 978961) ∧
    -Real.log (500000 / 978961) ≤ (671883707 / 1000000000) := by
  have h := checkLog_sound (w := (478961 / 1478961)) (n := 12)
    (lo := (335941853 / 500000000)) (hi := (671883707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978961 / 500000) = 1/(500000 / 978961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (335941853 / 500000000) (671883707 / 1000000000) (Real.log (978961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (978961 / 500000) = -Real.log (500000 / 978961) := by
    rw [show ((978961 / 500000) : ℝ) = ((500000 / 978961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3168230237 / 1000000000) ≤ -Real.log (21039 / 500000) ∧
    -Real.log (21039 / 500000) ≤ (1584115121 / 500000000) := by
  have h := checkLog_sound (w := (10211 / 52289)) (n := 12)
    (lo := (395641517 / 1000000000)) (hi := (197820759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21039) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21039) = 1/(21039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1584115121 / 500000000) (-3168230237 / 1000000000) (Real.log (21039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (335660353 / 500000000) ≤ -Real.log (50000 / 97841) ∧
    -Real.log (50000 / 97841) ≤ (671320707 / 1000000000) := by
  have h := checkLog_sound (w := (47841 / 147841)) (n := 12)
    (lo := (335660353 / 500000000)) (hi := (671320707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97841 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97841 / 50000) = 1/(50000 / 97841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (335660353 / 500000000) (671320707 / 1000000000) (Real.log (97841 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (97841 / 50000) = -Real.log (50000 / 97841) := by
    rw [show ((97841 / 50000) : ℝ) = ((50000 / 97841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3142377851 / 1000000000) ≤ -Real.log (2159 / 50000) ∧
    -Real.log (2159 / 50000) ≤ (24549827 / 7812500) := by
  have h := checkLog_sound (w := (483 / 2642)) (n := 12)
    (lo := (369789131 / 1000000000)) (hi := (92447283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2159) = 1/(2159 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24549827 / 7812500) (-3142377851 / 1000000000) (Real.log (2159 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (671616551 / 1000000000) ≤ -Real.log (1000000 / 1957399) ∧
    -Real.log (1000000 / 1957399) ≤ (83952069 / 125000000) := by
  have h := checkLog_sound (w := (957399 / 2957399)) (n := 12)
    (lo := (671616551 / 1000000000)) (hi := (83952069 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957399 / 1000000) = 1/(1000000 / 1957399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (671616551 / 1000000000) (83952069 / 125000000) (Real.log (1957399 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1957399 / 1000000) = -Real.log (1000000 / 1957399) := by
    rw [show ((1957399 / 1000000) : ℝ) = ((1000000 / 1957399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3155877549 / 1000000000) ≤ -Real.log (42601 / 1000000) ∧
    -Real.log (42601 / 1000000) ≤ (1577938777 / 500000000) := by
  have h := checkLog_sound (w := (19899 / 105101)) (n := 12)
    (lo := (383288829 / 1000000000)) (hi := (38328883 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42601) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42601) = 1/(42601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1577938777 / 500000000) (-3155877549 / 1000000000) (Real.log (42601 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1913279561 / 500000000) ≤ -Real.log (500000000000 / 22952157598499) ∧
    -Real.log (500000000000 / 22952157598499) ≤ (478319891 / 125000000) := by
  have h := checkLog_sound (w := (6952157598499 / 38952157598499)) (n := 12)
    (lo := (180411611 / 500000000)) (hi := (360823223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22952157598499 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22952157598499 / 16000000000000) = 1/(500000000000 / 22952157598499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1913279561 / 500000000) (478319891 / 125000000) (Real.log (22952157598499 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (22952157598499 / 500000000000) = -Real.log (500000000000 / 22952157598499) := by
    rw [show ((22952157598499 / 500000000000) : ℝ) = ((500000000000 / 22952157598499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (480014243 / 125000000) ≤ -Real.log (125000000000 / 5816347022197) ∧
    -Real.log (125000000000 / 5816347022197) ≤ (76802279 / 20000000) := by
  have h := checkLog_sound (w := (1816347022197 / 9816347022197)) (n := 12)
    (lo := (93594511 / 250000000)) (hi := (74875609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5816347022197 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5816347022197 / 4000000000000) = 1/(125000000000 / 5816347022197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (480014243 / 125000000) (76802279 / 20000000) (Real.log (5816347022197 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5816347022197 / 125000000000) = -Real.log (125000000000 / 5816347022197) := by
    rw [show ((5816347022197 / 125000000000) : ℝ) = ((125000000000 / 5816347022197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3813698557 / 1000000000) ≤ -Real.log (500000000000 / 22658869847151) ∧
    -Real.log (500000000000 / 22658869847151) ≤ (3813698563 / 1000000000) := by
  have h := checkLog_sound (w := (6658869847151 / 38658869847151)) (n := 12)
    (lo := (347962657 / 1000000000)) (hi := (173981329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22658869847151 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22658869847151 / 16000000000000) = 1/(500000000000 / 22658869847151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3813698557 / 1000000000) (3813698563 / 1000000000) (Real.log (22658869847151 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (22658869847151 / 500000000000) = -Real.log (500000000000 / 22658869847151) := by
    rw [show ((22658869847151 / 500000000000) : ℝ) = ((500000000000 / 22658869847151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38274941 / 10000000) ≤ -Real.log (500000000000 / 22973627379639) ∧
    -Real.log (500000000000 / 22973627379639) ≤ (1913747053 / 500000000) := by
  have h := checkLog_sound (w := (6973627379639 / 38973627379639)) (n := 12)
    (lo := (1808791 / 5000000)) (hi := (361758201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22973627379639 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22973627379639 / 16000000000000) = 1/(500000000000 / 22973627379639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38274941 / 10000000) (1913747053 / 500000000) (Real.log (22973627379639 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22973627379639 / 500000000000) = -Real.log (500000000000 / 22973627379639) := by
    rw [show ((22973627379639 / 500000000000) : ℝ) = ((500000000000 / 22973627379639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0118
