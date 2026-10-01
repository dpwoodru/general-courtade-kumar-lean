import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0479
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

theorem reflection_log_1_neg : (182443619 / 1000000000) ≤ -Real.log (20480 / 24579) ∧
    -Real.log (20480 / 24579) ≤ (9122181 / 50000000) := by
  have h := checkLog_sound (w := (4099 / 45059)) (n := 12)
    (lo := (182443619 / 1000000000)) (hi := (9122181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24579 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24579 / 20480) = 1/(20480 / 24579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (182443619 / 1000000000) (9122181 / 50000000) (Real.log (24579 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24579 / 20480) = -Real.log (20480 / 24579) := by
    rw [show ((24579 / 20480) : ℝ) = ((20480 / 24579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223326673 / 1000000000) ≤ -Real.log (16381 / 20480) ∧
    -Real.log (16381 / 20480) ≤ (111663337 / 500000000) := by
  have h := checkLog_sound (w := (4099 / 36861)) (n := 12)
    (lo := (223326673 / 1000000000)) (hi := (111663337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16381) = 1/(16381 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111663337 / 500000000) (-223326673 / 1000000000) (Real.log (16381 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168340739 / 500000000) ≤ -Real.log (10240 / 14339) ∧
    -Real.log (10240 / 14339) ≤ (336681479 / 1000000000) := by
  have h := checkLog_sound (w := (4099 / 24579)) (n := 12)
    (lo := (168340739 / 500000000)) (hi := (336681479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14339 / 10240) = 1/(10240 / 14339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168340739 / 500000000) (336681479 / 1000000000) (Real.log (14339 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14339 / 10240) = -Real.log (10240 / 14339) := by
    rw [show ((14339 / 10240) : ℝ) = ((10240 / 14339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63914253 / 125000000) ≤ -Real.log (6141 / 10240) ∧
    -Real.log (6141 / 10240) ≤ (20452561 / 40000000) := by
  have h := checkLog_sound (w := (4099 / 16381)) (n := 12)
    (lo := (63914253 / 125000000)) (hi := (20452561 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6141) = 1/(6141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20452561 / 40000000) (-63914253 / 125000000) (Real.log (6141 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125326827 / 500000000) ≤ -Real.log (200000 / 256973) ∧
    -Real.log (200000 / 256973) ≤ (50130731 / 200000000) := by
  have h := checkLog_sound (w := (56973 / 456973)) (n := 12)
    (lo := (125326827 / 500000000)) (hi := (50130731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256973 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256973 / 200000) = 1/(200000 / 256973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125326827 / 500000000) (50130731 / 200000000) (Real.log (256973 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (256973 / 200000) = -Real.log (200000 / 256973) := by
    rw [show ((256973 / 200000) : ℝ) = ((200000 / 256973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167641971 / 500000000) ≤ -Real.log (143027 / 200000) ∧
    -Real.log (143027 / 200000) ≤ (335283943 / 1000000000) := by
  have h := checkLog_sound (w := (56973 / 343027)) (n := 12)
    (lo := (167641971 / 500000000)) (hi := (335283943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143027) = 1/(143027 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-335283943 / 1000000000) (-167641971 / 500000000) (Real.log (143027 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (125409319 / 500000000) ≤ -Real.log (1000000 / 1285077) ∧
    -Real.log (1000000 / 1285077) ≤ (250818639 / 1000000000) := by
  have h := checkLog_sound (w := (285077 / 2285077)) (n := 12)
    (lo := (125409319 / 500000000)) (hi := (250818639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285077 / 1000000) = 1/(1000000 / 1285077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (125409319 / 500000000) (250818639 / 1000000000) (Real.log (1285077 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285077 / 1000000) = -Real.log (1000000 / 1285077) := by
    rw [show ((1285077 / 1000000) : ℝ) = ((1000000 / 1285077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167790217 / 500000000) ≤ -Real.log (714923 / 1000000) ∧
    -Real.log (714923 / 1000000) ≤ (67116087 / 200000000) := by
  have h := checkLog_sound (w := (285077 / 1714923)) (n := 12)
    (lo := (167790217 / 500000000)) (hi := (67116087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714923) = 1/(714923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67116087 / 200000000) (-167790217 / 500000000) (Real.log (714923 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1463741 / 7812500) ≤ -Real.log (50000 / 60303) ∧
    -Real.log (50000 / 60303) ≤ (187358849 / 1000000000) := by
  have h := checkLog_sound (w := (10303 / 110303)) (n := 12)
    (lo := (1463741 / 7812500)) (hi := (187358849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60303 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60303 / 50000) = 1/(50000 / 60303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1463741 / 7812500) (187358849 / 1000000000) (Real.log (60303 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60303 / 50000) = -Real.log (50000 / 60303) := by
    rw [show ((60303 / 50000) : ℝ) = ((50000 / 60303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (230747387 / 1000000000) ≤ -Real.log (39697 / 50000) ∧
    -Real.log (39697 / 50000) ≤ (57686847 / 250000000) := by
  have h := checkLog_sound (w := (10303 / 89697)) (n := 12)
    (lo := (230747387 / 1000000000)) (hi := (57686847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39697) = 1/(39697 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57686847 / 250000000) (-230747387 / 1000000000) (Real.log (39697 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (187492331 / 1000000000) ≤ -Real.log (1000000 / 1206221) ∧
    -Real.log (1000000 / 1206221) ≤ (46873083 / 250000000) := by
  have h := checkLog_sound (w := (206221 / 2206221)) (n := 12)
    (lo := (187492331 / 1000000000)) (hi := (46873083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206221 / 1000000) = 1/(1000000 / 1206221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187492331 / 1000000000) (46873083 / 250000000) (Real.log (1206221 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1206221 / 1000000) = -Real.log (1000000 / 1206221) := by
    rw [show ((1206221 / 1000000) : ℝ) = ((1000000 / 1206221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (115475097 / 500000000) ≤ -Real.log (793779 / 1000000) ∧
    -Real.log (793779 / 1000000) ≤ (46190039 / 200000000) := by
  have h := checkLog_sound (w := (206221 / 1793779)) (n := 12)
    (lo := (115475097 / 500000000)) (hi := (46190039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793779) = 1/(793779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46190039 / 200000000) (-115475097 / 500000000) (Real.log (793779 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (585937597 / 1000000000) ≤ -Real.log (250000000000 / 449168688429) ∧
    -Real.log (250000000000 / 449168688429) ≤ (292968799 / 500000000) := by
  have h := checkLog_sound (w := (199168688429 / 699168688429)) (n := 12)
    (lo := (585937597 / 1000000000)) (hi := (292968799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449168688429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449168688429 / 250000000000) = 1/(250000000000 / 449168688429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (585937597 / 1000000000) (292968799 / 500000000) (Real.log (449168688429 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449168688429 / 250000000000) = -Real.log (250000000000 / 449168688429) := by
    rw [show ((449168688429 / 250000000000) : ℝ) = ((250000000000 / 449168688429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (586399073 / 1000000000) ≤ -Real.log (125000000000 / 224688008359) ∧
    -Real.log (125000000000 / 224688008359) ≤ (293199537 / 500000000) := by
  have h := checkLog_sound (w := (99688008359 / 349688008359)) (n := 12)
    (lo := (586399073 / 1000000000)) (hi := (293199537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224688008359 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224688008359 / 125000000000) = 1/(125000000000 / 224688008359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (586399073 / 1000000000) (293199537 / 500000000) (Real.log (224688008359 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (224688008359 / 125000000000) = -Real.log (125000000000 / 224688008359) := by
    rw [show ((224688008359 / 125000000000) : ℝ) = ((125000000000 / 224688008359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (83621247 / 200000000) ≤ -Real.log (500000000000 / 759541023251) ∧
    -Real.log (500000000000 / 759541023251) ≤ (104526559 / 250000000) := by
  have h := checkLog_sound (w := (259541023251 / 1259541023251)) (n := 12)
    (lo := (83621247 / 200000000)) (hi := (104526559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759541023251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759541023251 / 500000000000) = 1/(500000000000 / 759541023251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (83621247 / 200000000) (104526559 / 250000000) (Real.log (759541023251 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (759541023251 / 500000000000) = -Real.log (500000000000 / 759541023251) := by
    rw [show ((759541023251 / 500000000000) : ℝ) = ((500000000000 / 759541023251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16737701 / 40000000) ≤ -Real.log (20000000000 / 30391859699) ∧
    -Real.log (20000000000 / 30391859699) ≤ (209221263 / 500000000) := by
  have h := checkLog_sound (w := (10391859699 / 50391859699)) (n := 12)
    (lo := (16737701 / 40000000)) (hi := (209221263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30391859699 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30391859699 / 20000000000) = 1/(20000000000 / 30391859699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16737701 / 40000000) (209221263 / 500000000) (Real.log (30391859699 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (30391859699 / 20000000000) = -Real.log (20000000000 / 30391859699) := by
    rw [show ((30391859699 / 20000000000) : ℝ) = ((20000000000 / 30391859699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0479
