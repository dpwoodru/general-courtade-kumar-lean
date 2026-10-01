import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0477
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

theorem reflection_log_1_neg : (1826877 / 10000000) ≤ -Real.log (4096 / 4917) ∧
    -Real.log (4096 / 4917) ≤ (182687701 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 9013)) (n := 12)
    (lo := (1826877 / 10000000)) (hi := (182687701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4917 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4917 / 4096) = 1/(4096 / 4917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1826877 / 10000000) (182687701 / 1000000000) (Real.log (4917 / 4096)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4917 / 4096) = -Real.log (4096 / 4917) := by
    rw [show ((4917 / 4096) : ℝ) = ((4096 / 4917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (111846509 / 500000000) ≤ -Real.log (3275 / 4096) ∧
    -Real.log (3275 / 4096) ≤ (223693019 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 7371)) (n := 12)
    (lo := (111846509 / 500000000)) (hi := (223693019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4096 / 3275) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4096 / 3275) = 1/(3275 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223693019 / 1000000000) (-111846509 / 500000000) (Real.log (3275 / 4096)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (182565667 / 1000000000) ≤ -Real.log (10240 / 12291) ∧
    -Real.log (10240 / 12291) ≤ (45641417 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 22531)) (n := 12)
    (lo := (182565667 / 1000000000)) (hi := (45641417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12291 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12291 / 10240) = 1/(10240 / 12291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (182565667 / 1000000000) (45641417 / 250000000) (Real.log (12291 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12291 / 10240) = -Real.log (10240 / 12291) := by
    rw [show ((12291 / 10240) : ℝ) = ((10240 / 12291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223509829 / 1000000000) ≤ -Real.log (8189 / 10240) ∧
    -Real.log (8189 / 10240) ≤ (22350983 / 100000000) := by
  have h := checkLog_sound (w := (2051 / 18429)) (n := 12)
    (lo := (223509829 / 1000000000)) (hi := (22350983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8189) = 1/(8189 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22350983 / 100000000) (-223509829 / 1000000000) (Real.log (8189 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (337099829 / 1000000000) ≤ -Real.log (2048 / 2869) ∧
    -Real.log (2048 / 2869) ≤ (33709983 / 100000000) := by
  have h := checkLog_sound (w := (821 / 4917)) (n := 12)
    (lo := (337099829 / 1000000000)) (hi := (33709983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2869 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2869 / 2048) = 1/(2048 / 2869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (337099829 / 1000000000) (33709983 / 100000000) (Real.log (2869 / 2048)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2869 / 2048) = -Real.log (2048 / 2869) := by
    rw [show ((2869 / 2048) : ℝ) = ((2048 / 2869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (512291541 / 1000000000) ≤ -Real.log (1227 / 2048) ∧
    -Real.log (1227 / 2048) ≤ (256145771 / 500000000) := by
  have h := checkLog_sound (w := (821 / 3275)) (n := 12)
    (lo := (512291541 / 1000000000)) (hi := (256145771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1227) = 1/(1227 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-256145771 / 500000000) (-512291541 / 1000000000) (Real.log (1227 / 2048)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13475627 / 40000000) ≤ -Real.log (5120 / 7171) ∧
    -Real.log (5120 / 7171) ≤ (84222669 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 12291)) (n := 12)
    (lo := (13475627 / 40000000)) (hi := (84222669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7171 / 5120) = 1/(5120 / 7171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13475627 / 40000000) (84222669 / 250000000) (Real.log (7171 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7171 / 5120) = -Real.log (5120 / 7171) := by
    rw [show ((7171 / 5120) : ℝ) = ((5120 / 7171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (511802663 / 1000000000) ≤ -Real.log (3069 / 5120) ∧
    -Real.log (3069 / 5120) ≤ (63975333 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 8189)) (n := 12)
    (lo := (511802663 / 1000000000)) (hi := (63975333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3069) = 1/(3069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-63975333 / 125000000) (-511802663 / 1000000000) (Real.log (3069 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (250982817 / 1000000000) ≤ -Real.log (125000 / 160661) ∧
    -Real.log (125000 / 160661) ≤ (125491409 / 500000000) := by
  have h := checkLog_sound (w := (35661 / 285661)) (n := 12)
    (lo := (250982817 / 1000000000)) (hi := (125491409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160661 / 125000) = 1/(125000 / 160661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (250982817 / 1000000000) (125491409 / 500000000) (Real.log (160661 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160661 / 125000) = -Real.log (125000 / 160661) := by
    rw [show ((160661 / 125000) : ℝ) = ((125000 / 160661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (167937807 / 500000000) ≤ -Real.log (89339 / 125000) ∧
    -Real.log (89339 / 125000) ≤ (67175123 / 200000000) := by
  have h := checkLog_sound (w := (35661 / 214339)) (n := 12)
    (lo := (167937807 / 500000000)) (hi := (67175123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89339) = 1/(89339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-67175123 / 200000000) (-167937807 / 500000000) (Real.log (89339 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10045941 / 40000000) ≤ -Real.log (1000000 / 1285501) ∧
    -Real.log (1000000 / 1285501) ≤ (125574263 / 500000000) := by
  have h := checkLog_sound (w := (285501 / 2285501)) (n := 12)
    (lo := (10045941 / 40000000)) (hi := (125574263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285501 / 1000000) = 1/(1000000 / 1285501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10045941 / 40000000) (125574263 / 500000000) (Real.log (1285501 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285501 / 1000000) = -Real.log (1000000 / 1285501) := by
    rw [show ((1285501 / 1000000) : ℝ) = ((1000000 / 1285501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (336173681 / 1000000000) ≤ -Real.log (714499 / 1000000) ∧
    -Real.log (714499 / 1000000) ≤ (168086841 / 500000000) := by
  have h := checkLog_sound (w := (285501 / 1714499)) (n := 12)
    (lo := (336173681 / 1000000000)) (hi := (168086841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714499) = 1/(714499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-168086841 / 500000000) (-336173681 / 1000000000) (Real.log (714499 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23453121 / 125000000) ≤ -Real.log (1000000 / 1206381) ∧
    -Real.log (1000000 / 1206381) ≤ (187624969 / 1000000000) := by
  have h := checkLog_sound (w := (206381 / 2206381)) (n := 12)
    (lo := (23453121 / 125000000)) (hi := (187624969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206381 / 1000000) = 1/(1000000 / 1206381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23453121 / 125000000) (187624969 / 1000000000) (Real.log (1206381 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206381 / 1000000) = -Real.log (1000000 / 1206381) := by
    rw [show ((1206381 / 1000000) : ℝ) = ((1000000 / 1206381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231151781 / 1000000000) ≤ -Real.log (793619 / 1000000) ∧
    -Real.log (793619 / 1000000) ≤ (115575891 / 500000000) := by
  have h := checkLog_sound (w := (206381 / 1793619)) (n := 12)
    (lo := (231151781 / 1000000000)) (hi := (115575891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793619) = 1/(793619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-115575891 / 500000000) (-231151781 / 1000000000) (Real.log (793619 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11734901 / 62500000) ≤ -Real.log (500000 / 603271) ∧
    -Real.log (500000 / 603271) ≤ (187758417 / 1000000000) := by
  have h := checkLog_sound (w := (103271 / 1103271)) (n := 12)
    (lo := (11734901 / 62500000)) (hi := (187758417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603271 / 500000) = 1/(500000 / 603271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11734901 / 62500000) (187758417 / 1000000000) (Real.log (603271 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603271 / 500000) = -Real.log (500000 / 603271) := by
    rw [show ((603271 / 500000) : ℝ) = ((500000 / 603271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23135467 / 100000000) ≤ -Real.log (396729 / 500000) ∧
    -Real.log (396729 / 500000) ≤ (231354671 / 1000000000) := by
  have h := checkLog_sound (w := (103271 / 896729)) (n := 12)
    (lo := (23135467 / 100000000)) (hi := (231354671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396729) = 1/(396729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-231354671 / 1000000000) (-23135467 / 100000000) (Real.log (396729 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (9169663 / 15625000) ≤ -Real.log (25000000000 / 44958248917) ∧
    -Real.log (25000000000 / 44958248917) ≤ (586858433 / 1000000000) := by
  have h := checkLog_sound (w := (19958248917 / 69958248917)) (n := 12)
    (lo := (9169663 / 15625000)) (hi := (586858433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44958248917 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44958248917 / 25000000000) = 1/(25000000000 / 44958248917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9169663 / 15625000) (586858433 / 1000000000) (Real.log (44958248917 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44958248917 / 25000000000) = -Real.log (25000000000 / 44958248917) := by
    rw [show ((44958248917 / 25000000000) : ℝ) = ((25000000000 / 44958248917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (293661103 / 500000000) ≤ -Real.log (50000000000 / 89958208479) ∧
    -Real.log (50000000000 / 89958208479) ≤ (587322207 / 1000000000) := by
  have h := checkLog_sound (w := (39958208479 / 139958208479)) (n := 12)
    (lo := (293661103 / 500000000)) (hi := (587322207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89958208479 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89958208479 / 50000000000) = 1/(50000000000 / 89958208479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (293661103 / 500000000) (587322207 / 1000000000) (Real.log (89958208479 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (89958208479 / 50000000000) = -Real.log (50000000000 / 89958208479) := by
    rw [show ((89958208479 / 50000000000) : ℝ) = ((50000000000 / 89958208479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1675107 / 4000000) ≤ -Real.log (250000000000 / 380025238811) ∧
    -Real.log (250000000000 / 380025238811) ≤ (418776751 / 1000000000) := by
  have h := checkLog_sound (w := (130025238811 / 630025238811)) (n := 12)
    (lo := (1675107 / 4000000)) (hi := (418776751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380025238811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380025238811 / 250000000000) = 1/(250000000000 / 380025238811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1675107 / 4000000) (418776751 / 1000000000) (Real.log (380025238811 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (380025238811 / 250000000000) = -Real.log (250000000000 / 380025238811) := by
    rw [show ((380025238811 / 250000000000) : ℝ) = ((250000000000 / 380025238811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (419113087 / 1000000000) ≤ -Real.log (500000000000 / 760306153571) ∧
    -Real.log (500000000000 / 760306153571) ≤ (3274321 / 7812500) := by
  have h := checkLog_sound (w := (260306153571 / 1260306153571)) (n := 12)
    (lo := (419113087 / 1000000000)) (hi := (3274321 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760306153571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760306153571 / 500000000000) = 1/(500000000000 / 760306153571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (419113087 / 1000000000) (3274321 / 7812500) (Real.log (760306153571 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (760306153571 / 500000000000) = -Real.log (500000000000 / 760306153571) := by
    rw [show ((760306153571 / 500000000000) : ℝ) = ((500000000000 / 760306153571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0477
