import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0476
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

theorem reflection_log_1_neg : (91404859 / 500000000) ≤ -Real.log (5120 / 6147) ∧
    -Real.log (5120 / 6147) ≤ (182809719 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 11267)) (n := 12)
    (lo := (91404859 / 500000000)) (hi := (182809719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6147 / 5120) = 1/(5120 / 6147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91404859 / 500000000) (182809719 / 1000000000) (Real.log (6147 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6147 / 5120) = -Real.log (5120 / 6147) := by
    rw [show ((6147 / 5120) : ℝ) = ((5120 / 6147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223876241 / 1000000000) ≤ -Real.log (4093 / 5120) ∧
    -Real.log (4093 / 5120) ≤ (111938121 / 500000000) := by
  have h := checkLog_sound (w := (1027 / 9213)) (n := 12)
    (lo := (223876241 / 1000000000)) (hi := (111938121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4093) = 1/(4093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111938121 / 500000000) (-223876241 / 1000000000) (Real.log (4093 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1826877 / 10000000) ≤ -Real.log (4096 / 4917) ∧
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


theorem reflection_log_3 : Bounds (1826877 / 10000000) (182687701 / 1000000000) (Real.log (4917 / 4096)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4917 / 4096) = -Real.log (4096 / 4917) := by
    rw [show ((4917 / 4096) : ℝ) = ((4096 / 4917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (111846509 / 500000000) ≤ -Real.log (3275 / 4096) ∧
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


theorem reflection_log_4 : Bounds (-223693019 / 1000000000) (-111846509 / 500000000) (Real.log (3275 / 4096)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16865447 / 50000000) ≤ -Real.log (2560 / 3587) ∧
    -Real.log (2560 / 3587) ≤ (337308941 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 6147)) (n := 12)
    (lo := (16865447 / 50000000)) (hi := (337308941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3587 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3587 / 2560) = 1/(2560 / 3587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16865447 / 50000000) (337308941 / 1000000000) (Real.log (3587 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3587 / 2560) = -Real.log (2560 / 3587) := by
    rw [show ((3587 / 2560) : ℝ) = ((2560 / 3587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (256390329 / 500000000) ≤ -Real.log (1533 / 2560) ∧
    -Real.log (1533 / 2560) ≤ (512780659 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 4093)) (n := 12)
    (lo := (256390329 / 500000000)) (hi := (512780659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1533) = 1/(1533 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-512780659 / 1000000000) (-256390329 / 500000000) (Real.log (1533 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (337099829 / 1000000000) ≤ -Real.log (2048 / 2869) ∧
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


theorem reflection_log_7 : Bounds (337099829 / 1000000000) (33709983 / 100000000) (Real.log (2869 / 2048)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2869 / 2048) = -Real.log (2048 / 2869) := by
    rw [show ((2869 / 2048) : ℝ) = ((2048 / 2869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512291541 / 1000000000) ≤ -Real.log (1227 / 2048) ∧
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


theorem reflection_log_8 : Bounds (-256145771 / 500000000) (-512291541 / 1000000000) (Real.log (1227 / 2048)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (251147747 / 1000000000) ≤ -Real.log (2000 / 2571) ∧
    -Real.log (2000 / 2571) ≤ (62786937 / 250000000) := by
  have h := checkLog_sound (w := (571 / 4571)) (n := 12)
    (lo := (251147747 / 1000000000)) (hi := (62786937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2000) = 1/(2000 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (251147747 / 1000000000) (62786937 / 250000000) (Real.log (2571 / 2000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (2571 / 2000) = -Real.log (2000 / 2571) := by
    rw [show ((2571 / 2000) : ℝ) = ((2000 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (336172281 / 1000000000) ≤ -Real.log (1429 / 2000) ∧
    -Real.log (1429 / 2000) ≤ (168086141 / 500000000) := by
  have h := checkLog_sound (w := (571 / 3429)) (n := 12)
    (lo := (336172281 / 1000000000)) (hi := (168086141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1429) = 1/(1429 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168086141 / 500000000) (-336172281 / 1000000000) (Real.log (1429 / 2000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62828357 / 250000000) ≤ -Real.log (1000000 / 1285713) ∧
    -Real.log (1000000 / 1285713) ≤ (251313429 / 1000000000) := by
  have h := checkLog_sound (w := (285713 / 2285713)) (n := 12)
    (lo := (62828357 / 250000000)) (hi := (251313429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285713 / 1000000) = 1/(1000000 / 1285713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62828357 / 250000000) (251313429 / 1000000000) (Real.log (1285713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285713 / 1000000) = -Real.log (1000000 / 1285713) := by
    rw [show ((1285713 / 1000000) : ℝ) = ((1000000 / 1285713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84117609 / 250000000) ≤ -Real.log (714287 / 1000000) ∧
    -Real.log (714287 / 1000000) ≤ (336470437 / 1000000000) := by
  have h := checkLog_sound (w := (285713 / 1714287)) (n := 12)
    (lo := (84117609 / 250000000)) (hi := (336470437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714287) = 1/(714287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336470437 / 1000000000) (-84117609 / 250000000) (Real.log (714287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (46939397 / 250000000) ≤ -Real.log (1000000 / 1206541) ∧
    -Real.log (1000000 / 1206541) ≤ (187757589 / 1000000000) := by
  have h := checkLog_sound (w := (206541 / 2206541)) (n := 12)
    (lo := (46939397 / 250000000)) (hi := (187757589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206541 / 1000000) = 1/(1000000 / 1206541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (46939397 / 250000000) (187757589 / 1000000000) (Real.log (1206541 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206541 / 1000000) = -Real.log (1000000 / 1206541) := by
    rw [show ((1206541 / 1000000) : ℝ) = ((1000000 / 1206541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23135341 / 100000000) ≤ -Real.log (793459 / 1000000) ∧
    -Real.log (793459 / 1000000) ≤ (231353411 / 1000000000) := by
  have h := checkLog_sound (w := (206541 / 1793459)) (n := 12)
    (lo := (23135341 / 100000000)) (hi := (231353411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793459) = 1/(793459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-231353411 / 1000000000) (-23135341 / 100000000) (Real.log (793459 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (93945509 / 500000000) ≤ -Real.log (500000 / 603351) ∧
    -Real.log (500000 / 603351) ≤ (187891019 / 1000000000) := by
  have h := checkLog_sound (w := (103351 / 1103351)) (n := 12)
    (lo := (93945509 / 500000000)) (hi := (187891019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603351 / 500000) = 1/(500000 / 603351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93945509 / 500000000) (187891019 / 1000000000) (Real.log (603351 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603351 / 500000) = -Real.log (500000 / 603351) := by
    rw [show ((603351 / 500000) : ℝ) = ((500000 / 603351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231556339 / 1000000000) ≤ -Real.log (396649 / 500000) ∧
    -Real.log (396649 / 500000) ≤ (11577817 / 50000000) := by
  have h := checkLog_sound (w := (103351 / 896649)) (n := 12)
    (lo := (231556339 / 1000000000)) (hi := (11577817 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396649) = 1/(396649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-11577817 / 50000000) (-231556339 / 1000000000) (Real.log (396649 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (587320029 / 1000000000) ≤ -Real.log (250000000000 / 449790062981) ∧
    -Real.log (250000000000 / 449790062981) ≤ (58732003 / 100000000) := by
  have h := checkLog_sound (w := (199790062981 / 699790062981)) (n := 12)
    (lo := (587320029 / 1000000000)) (hi := (58732003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449790062981 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449790062981 / 250000000000) = 1/(250000000000 / 449790062981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (587320029 / 1000000000) (58732003 / 100000000) (Real.log (449790062981 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449790062981 / 250000000000) = -Real.log (250000000000 / 449790062981) := by
    rw [show ((449790062981 / 250000000000) : ℝ) = ((250000000000 / 449790062981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73472983 / 125000000) ≤ -Real.log (100000000000 / 179999496001) ∧
    -Real.log (100000000000 / 179999496001) ≤ (117556773 / 200000000) := by
  have h := checkLog_sound (w := (79999496001 / 279999496001)) (n := 12)
    (lo := (73472983 / 125000000)) (hi := (117556773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179999496001 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179999496001 / 100000000000) = 1/(100000000000 / 179999496001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73472983 / 125000000) (117556773 / 200000000) (Real.log (179999496001 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179999496001 / 100000000000) = -Real.log (100000000000 / 179999496001) := by
    rw [show ((179999496001 / 100000000000) : ℝ) = ((100000000000 / 179999496001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (209555499 / 500000000) ≤ -Real.log (500000000000 / 760304565201) ∧
    -Real.log (500000000000 / 760304565201) ≤ (419110999 / 1000000000) := by
  have h := checkLog_sound (w := (260304565201 / 1260304565201)) (n := 12)
    (lo := (209555499 / 500000000)) (hi := (419110999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760304565201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760304565201 / 500000000000) = 1/(500000000000 / 760304565201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (209555499 / 500000000) (419110999 / 1000000000) (Real.log (760304565201 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760304565201 / 500000000000) = -Real.log (500000000000 / 760304565201) := by
    rw [show ((760304565201 / 500000000000) : ℝ) = ((500000000000 / 760304565201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209723679 / 500000000) ≤ -Real.log (100000000000 / 152112068857) ∧
    -Real.log (100000000000 / 152112068857) ≤ (419447359 / 1000000000) := by
  have h := checkLog_sound (w := (52112068857 / 252112068857)) (n := 12)
    (lo := (209723679 / 500000000)) (hi := (419447359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152112068857 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152112068857 / 100000000000) = 1/(100000000000 / 152112068857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209723679 / 500000000) (419447359 / 1000000000) (Real.log (152112068857 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (152112068857 / 100000000000) = -Real.log (100000000000 / 152112068857) := by
    rw [show ((152112068857 / 100000000000) : ℝ) = ((100000000000 / 152112068857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0476
