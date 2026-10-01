import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0245
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

theorem reflection_log_1_neg : (30655167 / 125000000) ≤ -Real.log (5120 / 6543) ∧
    -Real.log (5120 / 6543) ≤ (245241337 / 1000000000) := by
  have h := checkLog_sound (w := (1423 / 11663)) (n := 12)
    (lo := (30655167 / 125000000)) (hi := (245241337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6543 / 5120) = 1/(5120 / 6543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (30655167 / 125000000) (245241337 / 1000000000) (Real.log (6543 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6543 / 5120) = -Real.log (5120 / 6543) := by
    rw [show ((6543 / 5120) : ℝ) = ((5120 / 6543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (325632759 / 1000000000) ≤ -Real.log (3697 / 5120) ∧
    -Real.log (3697 / 5120) ≤ (8140819 / 25000000) := by
  have h := checkLog_sound (w := (1423 / 8817)) (n := 12)
    (lo := (325632759 / 1000000000)) (hi := (8140819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3697) = 1/(3697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8140819 / 25000000) (-325632759 / 1000000000) (Real.log (3697 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (122391363 / 500000000) ≤ -Real.log (256 / 327) ∧
    -Real.log (256 / 327) ≤ (244782727 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 583)) (n := 12)
    (lo := (122391363 / 500000000)) (hi := (244782727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 256) = 1/(256 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (122391363 / 500000000) (244782727 / 1000000000) (Real.log (327 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (327 / 256) = -Real.log (256 / 327) := by
    rw [show ((327 / 256) : ℝ) = ((256 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (324821619 / 1000000000) ≤ -Real.log (185 / 256) ∧
    -Real.log (185 / 256) ≤ (16241081 / 50000000) := by
  have h := checkLog_sound (w := (71 / 441)) (n := 12)
    (lo := (324821619 / 1000000000)) (hi := (16241081 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 185) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 185) = 1/(185 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16241081 / 50000000) (-324821619 / 1000000000) (Real.log (185 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88405609 / 200000000) ≤ -Real.log (2560 / 3983) ∧
    -Real.log (2560 / 3983) ≤ (221014023 / 500000000) := by
  have h := checkLog_sound (w := (1423 / 6543)) (n := 12)
    (lo := (88405609 / 200000000)) (hi := (221014023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3983 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3983 / 2560) = 1/(2560 / 3983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88405609 / 200000000) (221014023 / 500000000) (Real.log (3983 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3983 / 2560) = -Real.log (2560 / 3983) := by
    rw [show ((3983 / 2560) : ℝ) = ((2560 / 3983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (811614043 / 1000000000) ≤ -Real.log (1137 / 2560) ∧
    -Real.log (1137 / 2560) ≤ (162322809 / 200000000) := by
  have h := checkLog_sound (w := (143 / 2417)) (n := 12)
    (lo := (118466863 / 1000000000)) (hi := (7404179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1137) = 1/(1137 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-162322809 / 200000000) (-811614043 / 1000000000) (Real.log (1137 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1378983 / 3125000) ≤ -Real.log (128 / 199) ∧
    -Real.log (128 / 199) ≤ (441274561 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 128) = 1/(128 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1378983 / 3125000) (441274561 / 1000000000) (Real.log (199 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (199 / 128) = -Real.log (128 / 199) := by
    rw [show ((199 / 128) : ℝ) = ((128 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (161795799 / 200000000) ≤ -Real.log (57 / 128) ∧
    -Real.log (57 / 128) ≤ (808978997 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 57) = 1/(57 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-808978997 / 1000000000) (-161795799 / 200000000) (Real.log (57 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167530263 / 500000000) ≤ -Real.log (40000 / 55921) ∧
    -Real.log (40000 / 55921) ≤ (335060527 / 1000000000) := by
  have h := checkLog_sound (w := (15921 / 95921)) (n := 12)
    (lo := (167530263 / 500000000)) (hi := (335060527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55921 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55921 / 40000) = 1/(40000 / 55921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167530263 / 500000000) (335060527 / 1000000000) (Real.log (55921 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55921 / 40000) = -Real.log (40000 / 55921) := by
    rw [show ((55921 / 40000) : ℝ) = ((40000 / 55921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (253769681 / 500000000) ≤ -Real.log (24079 / 40000) ∧
    -Real.log (24079 / 40000) ≤ (507539363 / 1000000000) := by
  have h := checkLog_sound (w := (15921 / 64079)) (n := 12)
    (lo := (253769681 / 500000000)) (hi := (507539363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24079) = 1/(24079 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-507539363 / 1000000000) (-253769681 / 500000000) (Real.log (24079 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167841677 / 500000000) ≤ -Real.log (62500 / 87431) ∧
    -Real.log (62500 / 87431) ≤ (67136671 / 200000000) := by
  have h := checkLog_sound (w := (24931 / 149931)) (n := 12)
    (lo := (167841677 / 500000000)) (hi := (67136671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87431 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87431 / 62500) = 1/(62500 / 87431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167841677 / 500000000) (67136671 / 200000000) (Real.log (87431 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (87431 / 62500) = -Real.log (62500 / 87431) := by
    rw [show ((87431 / 62500) : ℝ) = ((62500 / 87431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (254493657 / 500000000) ≤ -Real.log (37569 / 62500) ∧
    -Real.log (37569 / 62500) ≤ (101797463 / 200000000) := by
  have h := checkLog_sound (w := (24931 / 100069)) (n := 12)
    (lo := (254493657 / 500000000)) (hi := (101797463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 37569) = 1/(37569 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-101797463 / 200000000) (-254493657 / 500000000) (Real.log (37569 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257999367 / 1000000000) ≤ -Real.log (500000 / 647169) ∧
    -Real.log (500000 / 647169) ≤ (32249921 / 125000000) := by
  have h := checkLog_sound (w := (147169 / 1147169)) (n := 12)
    (lo := (257999367 / 1000000000)) (hi := (32249921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647169 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647169 / 500000) = 1/(500000 / 647169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257999367 / 1000000000) (32249921 / 125000000) (Real.log (647169 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (647169 / 500000) = -Real.log (500000 / 647169) := by
    rw [show ((647169 / 500000) : ℝ) = ((500000 / 647169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (348618909 / 1000000000) ≤ -Real.log (352831 / 500000) ∧
    -Real.log (352831 / 500000) ≤ (34861891 / 100000000) := by
  have h := checkLog_sound (w := (147169 / 852831)) (n := 12)
    (lo := (348618909 / 1000000000)) (hi := (34861891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352831) = 1/(352831 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-34861891 / 100000000) (-348618909 / 1000000000) (Real.log (352831 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (129271177 / 500000000) ≤ -Real.log (1000000 / 1295041) ∧
    -Real.log (1000000 / 1295041) ≤ (51708471 / 200000000) := by
  have h := checkLog_sound (w := (295041 / 2295041)) (n := 12)
    (lo := (129271177 / 500000000)) (hi := (51708471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295041 / 1000000) = 1/(1000000 / 1295041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (129271177 / 500000000) (51708471 / 200000000) (Real.log (1295041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1295041 / 1000000) = -Real.log (1000000 / 1295041) := by
    rw [show ((1295041 / 1000000) : ℝ) = ((1000000 / 1295041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (349615633 / 1000000000) ≤ -Real.log (704959 / 1000000) ∧
    -Real.log (704959 / 1000000) ≤ (174807817 / 500000000) := by
  have h := checkLog_sound (w := (295041 / 1704959)) (n := 12)
    (lo := (349615633 / 1000000000)) (hi := (174807817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704959) = 1/(704959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-174807817 / 500000000) (-349615633 / 1000000000) (Real.log (704959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (52662493 / 62500000) ≤ -Real.log (500000000000 / 1161198554757) ∧
    -Real.log (500000000000 / 1161198554757) ≤ (84259989 / 100000000) := by
  have h := checkLog_sound (w := (161198554757 / 2161198554757)) (n := 12)
    (lo := (37363177 / 250000000)) (hi := (149452709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161198554757 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161198554757 / 1000000000000) = 1/(500000000000 / 1161198554757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (52662493 / 62500000) (84259989 / 100000000) (Real.log (1161198554757 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1161198554757 / 500000000000) = -Real.log (500000000000 / 1161198554757) := by
    rw [show ((1161198554757 / 500000000000) : ℝ) = ((500000000000 / 1161198554757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (211167667 / 250000000) ≤ -Real.log (31250000000 / 72725352019) ∧
    -Real.log (31250000000 / 72725352019) ≤ (84467067 / 100000000) := by
  have h := checkLog_sound (w := (10225352019 / 135225352019)) (n := 12)
    (lo := (4735109 / 31250000)) (hi := (151523489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72725352019 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72725352019 / 62500000000) = 1/(31250000000 / 72725352019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (211167667 / 250000000) (84467067 / 100000000) (Real.log (72725352019 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (72725352019 / 31250000000) = -Real.log (31250000000 / 72725352019) := by
    rw [show ((72725352019 / 31250000000) : ℝ) = ((31250000000 / 72725352019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (606618277 / 1000000000) ≤ -Real.log (62500000000 / 114638630109) ∧
    -Real.log (62500000000 / 114638630109) ≤ (303309139 / 500000000) := by
  have h := checkLog_sound (w := (52138630109 / 177138630109)) (n := 12)
    (lo := (606618277 / 1000000000)) (hi := (303309139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114638630109 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114638630109 / 62500000000) = 1/(62500000000 / 114638630109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (606618277 / 1000000000) (303309139 / 500000000) (Real.log (114638630109 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (114638630109 / 62500000000) = -Real.log (62500000000 / 114638630109) := by
    rw [show ((114638630109 / 62500000000) : ℝ) = ((62500000000 / 114638630109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (152039497 / 250000000) ≤ -Real.log (500000000000 / 918522211931) ∧
    -Real.log (500000000000 / 918522211931) ≤ (608157989 / 1000000000) := by
  have h := checkLog_sound (w := (418522211931 / 1418522211931)) (n := 12)
    (lo := (152039497 / 250000000)) (hi := (608157989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918522211931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918522211931 / 500000000000) = 1/(500000000000 / 918522211931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (152039497 / 250000000) (608157989 / 1000000000) (Real.log (918522211931 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (918522211931 / 500000000000) = -Real.log (500000000000 / 918522211931) := by
    rw [show ((918522211931 / 500000000000) : ℝ) = ((500000000000 / 918522211931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0245
