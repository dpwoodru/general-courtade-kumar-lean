import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0177
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

theorem reflection_log_1_neg : (315386491 / 500000000) ≤ -Real.log (3200 / 6013) ∧
    -Real.log (3200 / 6013) ≤ (630772983 / 1000000000) := by
  have h := checkLog_sound (w := (2813 / 9213)) (n := 12)
    (lo := (315386491 / 500000000)) (hi := (630772983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013 / 3200) = 1/(3200 / 6013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (315386491 / 500000000) (630772983 / 1000000000) (Real.log (6013 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6013 / 3200) = -Real.log (3200 / 6013) := by
    rw [show ((6013 / 3200) : ℝ) = ((3200 / 6013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1056240697 / 500000000) ≤ -Real.log (387 / 3200) ∧
    -Real.log (387 / 3200) ≤ (1056240699 / 500000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 387) = 1/(387 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1056240699 / 500000000) (-1056240697 / 500000000) (Real.log (387 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (314595911 / 500000000) ≤ -Real.log (6400 / 12007) ∧
    -Real.log (6400 / 12007) ≤ (629191823 / 1000000000) := by
  have h := checkLog_sound (w := (5607 / 18407)) (n := 12)
    (lo := (314595911 / 500000000)) (hi := (629191823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12007 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12007 / 6400) = 1/(6400 / 12007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (314595911 / 500000000) (629191823 / 1000000000) (Real.log (12007 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12007 / 6400) = -Real.log (6400 / 12007) := by
    rw [show ((12007 / 6400) : ℝ) = ((6400 / 12007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1044115023 / 500000000) ≤ -Real.log (793 / 6400) ∧
    -Real.log (793 / 6400) ≤ (41764601 / 20000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 793) = 1/(793 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-41764601 / 20000000) (-1044115023 / 500000000) (Real.log (793 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (5642479 / 10000000) ≤ -Real.log (1600 / 2813) ∧
    -Real.log (1600 / 2813) ≤ (564247901 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 4413)) (n := 12)
    (lo := (5642479 / 10000000)) (hi := (564247901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2813 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2813 / 1600) = 1/(1600 / 2813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (5642479 / 10000000) (564247901 / 1000000000) (Real.log (2813 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2813 / 1600) = -Real.log (1600 / 2813) := by
    rw [show ((2813 / 1600) : ℝ) = ((1600 / 2813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (709667107 / 500000000) ≤ -Real.log (387 / 1600) ∧
    -Real.log (387 / 1600) ≤ (1419334217 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 387) = 1/(387 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1419334217 / 1000000000) (-709667107 / 500000000) (Real.log (387 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (560865007 / 1000000000) ≤ -Real.log (3200 / 5607) ∧
    -Real.log (3200 / 5607) ≤ (35054063 / 62500000) := by
  have h := checkLog_sound (w := (2407 / 8807)) (n := 12)
    (lo := (560865007 / 1000000000)) (hi := (35054063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5607 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5607 / 3200) = 1/(3200 / 5607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (560865007 / 1000000000) (35054063 / 62500000) (Real.log (5607 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5607 / 3200) = -Real.log (3200 / 5607) := by
    rw [show ((5607 / 3200) : ℝ) = ((3200 / 5607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697541433 / 500000000) ≤ -Real.log (793 / 3200) ∧
    -Real.log (793 / 3200) ≤ (1395082869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 793) = 1/(793 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1395082869 / 1000000000) (-697541433 / 500000000) (Real.log (793 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161448633 / 250000000) ≤ -Real.log (500000 / 953751) ∧
    -Real.log (500000 / 953751) ≤ (645794533 / 1000000000) := by
  have h := checkLog_sound (w := (453751 / 1453751)) (n := 12)
    (lo := (161448633 / 250000000)) (hi := (645794533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953751 / 500000) = 1/(500000 / 953751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161448633 / 250000000) (645794533 / 1000000000) (Real.log (953751 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (953751 / 500000) = -Real.log (500000 / 953751) := by
    rw [show ((953751 / 500000) : ℝ) = ((500000 / 953751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1190284127 / 500000000) ≤ -Real.log (46249 / 500000) ∧
    -Real.log (46249 / 500000) ≤ (1190284129 / 500000000) := by
  have h := checkLog_sound (w := (16251 / 108749)) (n := 12)
    (lo := (150563357 / 500000000)) (hi := (60225343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46249) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 46249) = 1/(46249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1190284129 / 500000000) (-1190284127 / 500000000) (Real.log (46249 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16170093 / 25000000) ≤ -Real.log (250000 / 477357) ∧
    -Real.log (250000 / 477357) ≤ (646803721 / 1000000000) := by
  have h := checkLog_sound (w := (227357 / 727357)) (n := 12)
    (lo := (16170093 / 25000000)) (hi := (646803721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477357 / 250000) = 1/(250000 / 477357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16170093 / 25000000) (646803721 / 1000000000) (Real.log (477357 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (477357 / 250000) = -Real.log (250000 / 477357) := by
    rw [show ((477357 / 250000) : ℝ) = ((250000 / 477357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1200805081 / 500000000) ≤ -Real.log (22643 / 250000) ∧
    -Real.log (22643 / 250000) ≤ (1200805083 / 500000000) := by
  have h := checkLog_sound (w := (8607 / 53893)) (n := 12)
    (lo := (161084311 / 500000000)) (hi := (322168623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22643) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 22643) = 1/(22643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1200805083 / 500000000) (-1200805081 / 500000000) (Real.log (22643 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (643741051 / 1000000000) ≤ -Real.log (1000000 / 1903589) ∧
    -Real.log (1000000 / 1903589) ≤ (160935263 / 250000000) := by
  have h := checkLog_sound (w := (903589 / 2903589)) (n := 12)
    (lo := (643741051 / 1000000000)) (hi := (160935263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903589 / 1000000) = 1/(1000000 / 1903589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (643741051 / 1000000000) (160935263 / 250000000) (Real.log (1903589 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1903589 / 1000000) = -Real.log (1000000 / 1903589) := by
    rw [show ((1903589 / 1000000) : ℝ) = ((1000000 / 1903589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1169567487 / 500000000) ≤ -Real.log (96411 / 1000000) ∧
    -Real.log (96411 / 1000000) ≤ (1169567489 / 500000000) := by
  have h := checkLog_sound (w := (28589 / 221411)) (n := 12)
    (lo := (129846717 / 500000000)) (hi := (51938687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96411) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 96411) = 1/(96411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1169567489 / 500000000) (-1169567487 / 500000000) (Real.log (96411 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (322433093 / 500000000) ≤ -Real.log (250000 / 476433) ∧
    -Real.log (250000 / 476433) ≤ (644866187 / 1000000000) := by
  have h := checkLog_sound (w := (226433 / 726433)) (n := 12)
    (lo := (322433093 / 500000000)) (hi := (644866187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476433 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476433 / 250000) = 1/(250000 / 476433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (322433093 / 500000000) (644866187 / 1000000000) (Real.log (476433 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (476433 / 250000) = -Real.log (250000 / 476433) := by
    rw [show ((476433 / 250000) : ℝ) = ((250000 / 476433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2361613487 / 1000000000) ≤ -Real.log (23567 / 250000) ∧
    -Real.log (23567 / 250000) ≤ (2361613491 / 1000000000) := by
  have h := checkLog_sound (w := (7683 / 54817)) (n := 12)
    (lo := (282171947 / 1000000000)) (hi := (70542987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23567) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 23567) = 1/(23567 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2361613491 / 1000000000) (-2361613487 / 1000000000) (Real.log (23567 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1513181393 / 500000000) ≤ -Real.log (800000000 / 16497671301) ∧
    -Real.log (800000000 / 16497671301) ≤ (3026362791 / 1000000000) := by
  have h := checkLog_sound (w := (3697671301 / 29297671301)) (n := 12)
    (lo := (126887033 / 500000000)) (hi := (253774067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16497671301 / 12800000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16497671301 / 12800000000) = 1/(800000000 / 16497671301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1513181393 / 500000000) (3026362791 / 1000000000) (Real.log (16497671301 / 800000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16497671301 / 800000000) = -Real.log (800000000 / 16497671301) := by
    rw [show ((16497671301 / 800000000) : ℝ) = ((800000000 / 16497671301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1524206941 / 500000000) ≤ -Real.log (500000000000 / 10540939804797) ∧
    -Real.log (500000000000 / 10540939804797) ≤ (3048413887 / 1000000000) := by
  have h := checkLog_sound (w := (2540939804797 / 18540939804797)) (n := 12)
    (lo := (137912581 / 500000000)) (hi := (275825163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10540939804797 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10540939804797 / 8000000000000) = 1/(500000000000 / 10540939804797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1524206941 / 500000000) (3048413887 / 1000000000) (Real.log (10540939804797 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10540939804797 / 500000000000) = -Real.log (500000000000 / 10540939804797) := by
    rw [show ((10540939804797 / 500000000000) : ℝ) = ((500000000000 / 10540939804797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (119315041 / 40000000) ≤ -Real.log (250000000000 / 4936130213357) ∧
    -Real.log (250000000000 / 4936130213357) ≤ (298287603 / 100000000) := by
  have h := checkLog_sound (w := (936130213357 / 8936130213357)) (n := 12)
    (lo := (42057461 / 200000000)) (hi := (105143653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4936130213357 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4936130213357 / 4000000000000) = 1/(250000000000 / 4936130213357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (119315041 / 40000000) (298287603 / 100000000) (Real.log (4936130213357 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4936130213357 / 250000000000) = -Real.log (250000000000 / 4936130213357) := by
    rw [show ((4936130213357 / 250000000000) : ℝ) = ((250000000000 / 4936130213357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3006479673 / 1000000000) ≤ -Real.log (6250000000 / 126350670429) ∧
    -Real.log (6250000000 / 126350670429) ≤ (1503239839 / 500000000) := by
  have h := checkLog_sound (w := (26350670429 / 226350670429)) (n := 12)
    (lo := (233890953 / 1000000000)) (hi := (116945477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126350670429 / 100000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(126350670429 / 100000000000) = 1/(6250000000 / 126350670429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3006479673 / 1000000000) (1503239839 / 500000000) (Real.log (126350670429 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (126350670429 / 6250000000) = -Real.log (6250000000 / 126350670429) := by
    rw [show ((126350670429 / 6250000000) : ℝ) = ((6250000000 / 126350670429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0177
