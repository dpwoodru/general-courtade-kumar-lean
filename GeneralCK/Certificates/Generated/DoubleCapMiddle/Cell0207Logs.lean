import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0207
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

theorem reflection_log_1_neg : (262514493 / 1000000000) ≤ -Real.log (5120 / 6657) ∧
    -Real.log (5120 / 6657) ≤ (131257247 / 500000000) := by
  have h := checkLog_sound (w := (1537 / 11777)) (n := 12)
    (lo := (262514493 / 1000000000)) (hi := (131257247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6657 / 5120) = 1/(5120 / 6657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (262514493 / 1000000000) (131257247 / 500000000) (Real.log (6657 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6657 / 5120) = -Real.log (5120 / 6657) := by
    rw [show ((6657 / 5120) : ℝ) = ((5120 / 6657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (178477 / 500000) ≤ -Real.log (3583 / 5120) ∧
    -Real.log (3583 / 5120) ≤ (356954001 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 8703)) (n := 12)
    (lo := (178477 / 500000)) (hi := (356954001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3583) = 1/(3583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-356954001 / 1000000000) (-178477 / 500000) (Real.log (3583 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131031869 / 500000000) ≤ -Real.log (2560 / 3327) ∧
    -Real.log (2560 / 3327) ≤ (262063739 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 5887)) (n := 12)
    (lo := (131031869 / 500000000)) (hi := (262063739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3327 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3327 / 2560) = 1/(2560 / 3327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131031869 / 500000000) (262063739 / 1000000000) (Real.log (3327 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3327 / 2560) = -Real.log (2560 / 3327) := by
    rw [show ((3327 / 2560) : ℝ) = ((2560 / 3327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (356117063 / 1000000000) ≤ -Real.log (1793 / 2560) ∧
    -Real.log (1793 / 2560) ≤ (44514633 / 125000000) := by
  have h := checkLog_sound (w := (767 / 4353)) (n := 12)
    (lo := (356117063 / 1000000000)) (hi := (44514633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1793) = 1/(1793 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-44514633 / 125000000) (-356117063 / 1000000000) (Real.log (1793 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23512387 / 50000000) ≤ -Real.log (2560 / 4097) ∧
    -Real.log (2560 / 4097) ≤ (470247741 / 1000000000) := by
  have h := checkLog_sound (w := (1537 / 6657)) (n := 12)
    (lo := (23512387 / 50000000)) (hi := (470247741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4097 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4097 / 2560) = 1/(2560 / 4097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23512387 / 50000000) (470247741 / 1000000000) (Real.log (4097 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4097 / 2560) = -Real.log (2560 / 4097) := by
    rw [show ((4097 / 2560) : ℝ) = ((2560 / 4097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (91726777 / 100000000) ≤ -Real.log (1023 / 2560) ∧
    -Real.log (1023 / 2560) ≤ (229316943 / 250000000) := by
  have h := checkLog_sound (w := (257 / 2303)) (n := 12)
    (lo := (22412059 / 100000000)) (hi := (224120591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1023) = 1/(1023 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229316943 / 250000000) (-91726777 / 100000000) (Real.log (1023 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (117378807 / 250000000) ≤ -Real.log (1280 / 2047) ∧
    -Real.log (1280 / 2047) ≤ (469515229 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 3327)) (n := 12)
    (lo := (117378807 / 250000000)) (hi := (469515229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2047 / 1280) = 1/(1280 / 2047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (117378807 / 250000000) (469515229 / 1000000000) (Real.log (2047 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2047 / 1280) = -Real.log (1280 / 2047) := by
    rw [show ((2047 / 1280) : ℝ) = ((1280 / 2047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (914339511 / 1000000000) ≤ -Real.log (513 / 1280) ∧
    -Real.log (513 / 1280) ≤ (914339513 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 1153)) (n := 12)
    (lo := (221192331 / 1000000000)) (hi := (55298083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 513) = 1/(513 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-914339513 / 1000000000) (-914339511 / 1000000000) (Real.log (513 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (358537009 / 1000000000) ≤ -Real.log (500000 / 715617) ∧
    -Real.log (500000 / 715617) ≤ (35853701 / 100000000) := by
  have h := checkLog_sound (w := (215617 / 1215617)) (n := 12)
    (lo := (358537009 / 1000000000)) (hi := (35853701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715617 / 500000) = 1/(500000 / 715617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (358537009 / 1000000000) (35853701 / 100000000) (Real.log (715617 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (715617 / 500000) = -Real.log (500000 / 715617) := by
    rw [show ((715617 / 500000) : ℝ) = ((500000 / 715617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (564286177 / 1000000000) ≤ -Real.log (284383 / 500000) ∧
    -Real.log (284383 / 500000) ≤ (282143089 / 500000000) := by
  have h := checkLog_sound (w := (215617 / 784383)) (n := 12)
    (lo := (564286177 / 1000000000)) (hi := (282143089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 284383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 284383) = 1/(284383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-282143089 / 500000000) (-564286177 / 1000000000) (Real.log (284383 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2805867 / 7812500) ≤ -Real.log (1000000 / 1432113) ∧
    -Real.log (1000000 / 1432113) ≤ (359150977 / 1000000000) := by
  have h := checkLog_sound (w := (432113 / 2432113)) (n := 12)
    (lo := (2805867 / 7812500)) (hi := (359150977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432113 / 1000000) = 1/(1000000 / 1432113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2805867 / 7812500) (359150977 / 1000000000) (Real.log (1432113 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1432113 / 1000000) = -Real.log (1000000 / 1432113) := by
    rw [show ((1432113 / 1000000) : ℝ) = ((1000000 / 1432113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (565832823 / 1000000000) ≤ -Real.log (567887 / 1000000) ∧
    -Real.log (567887 / 1000000) ≤ (70729103 / 125000000) := by
  have h := checkLog_sound (w := (432113 / 1567887)) (n := 12)
    (lo := (565832823 / 1000000000)) (hi := (70729103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567887) = 1/(567887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-70729103 / 125000000) (-565832823 / 1000000000) (Real.log (567887 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (278724321 / 1000000000) ≤ -Real.log (1000000 / 1321443) ∧
    -Real.log (1000000 / 1321443) ≤ (139362161 / 500000000) := by
  have h := checkLog_sound (w := (321443 / 2321443)) (n := 12)
    (lo := (278724321 / 1000000000)) (hi := (139362161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321443 / 1000000) = 1/(1000000 / 1321443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (278724321 / 1000000000) (139362161 / 500000000) (Real.log (1321443 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1321443 / 1000000) = -Real.log (1000000 / 1321443) := by
    rw [show ((1321443 / 1000000) : ℝ) = ((1000000 / 1321443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (193893397 / 500000000) ≤ -Real.log (678557 / 1000000) ∧
    -Real.log (678557 / 1000000) ≤ (77557359 / 200000000) := by
  have h := checkLog_sound (w := (321443 / 1678557)) (n := 12)
    (lo := (193893397 / 500000000)) (hi := (77557359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678557) = 1/(678557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77557359 / 200000000) (-193893397 / 500000000) (Real.log (678557 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (139637163 / 500000000) ≤ -Real.log (100000 / 132217) ∧
    -Real.log (100000 / 132217) ≤ (279274327 / 1000000000) := by
  have h := checkLog_sound (w := (32217 / 232217)) (n := 12)
    (lo := (139637163 / 500000000)) (hi := (279274327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132217 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132217 / 100000) = 1/(100000 / 132217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (139637163 / 500000000) (279274327 / 1000000000) (Real.log (132217 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (132217 / 100000) = -Real.log (100000 / 132217) := by
    rw [show ((132217 / 100000) : ℝ) = ((100000 / 132217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (388858759 / 1000000000) ≤ -Real.log (67783 / 100000) ∧
    -Real.log (67783 / 100000) ≤ (9721469 / 25000000) := by
  have h := checkLog_sound (w := (32217 / 167783)) (n := 12)
    (lo := (388858759 / 1000000000)) (hi := (9721469 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67783) = 1/(67783 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9721469 / 25000000) (-388858759 / 1000000000) (Real.log (67783 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (184564637 / 200000000) ≤ -Real.log (500000000000 / 1258192297007) ∧
    -Real.log (500000000000 / 1258192297007) ≤ (922823187 / 1000000000) := by
  have h := checkLog_sound (w := (258192297007 / 2258192297007)) (n := 12)
    (lo := (45935201 / 200000000)) (hi := (114838003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258192297007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1258192297007 / 1000000000000) = 1/(500000000000 / 1258192297007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (184564637 / 200000000) (922823187 / 1000000000) (Real.log (1258192297007 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1258192297007 / 500000000000) = -Real.log (500000000000 / 1258192297007) := by
    rw [show ((1258192297007 / 500000000000) : ℝ) = ((500000000000 / 1258192297007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (924983799 / 1000000000) ≤ -Real.log (500000000000 / 1260913702903) ∧
    -Real.log (500000000000 / 1260913702903) ≤ (924983801 / 1000000000) := by
  have h := checkLog_sound (w := (260913702903 / 2260913702903)) (n := 12)
    (lo := (231836619 / 1000000000)) (hi := (11591831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260913702903 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1260913702903 / 1000000000000) = 1/(500000000000 / 1260913702903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (924983799 / 1000000000) (924983801 / 1000000000) (Real.log (1260913702903 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1260913702903 / 500000000000) = -Real.log (500000000000 / 1260913702903) := by
    rw [show ((1260913702903 / 500000000000) : ℝ) = ((500000000000 / 1260913702903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (133302223 / 200000000) ≤ -Real.log (125000000000 / 243428886593) ∧
    -Real.log (125000000000 / 243428886593) ≤ (166627779 / 250000000) := by
  have h := checkLog_sound (w := (118428886593 / 368428886593)) (n := 12)
    (lo := (133302223 / 200000000)) (hi := (166627779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243428886593 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243428886593 / 125000000000) = 1/(125000000000 / 243428886593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (133302223 / 200000000) (166627779 / 250000000) (Real.log (243428886593 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (243428886593 / 125000000000) = -Real.log (125000000000 / 243428886593) := by
    rw [show ((243428886593 / 125000000000) : ℝ) = ((125000000000 / 243428886593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (334066543 / 500000000) ≤ -Real.log (250000000000 / 487648082853) ∧
    -Real.log (250000000000 / 487648082853) ≤ (668133087 / 1000000000) := by
  have h := checkLog_sound (w := (237648082853 / 737648082853)) (n := 12)
    (lo := (334066543 / 500000000)) (hi := (668133087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487648082853 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487648082853 / 250000000000) = 1/(250000000000 / 487648082853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (334066543 / 500000000) (668133087 / 1000000000) (Real.log (487648082853 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (487648082853 / 250000000000) = -Real.log (250000000000 / 487648082853) := by
    rw [show ((487648082853 / 250000000000) : ℝ) = ((250000000000 / 487648082853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0207
