import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell160
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

theorem reflection_log_1_neg : (73975041 / 250000000) ≤ -Real.log (5120 / 6883) ∧
    -Real.log (5120 / 6883) ≤ (59180033 / 200000000) := by
  have h := checkLog_sound (w := (1763 / 12003)) (n := 12)
    (lo := (73975041 / 250000000)) (hi := (59180033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6883 / 5120) = 1/(5120 / 6883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73975041 / 250000000) (59180033 / 200000000) (Real.log (6883 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6883 / 5120) = -Real.log (5120 / 6883) := by
    rw [show ((6883 / 5120) : ℝ) = ((5120 / 6883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (422106721 / 1000000000) ≤ -Real.log (3357 / 5120) ∧
    -Real.log (3357 / 5120) ≤ (211053361 / 500000000) := by
  have h := checkLog_sound (w := (1763 / 8477)) (n := 12)
    (lo := (422106721 / 1000000000)) (hi := (211053361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3357) = 1/(3357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-211053361 / 500000000) (-422106721 / 1000000000) (Real.log (3357 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73866053 / 250000000) ≤ -Real.log (32 / 43) ∧
    -Real.log (32 / 43) ≤ (295464213 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 75)) (n := 12)
    (lo := (73866053 / 250000000)) (hi := (295464213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 32) = 1/(32 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73866053 / 250000000) (295464213 / 1000000000) (Real.log (43 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (43 / 32) = -Real.log (32 / 43) := by
    rw [show ((43 / 32) : ℝ) = ((32 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84242693 / 200000000) ≤ -Real.log (21 / 32) ∧
    -Real.log (21 / 32) ≤ (210606733 / 500000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 21) = 1/(21 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-210606733 / 500000000) (-84242693 / 200000000) (Real.log (21 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (218594821 / 1000000000) ≤ -Real.log (1000000 / 1244327) ∧
    -Real.log (1000000 / 1244327) ≤ (109297411 / 500000000) := by
  have h := checkLog_sound (w := (244327 / 2244327)) (n := 12)
    (lo := (218594821 / 1000000000)) (hi := (109297411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244327 / 1000000) = 1/(1000000 / 1244327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (218594821 / 1000000000) (109297411 / 500000000) (Real.log (1244327 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1244327 / 1000000) = -Real.log (1000000 / 1244327) := by
    rw [show ((1244327 / 1000000) : ℝ) = ((1000000 / 1244327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35018317 / 125000000) ≤ -Real.log (755673 / 1000000) ∧
    -Real.log (755673 / 1000000) ≤ (280146537 / 1000000000) := by
  have h := checkLog_sound (w := (244327 / 1755673)) (n := 12)
    (lo := (35018317 / 125000000)) (hi := (280146537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755673) = 1/(755673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280146537 / 1000000000) (-35018317 / 125000000) (Real.log (755673 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (218933903 / 1000000000) ≤ -Real.log (1000000 / 1244749) ∧
    -Real.log (1000000 / 1244749) ≤ (13683369 / 62500000) := by
  have h := checkLog_sound (w := (244749 / 2244749)) (n := 12)
    (lo := (218933903 / 1000000000)) (hi := (13683369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244749 / 1000000) = 1/(1000000 / 1244749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (218933903 / 1000000000) (13683369 / 62500000) (Real.log (1244749 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1244749 / 1000000) = -Real.log (1000000 / 1244749) := by
    rw [show ((1244749 / 1000000) : ℝ) = ((1000000 / 1244749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (140352567 / 500000000) ≤ -Real.log (755251 / 1000000) ∧
    -Real.log (755251 / 1000000) ≤ (56141027 / 200000000) := by
  have h := checkLog_sound (w := (244749 / 1755251)) (n := 12)
    (lo := (140352567 / 500000000)) (hi := (56141027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755251) = 1/(755251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56141027 / 200000000) (-140352567 / 500000000) (Real.log (755251 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161838197 / 1000000000) ≤ -Real.log (100000 / 117567) ∧
    -Real.log (100000 / 117567) ≤ (80919099 / 500000000) := by
  have h := checkLog_sound (w := (17567 / 217567)) (n := 12)
    (lo := (161838197 / 1000000000)) (hi := (80919099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117567 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117567 / 100000) = 1/(100000 / 117567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161838197 / 1000000000) (80919099 / 500000000) (Real.log (117567 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117567 / 100000) = -Real.log (100000 / 117567) := by
    rw [show ((117567 / 100000) : ℝ) = ((100000 / 117567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193184343 / 1000000000) ≤ -Real.log (82433 / 100000) ∧
    -Real.log (82433 / 100000) ≤ (24148043 / 125000000) := by
  have h := checkLog_sound (w := (17567 / 182433)) (n := 12)
    (lo := (193184343 / 1000000000)) (hi := (24148043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82433) = 1/(82433 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24148043 / 125000000) (-193184343 / 1000000000) (Real.log (82433 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162105243 / 1000000000) ≤ -Real.log (62500 / 73499) ∧
    -Real.log (62500 / 73499) ≤ (40526311 / 250000000) := by
  have h := checkLog_sound (w := (10999 / 135999)) (n := 12)
    (lo := (162105243 / 1000000000)) (hi := (40526311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73499 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73499 / 62500) = 1/(62500 / 73499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162105243 / 1000000000) (40526311 / 250000000) (Real.log (73499 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (73499 / 62500) = -Real.log (62500 / 73499) := by
    rw [show ((73499 / 62500) : ℝ) = ((62500 / 73499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (193565331 / 1000000000) ≤ -Real.log (51501 / 62500) ∧
    -Real.log (51501 / 62500) ≤ (48391333 / 250000000) := by
  have h := checkLog_sound (w := (10999 / 114001)) (n := 12)
    (lo := (193565331 / 1000000000)) (hi := (48391333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51501) = 1/(51501 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48391333 / 250000000) (-193565331 / 1000000000) (Real.log (51501 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (716677677 / 1000000000) ≤ -Real.log (500000000000 / 1023809523809) ∧
    -Real.log (500000000000 / 1023809523809) ≤ (716677679 / 1000000000) := by
  have h := checkLog_sound (w := (23809523809 / 2023809523809)) (n := 12)
    (lo := (23530497 / 1000000000)) (hi := (11765249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023809523809 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023809523809 / 1000000000000) = 1/(500000000000 / 1023809523809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (716677677 / 1000000000) (716677679 / 1000000000) (Real.log (1023809523809 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1023809523809 / 500000000000) = -Real.log (500000000000 / 1023809523809) := by
    rw [show ((1023809523809 / 500000000000) : ℝ) = ((500000000000 / 1023809523809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (179501721 / 250000000) ≤ -Real.log (100000000000 / 205034256777) ∧
    -Real.log (100000000000 / 205034256777) ≤ (359003443 / 500000000) := by
  have h := checkLog_sound (w := (5034256777 / 405034256777)) (n := 12)
    (lo := (3107463 / 125000000)) (hi := (4971941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205034256777 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(205034256777 / 200000000000) = 1/(100000000000 / 205034256777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (179501721 / 250000000) (359003443 / 500000000) (Real.log (205034256777 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (205034256777 / 100000000000) = -Real.log (100000000000 / 205034256777) := by
    rw [show ((205034256777 / 100000000000) : ℝ) = ((100000000000 / 205034256777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (498741357 / 1000000000) ≤ -Real.log (500000000000 / 823323712769) ∧
    -Real.log (500000000000 / 823323712769) ≤ (249370679 / 500000000) := by
  have h := checkLog_sound (w := (323323712769 / 1323323712769)) (n := 12)
    (lo := (498741357 / 1000000000)) (hi := (249370679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823323712769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823323712769 / 500000000000) = 1/(500000000000 / 823323712769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (498741357 / 1000000000) (249370679 / 500000000) (Real.log (823323712769 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (823323712769 / 500000000000) = -Real.log (500000000000 / 823323712769) := by
    rw [show ((823323712769 / 500000000000) : ℝ) = ((500000000000 / 823323712769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (499639037 / 1000000000) ≤ -Real.log (250000000000 / 412031563017) ∧
    -Real.log (250000000000 / 412031563017) ≤ (249819519 / 500000000) := by
  have h := checkLog_sound (w := (162031563017 / 662031563017)) (n := 12)
    (lo := (499639037 / 1000000000)) (hi := (249819519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412031563017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412031563017 / 250000000000) = 1/(250000000000 / 412031563017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (499639037 / 1000000000) (249819519 / 500000000) (Real.log (412031563017 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (412031563017 / 250000000000) = -Real.log (250000000000 / 412031563017) := by
    rw [show ((412031563017 / 250000000000) : ℝ) = ((250000000000 / 412031563017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (355022541 / 1000000000) ≤ -Real.log (250000000000 / 356553200781) ∧
    -Real.log (250000000000 / 356553200781) ≤ (177511271 / 500000000) := by
  have h := checkLog_sound (w := (106553200781 / 606553200781)) (n := 12)
    (lo := (355022541 / 1000000000)) (hi := (177511271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356553200781 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356553200781 / 250000000000) = 1/(250000000000 / 356553200781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355022541 / 1000000000) (177511271 / 500000000) (Real.log (356553200781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356553200781 / 250000000000) = -Real.log (250000000000 / 356553200781) := by
    rw [show ((356553200781 / 250000000000) : ℝ) = ((250000000000 / 356553200781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14226823 / 40000000) ≤ -Real.log (50000000000 / 71356866857) ∧
    -Real.log (50000000000 / 71356866857) ≤ (22229411 / 62500000) := by
  have h := checkLog_sound (w := (21356866857 / 121356866857)) (n := 12)
    (lo := (14226823 / 40000000)) (hi := (22229411 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71356866857 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71356866857 / 50000000000) = 1/(50000000000 / 71356866857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14226823 / 40000000) (22229411 / 62500000) (Real.log (71356866857 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (71356866857 / 50000000000) = -Real.log (50000000000 / 71356866857) := by
    rw [show ((71356866857 / 50000000000) : ℝ) = ((50000000000 / 71356866857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31460087 / 1000000000) ≤ -Real.log (3785271999 / 3906250000) ∧
    -Real.log (3785271999 / 3906250000) ≤ (3932511 / 125000000) := by
  have h := checkLog_sound (w := (120978001 / 7691521999)) (n := 12)
    (lo := (31460087 / 1000000000)) (hi := (3932511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3785271999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3785271999) = 1/(3785271999 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3932511 / 125000000) (-31460087 / 1000000000) (Real.log (3785271999 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6269229 / 200000000) ≤ -Real.log (9691400511 / 10000000000) ∧
    -Real.log (9691400511 / 10000000000) ≤ (15673073 / 500000000) := by
  have h := checkLog_sound (w := (308599489 / 19691400511)) (n := 12)
    (lo := (6269229 / 200000000)) (hi := (15673073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9691400511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9691400511) = 1/(9691400511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15673073 / 500000000) (-6269229 / 200000000) (Real.log (9691400511 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell160
