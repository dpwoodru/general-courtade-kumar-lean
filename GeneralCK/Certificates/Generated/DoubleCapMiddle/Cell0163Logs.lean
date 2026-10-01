import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0163
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

theorem reflection_log_1_neg : (8817163 / 31250000) ≤ -Real.log (5120 / 6789) ∧
    -Real.log (5120 / 6789) ≤ (282149217 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 11909)) (n := 12)
    (lo := (8817163 / 31250000)) (hi := (282149217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6789 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6789 / 5120) = 1/(5120 / 6789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8817163 / 31250000) (282149217 / 1000000000) (Real.log (6789 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6789 / 5120) = -Real.log (5120 / 6789) := by
    rw [show ((6789 / 5120) : ℝ) = ((5120 / 6789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197245197 / 500000000) ≤ -Real.log (3451 / 5120) ∧
    -Real.log (3451 / 5120) ≤ (78898079 / 200000000) := by
  have h := checkLog_sound (w := (1669 / 8571)) (n := 12)
    (lo := (197245197 / 500000000)) (hi := (78898079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3451) = 1/(3451 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78898079 / 200000000) (-197245197 / 500000000) (Real.log (3451 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (281707227 / 1000000000) ≤ -Real.log (2560 / 3393) ∧
    -Real.log (2560 / 3393) ≤ (70426807 / 250000000) := by
  have h := checkLog_sound (w := (833 / 5953)) (n := 12)
    (lo := (281707227 / 1000000000)) (hi := (70426807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3393 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3393 / 2560) = 1/(2560 / 3393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (281707227 / 1000000000) (70426807 / 250000000) (Real.log (3393 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3393 / 2560) = -Real.log (2560 / 3393) := by
    rw [show ((3393 / 2560) : ℝ) = ((2560 / 3393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (393621459 / 1000000000) ≤ -Real.log (1727 / 2560) ∧
    -Real.log (1727 / 2560) ≤ (19681073 / 50000000) := by
  have h := checkLog_sound (w := (833 / 4287)) (n := 12)
    (lo := (393621459 / 1000000000)) (hi := (19681073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1727) = 1/(1727 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-19681073 / 50000000) (-393621459 / 1000000000) (Real.log (1727 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (501958299 / 1000000000) ≤ -Real.log (2560 / 4229) ∧
    -Real.log (2560 / 4229) ≤ (5019583 / 10000000) := by
  have h := checkLog_sound (w := (1669 / 6789)) (n := 12)
    (lo := (501958299 / 1000000000)) (hi := (5019583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4229 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4229 / 2560) = 1/(2560 / 4229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (501958299 / 1000000000) (5019583 / 10000000) (Real.log (4229 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4229 / 2560) = -Real.log (2560 / 4229) := by
    rw [show ((4229 / 2560) : ℝ) = ((2560 / 4229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1055418109 / 1000000000) ≤ -Real.log (891 / 2560) ∧
    -Real.log (891 / 2560) ≤ (1055418111 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 891) = 1/(891 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1055418111 / 1000000000) (-1055418109 / 1000000000) (Real.log (891 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25062433 / 50000000) ≤ -Real.log (1280 / 2113) ∧
    -Real.log (1280 / 2113) ≤ (501248661 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 3393)) (n := 12)
    (lo := (25062433 / 50000000)) (hi := (501248661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2113 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2113 / 1280) = 1/(1280 / 2113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25062433 / 50000000) (501248661 / 1000000000) (Real.log (2113 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2113 / 1280) = -Real.log (1280 / 2113) := by
    rw [show ((2113 / 1280) : ℝ) = ((1280 / 2113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1052056761 / 1000000000) ≤ -Real.log (447 / 1280) ∧
    -Real.log (447 / 1280) ≤ (1052056763 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 447) = 1/(447 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1052056763 / 1000000000) (-1052056761 / 1000000000) (Real.log (447 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4817251 / 12500000) ≤ -Real.log (1000000 / 1470173) ∧
    -Real.log (1000000 / 1470173) ≤ (385380081 / 1000000000) := by
  have h := checkLog_sound (w := (470173 / 2470173)) (n := 12)
    (lo := (4817251 / 12500000)) (hi := (385380081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1470173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1470173 / 1000000) = 1/(1000000 / 1470173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4817251 / 12500000) (385380081 / 1000000000) (Real.log (1470173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1470173 / 1000000) = -Real.log (1000000 / 1470173) := by
    rw [show ((1470173 / 1000000) : ℝ) = ((1000000 / 1470173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31760237 / 50000000) ≤ -Real.log (529827 / 1000000) ∧
    -Real.log (529827 / 1000000) ≤ (635204741 / 1000000000) := by
  have h := checkLog_sound (w := (470173 / 1529827)) (n := 12)
    (lo := (31760237 / 50000000)) (hi := (635204741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 529827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 529827) = 1/(529827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-635204741 / 1000000000) (-31760237 / 50000000) (Real.log (529827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (96496827 / 250000000) ≤ -Real.log (500000 / 735533) ∧
    -Real.log (500000 / 735533) ≤ (385987309 / 1000000000) := by
  have h := checkLog_sound (w := (235533 / 1235533)) (n := 12)
    (lo := (96496827 / 250000000)) (hi := (385987309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735533 / 500000) = 1/(500000 / 735533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (96496827 / 250000000) (385987309 / 1000000000) (Real.log (735533 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735533 / 500000) = -Real.log (500000 / 735533) := by
    rw [show ((735533 / 500000) : ℝ) = ((500000 / 735533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (318445809 / 500000000) ≤ -Real.log (264467 / 500000) ∧
    -Real.log (264467 / 500000) ≤ (636891619 / 1000000000) := by
  have h := checkLog_sound (w := (235533 / 764467)) (n := 12)
    (lo := (318445809 / 500000000)) (hi := (636891619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264467) = 1/(264467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-636891619 / 1000000000) (-318445809 / 500000000) (Real.log (264467 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (18944541 / 62500000) ≤ -Real.log (1000000 / 1354067) ∧
    -Real.log (1000000 / 1354067) ≤ (303112657 / 1000000000) := by
  have h := checkLog_sound (w := (354067 / 2354067)) (n := 12)
    (lo := (18944541 / 62500000)) (hi := (303112657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354067 / 1000000) = 1/(1000000 / 1354067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (18944541 / 62500000) (303112657 / 1000000000) (Real.log (1354067 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1354067 / 1000000) = -Real.log (1000000 / 1354067) := by
    rw [show ((1354067 / 1000000) : ℝ) = ((1000000 / 1354067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (87411899 / 200000000) ≤ -Real.log (645933 / 1000000) ∧
    -Real.log (645933 / 1000000) ≤ (54632437 / 125000000) := by
  have h := checkLog_sound (w := (354067 / 1645933)) (n := 12)
    (lo := (87411899 / 200000000)) (hi := (54632437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645933) = 1/(645933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54632437 / 125000000) (-87411899 / 200000000) (Real.log (645933 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30367377 / 100000000) ≤ -Real.log (1000000 / 1354827) ∧
    -Real.log (1000000 / 1354827) ≤ (303673771 / 1000000000) := by
  have h := checkLog_sound (w := (354827 / 2354827)) (n := 12)
    (lo := (30367377 / 100000000)) (hi := (303673771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1354827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1354827 / 1000000) = 1/(1000000 / 1354827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30367377 / 100000000) (303673771 / 1000000000) (Real.log (1354827 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1354827 / 1000000) = -Real.log (1000000 / 1354827) := by
    rw [show ((1354827 / 1000000) : ℝ) = ((1000000 / 1354827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (438236781 / 1000000000) ≤ -Real.log (645173 / 1000000) ∧
    -Real.log (645173 / 1000000) ≤ (219118391 / 500000000) := by
  have h := checkLog_sound (w := (354827 / 1645173)) (n := 12)
    (lo := (438236781 / 1000000000)) (hi := (219118391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 645173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 645173) = 1/(645173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-219118391 / 500000000) (-438236781 / 1000000000) (Real.log (645173 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1020584821 / 1000000000) ≤ -Real.log (62500000000 / 173426066433) ∧
    -Real.log (62500000000 / 173426066433) ≤ (1020584823 / 1000000000) := by
  have h := checkLog_sound (w := (48426066433 / 298426066433)) (n := 12)
    (lo := (327437641 / 1000000000)) (hi := (163718821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173426066433 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(173426066433 / 125000000000) = 1/(62500000000 / 173426066433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1020584821 / 1000000000) (1020584823 / 1000000000) (Real.log (173426066433 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (173426066433 / 62500000000) = -Real.log (62500000000 / 173426066433) := by
    rw [show ((173426066433 / 62500000000) : ℝ) = ((62500000000 / 173426066433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (511439463 / 500000000) ≤ -Real.log (100000000000 / 278119009177) ∧
    -Real.log (100000000000 / 278119009177) ≤ (63929933 / 62500000) := by
  have h := checkLog_sound (w := (78119009177 / 478119009177)) (n := 12)
    (lo := (164865873 / 500000000)) (hi := (329731747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278119009177 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(278119009177 / 200000000000) = 1/(100000000000 / 278119009177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (511439463 / 500000000) (63929933 / 62500000) (Real.log (278119009177 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (278119009177 / 100000000000) = -Real.log (100000000000 / 278119009177) := by
    rw [show ((278119009177 / 100000000000) : ℝ) = ((100000000000 / 278119009177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (740172151 / 1000000000) ≤ -Real.log (500000000000 / 1048148182551) ∧
    -Real.log (500000000000 / 1048148182551) ≤ (740172153 / 1000000000) := by
  have h := checkLog_sound (w := (48148182551 / 2048148182551)) (n := 12)
    (lo := (47024971 / 1000000000)) (hi := (11756243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1048148182551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1048148182551 / 1000000000000) = 1/(500000000000 / 1048148182551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (740172151 / 1000000000) (740172153 / 1000000000) (Real.log (1048148182551 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1048148182551 / 500000000000) = -Real.log (500000000000 / 1048148182551) := by
    rw [show ((1048148182551 / 500000000000) : ℝ) = ((500000000000 / 1048148182551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (741910551 / 1000000000) ≤ -Real.log (500000000000 / 1049971868011) ∧
    -Real.log (500000000000 / 1049971868011) ≤ (741910553 / 1000000000) := by
  have h := checkLog_sound (w := (49971868011 / 2049971868011)) (n := 12)
    (lo := (48763371 / 1000000000)) (hi := (12190843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049971868011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1049971868011 / 1000000000000) = 1/(500000000000 / 1049971868011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (741910551 / 1000000000) (741910553 / 1000000000) (Real.log (1049971868011 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1049971868011 / 500000000000) = -Real.log (500000000000 / 1049971868011) := by
    rw [show ((1049971868011 / 500000000000) : ℝ) = ((500000000000 / 1049971868011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0163
