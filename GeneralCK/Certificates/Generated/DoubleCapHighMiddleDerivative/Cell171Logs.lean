import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell171
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

theorem reflection_log_1_neg : (37585391 / 125000000) ≤ -Real.log (1280 / 1729) ∧
    -Real.log (1280 / 1729) ≤ (300683129 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3009)) (n := 12)
    (lo := (37585391 / 125000000)) (hi := (300683129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1729 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1729 / 1280) = 1/(1280 / 1729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37585391 / 125000000) (300683129 / 1000000000) (Real.log (1729 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1729 / 1280) = -Real.log (1280 / 1729) := by
    rw [show ((1729 / 1280) : ℝ) = ((1280 / 1729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (215992781 / 500000000) ≤ -Real.log (831 / 1280) ∧
    -Real.log (831 / 1280) ≤ (431985563 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 2111)) (n := 12)
    (lo := (215992781 / 500000000)) (hi := (431985563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 831) = 1/(831 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-431985563 / 1000000000) (-215992781 / 500000000) (Real.log (831 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300249257 / 1000000000) ≤ -Real.log (5120 / 6913) ∧
    -Real.log (5120 / 6913) ≤ (150124629 / 500000000) := by
  have h := checkLog_sound (w := (1793 / 12033)) (n := 12)
    (lo := (300249257 / 1000000000)) (hi := (150124629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6913 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6913 / 5120) = 1/(5120 / 6913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300249257 / 1000000000) (150124629 / 500000000) (Real.log (6913 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6913 / 5120) = -Real.log (5120 / 6913) := by
    rw [show ((6913 / 5120) : ℝ) = ((5120 / 6913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (215541721 / 500000000) ≤ -Real.log (3327 / 5120) ∧
    -Real.log (3327 / 5120) ≤ (431083443 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 8447)) (n := 12)
    (lo := (215541721 / 500000000)) (hi := (431083443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3327) = 1/(3327 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-431083443 / 1000000000) (-215541721 / 500000000) (Real.log (3327 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (222309603 / 1000000000) ≤ -Real.log (500000 / 624479) ∧
    -Real.log (500000 / 624479) ≤ (55577401 / 250000000) := by
  have h := checkLog_sound (w := (124479 / 1124479)) (n := 12)
    (lo := (222309603 / 1000000000)) (hi := (55577401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624479 / 500000) = 1/(500000 / 624479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (222309603 / 1000000000) (55577401 / 250000000) (Real.log (624479 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624479 / 500000) = -Real.log (500000 / 624479) := by
    rw [show ((624479 / 500000) : ℝ) = ((500000 / 624479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286293703 / 1000000000) ≤ -Real.log (375521 / 500000) ∧
    -Real.log (375521 / 500000) ≤ (35786713 / 125000000) := by
  have h := checkLog_sound (w := (124479 / 875521)) (n := 12)
    (lo := (286293703 / 1000000000)) (hi := (35786713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375521) = 1/(375521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-35786713 / 125000000) (-286293703 / 1000000000) (Real.log (375521 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (222649029 / 1000000000) ≤ -Real.log (500000 / 624691) ∧
    -Real.log (500000 / 624691) ≤ (22264903 / 100000000) := by
  have h := checkLog_sound (w := (124691 / 1124691)) (n := 12)
    (lo := (222649029 / 1000000000)) (hi := (22264903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624691 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624691 / 500000) = 1/(500000 / 624691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (222649029 / 1000000000) (22264903 / 100000000) (Real.log (624691 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (624691 / 500000) = -Real.log (500000 / 624691) := by
    rw [show ((624691 / 500000) : ℝ) = ((500000 / 624691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (286858411 / 1000000000) ≤ -Real.log (375309 / 500000) ∧
    -Real.log (375309 / 500000) ≤ (71714603 / 250000000) := by
  have h := checkLog_sound (w := (124691 / 875309)) (n := 12)
    (lo := (286858411 / 1000000000)) (hi := (71714603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375309) = 1/(375309 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71714603 / 250000000) (-286858411 / 1000000000) (Real.log (375309 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32953001 / 200000000) ≤ -Real.log (250000 / 294779) ∧
    -Real.log (250000 / 294779) ≤ (82382503 / 500000000) := by
  have h := checkLog_sound (w := (44779 / 544779)) (n := 12)
    (lo := (32953001 / 200000000)) (hi := (82382503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294779 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294779 / 250000) = 1/(250000 / 294779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32953001 / 200000000) (82382503 / 500000000) (Real.log (294779 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (294779 / 250000) = -Real.log (250000 / 294779) := by
    rw [show ((294779 / 250000) : ℝ) = ((250000 / 294779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19737347 / 100000000) ≤ -Real.log (205221 / 250000) ∧
    -Real.log (205221 / 250000) ≤ (197373471 / 1000000000) := by
  have h := checkLog_sound (w := (44779 / 455221)) (n := 12)
    (lo := (19737347 / 100000000)) (hi := (197373471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205221) = 1/(205221 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197373471 / 1000000000) (-19737347 / 100000000) (Real.log (205221 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (82516059 / 500000000) ≤ -Real.log (1000000 / 1179431) ∧
    -Real.log (1000000 / 1179431) ≤ (165032119 / 1000000000) := by
  have h := checkLog_sound (w := (179431 / 2179431)) (n := 12)
    (lo := (82516059 / 500000000)) (hi := (165032119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179431 / 1000000) = 1/(1000000 / 1179431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (82516059 / 500000000) (165032119 / 1000000000) (Real.log (1179431 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1179431 / 1000000) = -Real.log (1000000 / 1179431) := by
    rw [show ((1179431 / 1000000) : ℝ) = ((1000000 / 1179431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (49439319 / 250000000) ≤ -Real.log (820569 / 1000000) ∧
    -Real.log (820569 / 1000000) ≤ (197757277 / 1000000000) := by
  have h := checkLog_sound (w := (179431 / 1820569)) (n := 12)
    (lo := (49439319 / 250000000)) (hi := (197757277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820569) = 1/(820569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197757277 / 1000000000) (-49439319 / 250000000) (Real.log (820569 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (731332699 / 1000000000) ≤ -Real.log (100000000000 / 207784791103) ∧
    -Real.log (100000000000 / 207784791103) ≤ (731332701 / 1000000000) := by
  have h := checkLog_sound (w := (7784791103 / 407784791103)) (n := 12)
    (lo := (38185519 / 1000000000)) (hi := (477319 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207784791103 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207784791103 / 200000000000) = 1/(100000000000 / 207784791103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (731332699 / 1000000000) (731332701 / 1000000000) (Real.log (207784791103 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (207784791103 / 100000000000) = -Real.log (100000000000 / 207784791103) := by
    rw [show ((207784791103 / 100000000000) : ℝ) = ((100000000000 / 207784791103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (73266869 / 100000000) ≤ -Real.log (500000000000 / 1040312876053) ∧
    -Real.log (500000000000 / 1040312876053) ≤ (183167173 / 250000000) := by
  have h := checkLog_sound (w := (40312876053 / 2040312876053)) (n := 12)
    (lo := (3952151 / 100000000)) (hi := (39521511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040312876053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040312876053 / 1000000000000) = 1/(500000000000 / 1040312876053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (73266869 / 100000000) (183167173 / 250000000) (Real.log (1040312876053 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1040312876053 / 500000000000) = -Real.log (500000000000 / 1040312876053) := by
    rw [show ((1040312876053 / 500000000000) : ℝ) = ((500000000000 / 1040312876053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (508603307 / 1000000000) ≤ -Real.log (25000000000 / 41574172949) ∧
    -Real.log (25000000000 / 41574172949) ≤ (127150827 / 250000000) := by
  have h := checkLog_sound (w := (16574172949 / 66574172949)) (n := 12)
    (lo := (508603307 / 1000000000)) (hi := (127150827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41574172949 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41574172949 / 25000000000) = 1/(25000000000 / 41574172949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (508603307 / 1000000000) (127150827 / 250000000) (Real.log (41574172949 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (41574172949 / 25000000000) = -Real.log (25000000000 / 41574172949) := by
    rw [show ((41574172949 / 25000000000) : ℝ) = ((25000000000 / 41574172949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6368843 / 12500000) ≤ -Real.log (500000000000 / 832235571223) ∧
    -Real.log (500000000000 / 832235571223) ≤ (509507441 / 1000000000) := by
  have h := checkLog_sound (w := (332235571223 / 1332235571223)) (n := 12)
    (lo := (6368843 / 12500000)) (hi := (509507441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832235571223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832235571223 / 500000000000) = 1/(500000000000 / 832235571223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (6368843 / 12500000) (509507441 / 1000000000) (Real.log (832235571223 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (832235571223 / 500000000000) = -Real.log (500000000000 / 832235571223) := by
    rw [show ((832235571223 / 500000000000) : ℝ) = ((500000000000 / 832235571223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14485539 / 40000000) ≤ -Real.log (31250000000 / 44887432329) ∧
    -Real.log (31250000000 / 44887432329) ≤ (90534619 / 250000000) := by
  have h := checkLog_sound (w := (13637432329 / 76137432329)) (n := 12)
    (lo := (14485539 / 40000000)) (hi := (90534619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44887432329 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44887432329 / 31250000000) = 1/(31250000000 / 44887432329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14485539 / 40000000) (90534619 / 250000000) (Real.log (44887432329 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44887432329 / 31250000000) = -Real.log (31250000000 / 44887432329) := by
    rw [show ((44887432329 / 31250000000) : ℝ) = ((31250000000 / 44887432329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72557879 / 200000000) ≤ -Real.log (20000000000 / 28746662377) ∧
    -Real.log (20000000000 / 28746662377) ≤ (90697349 / 250000000) := by
  have h := checkLog_sound (w := (8746662377 / 48746662377)) (n := 12)
    (lo := (72557879 / 200000000)) (hi := (90697349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28746662377 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28746662377 / 20000000000) = 1/(20000000000 / 28746662377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72557879 / 200000000) (90697349 / 250000000) (Real.log (28746662377 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28746662377 / 20000000000) = -Real.log (20000000000 / 28746662377) := by
    rw [show ((28746662377 / 20000000000) : ℝ) = ((20000000000 / 28746662377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16362579 / 500000000) ≤ -Real.log (967804516239 / 1000000000000) ∧
    -Real.log (967804516239 / 1000000000000) ≤ (32725159 / 1000000000) := by
  have h := checkLog_sound (w := (32195483761 / 1967804516239)) (n := 12)
    (lo := (16362579 / 500000000)) (hi := (32725159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967804516239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967804516239) = 1/(967804516239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32725159 / 1000000000) (-16362579 / 500000000) (Real.log (967804516239 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6521693 / 200000000) ≤ -Real.log (60494841159 / 62500000000) ∧
    -Real.log (60494841159 / 62500000000) ≤ (16304233 / 500000000) := by
  have h := checkLog_sound (w := (2005158841 / 122994841159)) (n := 12)
    (lo := (6521693 / 200000000)) (hi := (16304233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60494841159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60494841159) = 1/(60494841159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16304233 / 500000000) (-6521693 / 200000000) (Real.log (60494841159 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell171
