import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell138
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

theorem reflection_log_1_neg : (286265053 / 1000000000) ≤ -Real.log (5120 / 6817) ∧
    -Real.log (5120 / 6817) ≤ (143132527 / 500000000) := by
  have h := checkLog_sound (w := (1697 / 11937)) (n := 12)
    (lo := (286265053 / 1000000000)) (hi := (143132527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6817 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6817 / 5120) = 1/(5120 / 6817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (286265053 / 1000000000) (143132527 / 500000000) (Real.log (6817 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6817 / 5120) = -Real.log (5120 / 6817) := by
    rw [show ((6817 / 5120) : ℝ) = ((5120 / 6817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (402637079 / 1000000000) ≤ -Real.log (3423 / 5120) ∧
    -Real.log (3423 / 5120) ≤ (10065927 / 25000000) := by
  have h := checkLog_sound (w := (1697 / 8543)) (n := 12)
    (lo := (402637079 / 1000000000)) (hi := (10065927 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3423) = 1/(3423 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10065927 / 25000000) (-402637079 / 1000000000) (Real.log (3423 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3572811 / 12500000) ≤ -Real.log (2560 / 3407) ∧
    -Real.log (2560 / 3407) ≤ (285824881 / 1000000000) := by
  have h := checkLog_sound (w := (847 / 5967)) (n := 12)
    (lo := (3572811 / 12500000)) (hi := (285824881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3407 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3407 / 2560) = 1/(2560 / 3407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3572811 / 12500000) (285824881 / 1000000000) (Real.log (3407 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3407 / 2560) = -Real.log (2560 / 3407) := by
    rw [show ((3407 / 2560) : ℝ) = ((2560 / 3407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (401761039 / 1000000000) ≤ -Real.log (1713 / 2560) ∧
    -Real.log (1713 / 2560) ≤ (5022013 / 12500000) := by
  have h := checkLog_sound (w := (847 / 4273)) (n := 12)
    (lo := (401761039 / 1000000000)) (hi := (5022013 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1713) = 1/(1713 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-5022013 / 12500000) (-401761039 / 1000000000) (Real.log (1713 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (105564229 / 500000000) ≤ -Real.log (1000000 / 1235071) ∧
    -Real.log (1000000 / 1235071) ≤ (211128459 / 1000000000) := by
  have h := checkLog_sound (w := (235071 / 2235071)) (n := 12)
    (lo := (105564229 / 500000000)) (hi := (211128459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235071 / 1000000) = 1/(1000000 / 1235071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (105564229 / 500000000) (211128459 / 1000000000) (Real.log (1235071 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1235071 / 1000000) = -Real.log (1000000 / 1235071) := by
    rw [show ((1235071 / 1000000) : ℝ) = ((1000000 / 1235071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (267972259 / 1000000000) ≤ -Real.log (764929 / 1000000) ∧
    -Real.log (764929 / 1000000) ≤ (13398613 / 50000000) := by
  have h := checkLog_sound (w := (235071 / 1764929)) (n := 12)
    (lo := (267972259 / 1000000000)) (hi := (13398613 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764929) = 1/(764929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13398613 / 50000000) (-267972259 / 1000000000) (Real.log (764929 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (211469271 / 1000000000) ≤ -Real.log (250000 / 308873) ∧
    -Real.log (250000 / 308873) ≤ (26433659 / 125000000) := by
  have h := checkLog_sound (w := (58873 / 558873)) (n := 12)
    (lo := (211469271 / 1000000000)) (hi := (26433659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308873 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308873 / 250000) = 1/(250000 / 308873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (211469271 / 1000000000) (26433659 / 125000000) (Real.log (308873 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (308873 / 250000) = -Real.log (250000 / 308873) := by
    rw [show ((308873 / 250000) : ℝ) = ((250000 / 308873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (268522789 / 1000000000) ≤ -Real.log (191127 / 250000) ∧
    -Real.log (191127 / 250000) ≤ (26852279 / 100000000) := by
  have h := checkLog_sound (w := (58873 / 441127)) (n := 12)
    (lo := (268522789 / 1000000000)) (hi := (26852279 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191127) = 1/(191127 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26852279 / 100000000) (-268522789 / 1000000000) (Real.log (191127 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155981859 / 1000000000) ≤ -Real.log (200000 / 233761) ∧
    -Real.log (200000 / 233761) ≤ (7799093 / 50000000) := by
  have h := checkLog_sound (w := (33761 / 433761)) (n := 12)
    (lo := (155981859 / 1000000000)) (hi := (7799093 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233761 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233761 / 200000) = 1/(200000 / 233761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155981859 / 1000000000) (7799093 / 50000000) (Real.log (233761 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233761 / 200000) = -Real.log (200000 / 233761) := by
    rw [show ((233761 / 200000) : ℝ) = ((200000 / 233761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92445427 / 500000000) ≤ -Real.log (166239 / 200000) ∧
    -Real.log (166239 / 200000) ≤ (36978171 / 200000000) := by
  have h := checkLog_sound (w := (33761 / 366239)) (n := 12)
    (lo := (92445427 / 500000000)) (hi := (36978171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166239) = 1/(166239 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36978171 / 200000000) (-92445427 / 500000000) (Real.log (166239 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156248763 / 1000000000) ≤ -Real.log (1000000 / 1169117) ∧
    -Real.log (1000000 / 1169117) ≤ (39062191 / 250000000) := by
  have h := checkLog_sound (w := (169117 / 2169117)) (n := 12)
    (lo := (156248763 / 1000000000)) (hi := (39062191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169117 / 1000000) = 1/(1000000 / 1169117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156248763 / 1000000000) (39062191 / 250000000) (Real.log (1169117 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1169117 / 1000000) = -Real.log (1000000 / 1169117) := by
    rw [show ((1169117 / 1000000) : ℝ) = ((1000000 / 1169117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (11579143 / 62500000) ≤ -Real.log (830883 / 1000000) ∧
    -Real.log (830883 / 1000000) ≤ (185266289 / 1000000000) := by
  have h := checkLog_sound (w := (169117 / 1830883)) (n := 12)
    (lo := (11579143 / 62500000)) (hi := (185266289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830883) = 1/(830883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-185266289 / 1000000000) (-11579143 / 62500000) (Real.log (830883 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (687585919 / 1000000000) ≤ -Real.log (500000000000 / 994454173963) ∧
    -Real.log (500000000000 / 994454173963) ≤ (1074353 / 1562500) := by
  have h := checkLog_sound (w := (494454173963 / 1494454173963)) (n := 12)
    (lo := (687585919 / 1000000000)) (hi := (1074353 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994454173963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994454173963 / 500000000000) = 1/(500000000000 / 994454173963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (687585919 / 1000000000) (1074353 / 1562500) (Real.log (994454173963 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (994454173963 / 500000000000) = -Real.log (500000000000 / 994454173963) := by
    rw [show ((994454173963 / 500000000000) : ℝ) = ((500000000000 / 994454173963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172225533 / 250000000) ≤ -Real.log (62500000000 / 124470493719) ∧
    -Real.log (62500000000 / 124470493719) ≤ (688902133 / 1000000000) := by
  have h := checkLog_sound (w := (61970493719 / 186970493719)) (n := 12)
    (lo := (172225533 / 250000000)) (hi := (688902133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124470493719 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124470493719 / 62500000000) = 1/(62500000000 / 124470493719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (172225533 / 250000000) (688902133 / 1000000000) (Real.log (124470493719 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (124470493719 / 62500000000) = -Real.log (62500000000 / 124470493719) := by
    rw [show ((124470493719 / 62500000000) : ℝ) = ((62500000000 / 124470493719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (239550359 / 500000000) ≤ -Real.log (125000000000 / 201827718651) ∧
    -Real.log (125000000000 / 201827718651) ≤ (479100719 / 1000000000) := by
  have h := checkLog_sound (w := (76827718651 / 326827718651)) (n := 12)
    (lo := (239550359 / 500000000)) (hi := (479100719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201827718651 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201827718651 / 125000000000) = 1/(125000000000 / 201827718651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (239550359 / 500000000) (479100719 / 1000000000) (Real.log (201827718651 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (201827718651 / 125000000000) = -Real.log (125000000000 / 201827718651) := by
    rw [show ((201827718651 / 125000000000) : ℝ) = ((125000000000 / 201827718651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23999603 / 50000000) ≤ -Real.log (500000000000 / 808030785813) ∧
    -Real.log (500000000000 / 808030785813) ≤ (479992061 / 1000000000) := by
  have h := checkLog_sound (w := (308030785813 / 1308030785813)) (n := 12)
    (lo := (23999603 / 50000000)) (hi := (479992061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808030785813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808030785813 / 500000000000) = 1/(500000000000 / 808030785813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23999603 / 50000000) (479992061 / 1000000000) (Real.log (808030785813 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (808030785813 / 500000000000) = -Real.log (500000000000 / 808030785813) := by
    rw [show ((808030785813 / 500000000000) : ℝ) = ((500000000000 / 808030785813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (340872713 / 1000000000) ≤ -Real.log (500000000000 / 703087121553) ∧
    -Real.log (500000000000 / 703087121553) ≤ (170436357 / 500000000) := by
  have h := checkLog_sound (w := (203087121553 / 1203087121553)) (n := 12)
    (lo := (340872713 / 1000000000)) (hi := (170436357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703087121553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703087121553 / 500000000000) = 1/(500000000000 / 703087121553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (340872713 / 1000000000) (170436357 / 500000000) (Real.log (703087121553 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703087121553 / 500000000000) = -Real.log (500000000000 / 703087121553) := by
    rw [show ((703087121553 / 500000000000) : ℝ) = ((500000000000 / 703087121553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (341515051 / 1000000000) ≤ -Real.log (25000000000 / 35176944287) ∧
    -Real.log (25000000000 / 35176944287) ≤ (85378763 / 250000000) := by
  have h := checkLog_sound (w := (10176944287 / 60176944287)) (n := 12)
    (lo := (341515051 / 1000000000)) (hi := (85378763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35176944287 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35176944287 / 25000000000) = 1/(25000000000 / 35176944287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (341515051 / 1000000000) (85378763 / 250000000) (Real.log (35176944287 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35176944287 / 25000000000) = -Real.log (25000000000 / 35176944287) := by
    rw [show ((35176944287 / 25000000000) : ℝ) = ((25000000000 / 35176944287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1160701 / 40000000) ≤ -Real.log (971399440311 / 1000000000000) ∧
    -Real.log (971399440311 / 1000000000000) ≤ (14508763 / 500000000) := by
  have h := checkLog_sound (w := (28600559689 / 1971399440311)) (n := 12)
    (lo := (1160701 / 40000000)) (hi := (14508763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971399440311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971399440311) = 1/(971399440311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-14508763 / 500000000) (-1160701 / 40000000) (Real.log (971399440311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5781799 / 200000000) ≤ -Real.log (38860194879 / 40000000000) ∧
    -Real.log (38860194879 / 40000000000) ≤ (7227249 / 250000000) := by
  have h := checkLog_sound (w := (1139805121 / 78860194879)) (n := 12)
    (lo := (5781799 / 200000000)) (hi := (7227249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38860194879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38860194879) = 1/(38860194879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7227249 / 250000000) (-5781799 / 200000000) (Real.log (38860194879 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell138
