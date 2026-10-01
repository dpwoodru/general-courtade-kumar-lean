import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell192
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

theorem reflection_log_1_neg : (387189 / 1250000) ≤ -Real.log (5120 / 6979) ∧
    -Real.log (5120 / 6979) ≤ (309751201 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 12099)) (n := 12)
    (lo := (387189 / 1250000)) (hi := (309751201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6979 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6979 / 5120) = 1/(5120 / 6979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (387189 / 1250000) (309751201 / 1000000000) (Real.log (6979 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6979 / 5120) = -Real.log (5120 / 6979) := by
    rw [show ((6979 / 5120) : ℝ) = ((5120 / 6979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (225560271 / 500000000) ≤ -Real.log (3261 / 5120) ∧
    -Real.log (3261 / 5120) ≤ (451120543 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 8381)) (n := 12)
    (lo := (225560271 / 500000000)) (hi := (451120543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3261) = 1/(3261 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-451120543 / 1000000000) (-225560271 / 500000000) (Real.log (3261 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (309321247 / 1000000000) ≤ -Real.log (80 / 109) ∧
    -Real.log (80 / 109) ≤ (9666289 / 31250000) := by
  have h := checkLog_sound (w := (29 / 189)) (n := 12)
    (lo := (309321247 / 1000000000)) (hi := (9666289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109 / 80) = 1/(80 / 109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (309321247 / 1000000000) (9666289 / 31250000) (Real.log (109 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (109 / 80) = -Real.log (80 / 109) := by
    rw [show ((109 / 80) : ℝ) = ((80 / 109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (450201001 / 1000000000) ≤ -Real.log (51 / 80) ∧
    -Real.log (51 / 80) ≤ (225100501 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 51) = 1/(51 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-225100501 / 500000000) (-450201001 / 1000000000) (Real.log (51 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (57343227 / 250000000) ≤ -Real.log (1000000 / 1257811) ∧
    -Real.log (1000000 / 1257811) ≤ (229372909 / 1000000000) := by
  have h := checkLog_sound (w := (257811 / 2257811)) (n := 12)
    (lo := (57343227 / 250000000)) (hi := (229372909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257811 / 1000000) = 1/(1000000 / 1257811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (57343227 / 250000000) (229372909 / 1000000000) (Real.log (1257811 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1257811 / 1000000) = -Real.log (1000000 / 1257811) := by
    rw [show ((1257811 / 1000000) : ℝ) = ((1000000 / 1257811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298151351 / 1000000000) ≤ -Real.log (742189 / 1000000) ∧
    -Real.log (742189 / 1000000) ≤ (37268919 / 125000000) := by
  have h := checkLog_sound (w := (257811 / 1742189)) (n := 12)
    (lo := (298151351 / 1000000000)) (hi := (37268919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742189) = 1/(742189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-37268919 / 125000000) (-298151351 / 1000000000) (Real.log (742189 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4594183 / 20000000) ≤ -Real.log (500000 / 629117) ∧
    -Real.log (500000 / 629117) ≤ (229709151 / 1000000000) := by
  have h := checkLog_sound (w := (129117 / 1129117)) (n := 12)
    (lo := (4594183 / 20000000)) (hi := (229709151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629117 / 500000) = 1/(500000 / 629117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4594183 / 20000000) (229709151 / 1000000000) (Real.log (629117 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629117 / 500000) = -Real.log (500000 / 629117) := by
    rw [show ((629117 / 500000) : ℝ) = ((500000 / 629117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298721449 / 1000000000) ≤ -Real.log (370883 / 500000) ∧
    -Real.log (370883 / 500000) ≤ (5974429 / 20000000) := by
  have h := checkLog_sound (w := (129117 / 870883)) (n := 12)
    (lo := (298721449 / 1000000000)) (hi := (5974429 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370883) = 1/(370883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5974429 / 20000000) (-298721449 / 1000000000) (Real.log (370883 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170349341 / 1000000000) ≤ -Real.log (1000000 / 1185719) ∧
    -Real.log (1000000 / 1185719) ≤ (85174671 / 500000000) := by
  have h := checkLog_sound (w := (185719 / 2185719)) (n := 12)
    (lo := (170349341 / 1000000000)) (hi := (85174671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185719 / 1000000) = 1/(1000000 / 1185719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170349341 / 1000000000) (85174671 / 500000000) (Real.log (1185719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1185719 / 1000000) = -Real.log (1000000 / 1185719) := by
    rw [show ((1185719 / 1000000) : ℝ) = ((1000000 / 1185719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205449763 / 1000000000) ≤ -Real.log (814281 / 1000000) ∧
    -Real.log (814281 / 1000000) ≤ (51362441 / 250000000) := by
  have h := checkLog_sound (w := (185719 / 1814281)) (n := 12)
    (lo := (205449763 / 1000000000)) (hi := (51362441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814281) = 1/(814281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-51362441 / 250000000) (-205449763 / 1000000000) (Real.log (814281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85308327 / 500000000) ≤ -Real.log (250000 / 296509) ∧
    -Real.log (250000 / 296509) ≤ (34123331 / 200000000) := by
  have h := checkLog_sound (w := (46509 / 546509)) (n := 12)
    (lo := (85308327 / 500000000)) (hi := (34123331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296509 / 250000) = 1/(250000 / 296509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85308327 / 500000000) (34123331 / 200000000) (Real.log (296509 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (296509 / 250000) = -Real.log (250000 / 296509) := by
    rw [show ((296509 / 250000) : ℝ) = ((250000 / 296509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10291957 / 50000000) ≤ -Real.log (203491 / 250000) ∧
    -Real.log (203491 / 250000) ≤ (205839141 / 1000000000) := by
  have h := checkLog_sound (w := (46509 / 453491)) (n := 12)
    (lo := (10291957 / 50000000)) (hi := (205839141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203491) = 1/(203491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-205839141 / 1000000000) (-10291957 / 50000000) (Real.log (203491 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94940281 / 125000000) ≤ -Real.log (25000000000 / 53431372549) ∧
    -Real.log (25000000000 / 53431372549) ≤ (3038089 / 4000000) := by
  have h := checkLog_sound (w := (3431372549 / 103431372549)) (n := 12)
    (lo := (16593767 / 250000000)) (hi := (66375069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53431372549 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53431372549 / 50000000000) = 1/(25000000000 / 53431372549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94940281 / 125000000) (3038089 / 4000000) (Real.log (53431372549 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53431372549 / 25000000000) = -Real.log (25000000000 / 53431372549) := by
    rw [show ((53431372549 / 25000000000) : ℝ) = ((25000000000 / 53431372549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (380435871 / 500000000) ≤ -Real.log (500000000000 / 1070070530513) ∧
    -Real.log (500000000000 / 1070070530513) ≤ (11888621 / 15625000) := by
  have h := checkLog_sound (w := (70070530513 / 2070070530513)) (n := 12)
    (lo := (33862281 / 500000000)) (hi := (67724563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070070530513 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070070530513 / 1000000000000) = 1/(500000000000 / 1070070530513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (380435871 / 500000000) (11888621 / 15625000) (Real.log (1070070530513 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1070070530513 / 500000000000) = -Real.log (500000000000 / 1070070530513) := by
    rw [show ((1070070530513 / 500000000000) : ℝ) = ((500000000000 / 1070070530513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (527524259 / 1000000000) ≤ -Real.log (100000000000 / 169473139591) ∧
    -Real.log (100000000000 / 169473139591) ≤ (26376213 / 50000000) := by
  have h := checkLog_sound (w := (69473139591 / 269473139591)) (n := 12)
    (lo := (527524259 / 1000000000)) (hi := (26376213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169473139591 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169473139591 / 100000000000) = 1/(100000000000 / 169473139591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (527524259 / 1000000000) (26376213 / 50000000) (Real.log (169473139591 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (169473139591 / 100000000000) = -Real.log (100000000000 / 169473139591) := by
    rw [show ((169473139591 / 100000000000) : ℝ) = ((100000000000 / 169473139591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (528430599 / 1000000000) ≤ -Real.log (100000000000 / 169626809533) ∧
    -Real.log (100000000000 / 169626809533) ≤ (2642153 / 5000000) := by
  have h := checkLog_sound (w := (69626809533 / 269626809533)) (n := 12)
    (lo := (528430599 / 1000000000)) (hi := (2642153 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169626809533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169626809533 / 100000000000) = 1/(100000000000 / 169626809533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (528430599 / 1000000000) (2642153 / 5000000) (Real.log (169626809533 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (169626809533 / 100000000000) = -Real.log (100000000000 / 169626809533) := by
    rw [show ((169626809533 / 100000000000) : ℝ) = ((100000000000 / 169626809533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (75159821 / 200000000) ≤ -Real.log (500000000000 / 728077285359) ∧
    -Real.log (500000000000 / 728077285359) ≤ (187899553 / 500000000) := by
  have h := checkLog_sound (w := (228077285359 / 1228077285359)) (n := 12)
    (lo := (75159821 / 200000000)) (hi := (187899553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728077285359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728077285359 / 500000000000) = 1/(500000000000 / 728077285359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (75159821 / 200000000) (187899553 / 500000000) (Real.log (728077285359 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (728077285359 / 500000000000) = -Real.log (500000000000 / 728077285359) := by
    rw [show ((728077285359 / 500000000000) : ℝ) = ((500000000000 / 728077285359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (188227897 / 500000000) ≤ -Real.log (250000000000 / 364277781327) ∧
    -Real.log (250000000000 / 364277781327) ≤ (75291159 / 200000000) := by
  have h := checkLog_sound (w := (114277781327 / 614277781327)) (n := 12)
    (lo := (188227897 / 500000000)) (hi := (75291159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364277781327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364277781327 / 250000000000) = 1/(250000000000 / 364277781327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (188227897 / 500000000) (75291159 / 200000000) (Real.log (364277781327 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (364277781327 / 250000000000) = -Real.log (250000000000 / 364277781327) := by
    rw [show ((364277781327 / 250000000000) : ℝ) = ((250000000000 / 364277781327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7044497 / 200000000) ≤ -Real.log (60336912919 / 62500000000) ∧
    -Real.log (60336912919 / 62500000000) ≤ (17611243 / 500000000) := by
  have h := checkLog_sound (w := (2163087081 / 122836912919)) (n := 12)
    (lo := (7044497 / 200000000)) (hi := (17611243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60336912919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60336912919) = 1/(60336912919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17611243 / 500000000) (-7044497 / 200000000) (Real.log (60336912919 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17550211 / 500000000) ≤ -Real.log (965508453039 / 1000000000000) ∧
    -Real.log (965508453039 / 1000000000000) ≤ (35100423 / 1000000000) := by
  have h := checkLog_sound (w := (34491546961 / 1965508453039)) (n := 12)
    (lo := (17550211 / 500000000)) (hi := (35100423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965508453039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965508453039) = 1/(965508453039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35100423 / 1000000000) (-17550211 / 500000000) (Real.log (965508453039 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell192
