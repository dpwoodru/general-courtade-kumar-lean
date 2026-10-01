import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0429
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

theorem reflection_log_1_neg : (193247973 / 1000000000) ≤ -Real.log (10240 / 12423) ∧
    -Real.log (10240 / 12423) ≤ (96623987 / 500000000) := by
  have h := checkLog_sound (w := (2183 / 22663)) (n := 12)
    (lo := (193247973 / 1000000000)) (hi := (96623987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12423 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12423 / 10240) = 1/(10240 / 12423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (193247973 / 1000000000) (96623987 / 500000000) (Real.log (12423 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12423 / 10240) = -Real.log (10240 / 12423) := by
    rw [show ((12423 / 10240) : ℝ) = ((10240 / 12423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11988017 / 50000000) ≤ -Real.log (8057 / 10240) ∧
    -Real.log (8057 / 10240) ≤ (239760341 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 18297)) (n := 12)
    (lo := (11988017 / 50000000)) (hi := (239760341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8057) = 1/(8057 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-239760341 / 1000000000) (-11988017 / 50000000) (Real.log (8057 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24125807 / 125000000) ≤ -Real.log (512 / 621) ∧
    -Real.log (512 / 621) ≤ (193006457 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1133)) (n := 12)
    (lo := (24125807 / 125000000)) (hi := (193006457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 512) = 1/(512 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24125807 / 125000000) (193006457 / 1000000000) (Real.log (621 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (621 / 512) = -Real.log (512 / 621) := by
    rw [show ((621 / 512) : ℝ) = ((512 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (239388063 / 1000000000) ≤ -Real.log (403 / 512) ∧
    -Real.log (403 / 512) ≤ (7480877 / 31250000) := by
  have h := checkLog_sound (w := (109 / 915)) (n := 12)
    (lo := (239388063 / 1000000000)) (hi := (7480877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 403) = 1/(403 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7480877 / 31250000) (-239388063 / 1000000000) (Real.log (403 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (355130783 / 1000000000) ≤ -Real.log (5120 / 7303) ∧
    -Real.log (5120 / 7303) ≤ (11097837 / 31250000) := by
  have h := checkLog_sound (w := (2183 / 12423)) (n := 12)
    (lo := (355130783 / 1000000000)) (hi := (11097837 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7303 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7303 / 5120) = 1/(5120 / 7303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (355130783 / 1000000000) (11097837 / 31250000) (Real.log (7303 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7303 / 5120) = -Real.log (5120 / 7303) := by
    rw [show ((7303 / 5120) : ℝ) = ((5120 / 7303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (277882893 / 500000000) ≤ -Real.log (2937 / 5120) ∧
    -Real.log (2937 / 5120) ≤ (555765787 / 1000000000) := by
  have h := checkLog_sound (w := (2183 / 8057)) (n := 12)
    (lo := (277882893 / 500000000)) (hi := (555765787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2937) = 1/(2937 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-555765787 / 1000000000) (-277882893 / 500000000) (Real.log (2937 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (354719909 / 1000000000) ≤ -Real.log (256 / 365) ∧
    -Real.log (256 / 365) ≤ (35471991 / 100000000) := by
  have h := checkLog_sound (w := (109 / 621)) (n := 12)
    (lo := (354719909 / 1000000000)) (hi := (35471991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365 / 256) = 1/(256 / 365) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (354719909 / 1000000000) (35471991 / 100000000) (Real.log (365 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (365 / 256) = -Real.log (256 / 365) := by
    rw [show ((365 / 256) : ℝ) = ((256 / 365) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (554744857 / 1000000000) ≤ -Real.log (147 / 256) ∧
    -Real.log (147 / 256) ≤ (277372429 / 500000000) := by
  have h := checkLog_sound (w := (109 / 403)) (n := 12)
    (lo := (554744857 / 1000000000)) (hi := (277372429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 147) = 1/(147 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277372429 / 500000000) (-554744857 / 1000000000) (Real.log (147 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (265080571 / 1000000000) ≤ -Real.log (62500 / 81471) ∧
    -Real.log (62500 / 81471) ≤ (66270143 / 250000000) := by
  have h := checkLog_sound (w := (18971 / 143971)) (n := 12)
    (lo := (265080571 / 1000000000)) (hi := (66270143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81471 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81471 / 62500) = 1/(62500 / 81471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (265080571 / 1000000000) (66270143 / 250000000) (Real.log (81471 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (81471 / 62500) = -Real.log (62500 / 81471) := by
    rw [show ((81471 / 62500) : ℝ) = ((62500 / 81471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (180869587 / 500000000) ≤ -Real.log (43529 / 62500) ∧
    -Real.log (43529 / 62500) ≤ (14469567 / 40000000) := by
  have h := checkLog_sound (w := (18971 / 106029)) (n := 12)
    (lo := (180869587 / 500000000)) (hi := (14469567 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43529) = 1/(43529 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14469567 / 40000000) (-180869587 / 500000000) (Real.log (43529 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265407321 / 1000000000) ≤ -Real.log (500000 / 651981) ∧
    -Real.log (500000 / 651981) ≤ (132703661 / 500000000) := by
  have h := checkLog_sound (w := (151981 / 1151981)) (n := 12)
    (lo := (265407321 / 1000000000)) (hi := (132703661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651981 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651981 / 500000) = 1/(500000 / 651981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265407321 / 1000000000) (132703661 / 500000000) (Real.log (651981 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (651981 / 500000) = -Real.log (500000 / 651981) := by
    rw [show ((651981 / 500000) : ℝ) = ((500000 / 651981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (181175511 / 500000000) ≤ -Real.log (348019 / 500000) ∧
    -Real.log (348019 / 500000) ≤ (362351023 / 1000000000) := by
  have h := checkLog_sound (w := (151981 / 848019)) (n := 12)
    (lo := (181175511 / 500000000)) (hi := (362351023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348019) = 1/(348019 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-362351023 / 1000000000) (-181175511 / 500000000) (Real.log (348019 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7962263 / 40000000) ≤ -Real.log (1000000 / 1220251) ∧
    -Real.log (1000000 / 1220251) ≤ (3110259 / 15625000) := by
  have h := checkLog_sound (w := (220251 / 2220251)) (n := 12)
    (lo := (7962263 / 40000000)) (hi := (3110259 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220251 / 1000000) = 1/(1000000 / 1220251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7962263 / 40000000) (3110259 / 15625000) (Real.log (1220251 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1220251 / 1000000) = -Real.log (1000000 / 1220251) := by
    rw [show ((1220251 / 1000000) : ℝ) = ((1000000 / 1220251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49756641 / 200000000) ≤ -Real.log (779749 / 1000000) ∧
    -Real.log (779749 / 1000000) ≤ (124391603 / 500000000) := by
  have h := checkLog_sound (w := (220251 / 1779749)) (n := 12)
    (lo := (49756641 / 200000000)) (hi := (124391603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779749) = 1/(779749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-124391603 / 500000000) (-49756641 / 200000000) (Real.log (779749 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99661439 / 500000000) ≤ -Real.log (31250 / 38143) ∧
    -Real.log (31250 / 38143) ≤ (199322879 / 1000000000) := by
  have h := checkLog_sound (w := (6893 / 69393)) (n := 12)
    (lo := (99661439 / 500000000)) (hi := (199322879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38143 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38143 / 31250) = 1/(31250 / 38143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99661439 / 500000000) (199322879 / 1000000000) (Real.log (38143 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38143 / 31250) = -Real.log (31250 / 38143) := by
    rw [show ((38143 / 31250) : ℝ) = ((31250 / 38143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (249200093 / 1000000000) ≤ -Real.log (24357 / 31250) ∧
    -Real.log (24357 / 31250) ≤ (124600047 / 500000000) := by
  have h := checkLog_sound (w := (6893 / 55607)) (n := 12)
    (lo := (249200093 / 1000000000)) (hi := (124600047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24357) = 1/(24357 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-124600047 / 500000000) (-249200093 / 1000000000) (Real.log (24357 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (313409873 / 500000000) ≤ -Real.log (500000000000 / 935824392933) ∧
    -Real.log (500000000000 / 935824392933) ≤ (626819747 / 1000000000) := by
  have h := checkLog_sound (w := (435824392933 / 1435824392933)) (n := 12)
    (lo := (313409873 / 500000000)) (hi := (626819747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935824392933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935824392933 / 500000000000) = 1/(500000000000 / 935824392933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (313409873 / 500000000) (626819747 / 1000000000) (Real.log (935824392933 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (935824392933 / 500000000000) = -Real.log (500000000000 / 935824392933) := by
    rw [show ((935824392933 / 500000000000) : ℝ) = ((500000000000 / 935824392933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (78469793 / 125000000) ≤ -Real.log (250000000000 / 468351584253) ∧
    -Real.log (250000000000 / 468351584253) ≤ (125551669 / 200000000) := by
  have h := checkLog_sound (w := (218351584253 / 718351584253)) (n := 12)
    (lo := (78469793 / 125000000)) (hi := (125551669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468351584253 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468351584253 / 250000000000) = 1/(250000000000 / 468351584253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (78469793 / 125000000) (125551669 / 200000000) (Real.log (468351584253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (468351584253 / 250000000000) = -Real.log (250000000000 / 468351584253) := by
    rw [show ((468351584253 / 250000000000) : ℝ) = ((250000000000 / 468351584253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (447839781 / 1000000000) ≤ -Real.log (25000000000 / 39123198619) ∧
    -Real.log (25000000000 / 39123198619) ≤ (223919891 / 500000000) := by
  have h := checkLog_sound (w := (14123198619 / 64123198619)) (n := 12)
    (lo := (447839781 / 1000000000)) (hi := (223919891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39123198619 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39123198619 / 25000000000) = 1/(25000000000 / 39123198619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (447839781 / 1000000000) (223919891 / 500000000) (Real.log (39123198619 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (39123198619 / 25000000000) = -Real.log (25000000000 / 39123198619) := by
    rw [show ((39123198619 / 25000000000) : ℝ) = ((25000000000 / 39123198619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (112130743 / 250000000) ≤ -Real.log (250000000000 / 391499363633) ∧
    -Real.log (250000000000 / 391499363633) ≤ (448522973 / 1000000000) := by
  have h := checkLog_sound (w := (141499363633 / 641499363633)) (n := 12)
    (lo := (112130743 / 250000000)) (hi := (448522973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391499363633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391499363633 / 250000000000) = 1/(250000000000 / 391499363633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (112130743 / 250000000) (448522973 / 1000000000) (Real.log (391499363633 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (391499363633 / 250000000000) = -Real.log (250000000000 / 391499363633) := by
    rw [show ((391499363633 / 250000000000) : ℝ) = ((250000000000 / 391499363633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0429
