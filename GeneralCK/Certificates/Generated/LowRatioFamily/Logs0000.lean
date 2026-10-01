import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
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

theorem reflection_log_1_neg : (27969779 / 200000000) ≤ -Real.log (10000 / 11501) ∧
    -Real.log (10000 / 11501) ≤ (2185139 / 15625000) := by
  have h := checkLog_sound (w := (1501 / 21501)) (n := 12)
    (lo := (27969779 / 200000000)) (hi := (2185139 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11501 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11501 / 10000) = 1/(10000 / 11501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27969779 / 200000000) (2185139 / 15625000) (Real.log (11501 / 10000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11501 / 10000) = -Real.log (10000 / 11501) := by
    rw [show ((11501 / 10000) : ℝ) = ((10000 / 11501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (162636583 / 1000000000) ≤ -Real.log (8499 / 10000) ∧
    -Real.log (8499 / 10000) ≤ (20329573 / 125000000) := by
  have h := checkLog_sound (w := (1501 / 18499)) (n := 12)
    (lo := (162636583 / 1000000000)) (hi := (20329573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8499) = 1/(8499 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-20329573 / 125000000) (-162636583 / 1000000000) (Real.log (8499 / 10000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18761 / 125000000) ≤ -Real.log (10000000 / 10001501) ∧
    -Real.log (10000000 / 10001501) ≤ (150089 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 20001501)) (n := 12)
    (lo := (18761 / 125000000)) (hi := (150089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001501 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001501 / 10000000) = 1/(10000000 / 10001501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18761 / 125000000) (150089 / 1000000000) (Real.log (10001501 / 10000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10001501 / 10000000) = -Real.log (10000000 / 10001501) := by
    rw [show ((10001501 / 10000000) : ℝ) = ((10000000 / 10001501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150111 / 1000000000) ≤ -Real.log (9998499 / 10000000) ∧
    -Real.log (9998499 / 10000000) ≤ (4691 / 31250000) := by
  have h := checkLog_sound (w := (1501 / 19998499)) (n := 12)
    (lo := (150111 / 1000000000)) (hi := (4691 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998499) = 1/(9998499 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4691 / 31250000) (-150111 / 1000000000) (Real.log (9998499 / 10000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7 : Bounds 0 0 (Real.log 1) := by norm_num [Bounds]

theorem reflection_log_8_neg : (36267761 / 500000000) ≤ -Real.log (1000000 / 1075231) ∧
    -Real.log (1000000 / 1075231) ≤ (72535523 / 1000000000) := by
  have h := checkLog_sound (w := (75231 / 2075231)) (n := 12)
    (lo := (36267761 / 500000000)) (hi := (72535523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075231 / 1000000) = 1/(1000000 / 1075231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (36267761 / 500000000) (72535523 / 1000000000) (Real.log (1075231 / 1000000)) := by
  have h := reflection_log_8_neg
  have he : Real.log (1075231 / 1000000) = -Real.log (1000000 / 1075231) := by
    rw [show ((1075231 / 1000000) : ℝ) = ((1000000 / 1075231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9_neg : (39105651 / 500000000) ≤ -Real.log (924769 / 1000000) ∧
    -Real.log (924769 / 1000000) ≤ (78211303 / 1000000000) := by
  have h := checkLog_sound (w := (75231 / 1924769)) (n := 12)
    (lo := (39105651 / 500000000)) (hi := (78211303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924769) = 1/(924769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (-78211303 / 1000000000) (-39105651 / 500000000) (Real.log (924769 / 1000000)) := by
  have h := reflection_log_9_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10_neg : (72722441 / 1000000000) ≤ -Real.log (125000 / 134429) ∧
    -Real.log (125000 / 134429) ≤ (36361221 / 500000000) := by
  have h := checkLog_sound (w := (9429 / 259429)) (n := 12)
    (lo := (72722441 / 1000000000)) (hi := (36361221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134429 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134429 / 125000) = 1/(125000 / 134429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (72722441 / 1000000000) (36361221 / 500000000) (Real.log (134429 / 125000)) := by
  have h := reflection_log_10_neg
  have he : Real.log (134429 / 125000) = -Real.log (125000 / 134429) := by
    rw [show ((134429 / 125000) : ℝ) = ((125000 / 134429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11_neg : (78428677 / 1000000000) ≤ -Real.log (115571 / 125000) ∧
    -Real.log (115571 / 125000) ≤ (39214339 / 500000000) := by
  have h := checkLog_sound (w := (9429 / 240571)) (n := 12)
    (lo := (78428677 / 1000000000)) (hi := (39214339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115571) = 1/(115571 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (-39214339 / 500000000) (-78428677 / 1000000000) (Real.log (115571 / 125000)) := by
  have h := reflection_log_11_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12_neg : (1426559 / 250000000) ≤ -Real.log (15536093959 / 15625000000) ∧
    -Real.log (15536093959 / 15625000000) ≤ (5706237 / 1000000000) := by
  have h := checkLog_sound (w := (88906041 / 31161093959)) (n := 12)
    (lo := (1426559 / 250000000)) (hi := (5706237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15536093959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15536093959) = 1/(15536093959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5706237 / 1000000000) (-1426559 / 250000000) (Real.log (15536093959 / 15625000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (283789 / 50000000) ≤ -Real.log (994340296639 / 1000000000000) ∧
    -Real.log (994340296639 / 1000000000000) ≤ (5675781 / 1000000000) := by
  have h := checkLog_sound (w := (5659703361 / 1994340296639)) (n := 12)
    (lo := (283789 / 50000000)) (hi := (5675781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994340296639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994340296639) = 1/(994340296639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (-5675781 / 1000000000) (-283789 / 50000000) (Real.log (994340296639 / 1000000000000)) := by
  have h := reflection_log_13_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14_neg : (18843353 / 125000000) ≤ -Real.log (100000000000 / 116270225321) ∧
    -Real.log (100000000000 / 116270225321) ≤ (6029873 / 40000000) := by
  have h := checkLog_sound (w := (16270225321 / 216270225321)) (n := 12)
    (lo := (18843353 / 125000000)) (hi := (6029873 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116270225321 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116270225321 / 100000000000) = 1/(100000000000 / 116270225321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (18843353 / 125000000) (6029873 / 40000000) (Real.log (116270225321 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (116270225321 / 100000000000) = -Real.log (100000000000 / 116270225321) := by
    rw [show ((116270225321 / 100000000000) : ℝ) = ((100000000000 / 116270225321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (75575559 / 500000000) ≤ -Real.log (250000000000 / 290793105537) ∧
    -Real.log (250000000000 / 290793105537) ≤ (151151119 / 1000000000) := by
  have h := checkLog_sound (w := (40793105537 / 540793105537)) (n := 12)
    (lo := (75575559 / 500000000)) (hi := (151151119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290793105537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290793105537 / 250000000000) = 1/(250000000000 / 290793105537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75575559 / 500000000) (151151119 / 1000000000) (Real.log (290793105537 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (290793105537 / 250000000000) = -Real.log (250000000000 / 290793105537) := by
    rw [show ((290793105537 / 250000000000) : ℝ) = ((250000000000 / 290793105537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (302280871 / 1000000000) ≤ -Real.log (100000000000 / 135294117647) ∧
    -Real.log (100000000000 / 135294117647) ≤ (37785109 / 125000000) := by
  have h := checkLog_sound (w := (35294117647 / 235294117647)) (n := 12)
    (lo := (302280871 / 1000000000)) (hi := (37785109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135294117647 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135294117647 / 100000000000) = 1/(100000000000 / 135294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (302280871 / 1000000000) (37785109 / 125000000) (Real.log (135294117647 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (135294117647 / 100000000000) = -Real.log (100000000000 / 135294117647) := by
    rw [show ((135294117647 / 100000000000) : ℝ) = ((100000000000 / 135294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (151242739 / 500000000) ≤ -Real.log (250000000000 / 338304506413) ∧
    -Real.log (250000000000 / 338304506413) ≤ (302485479 / 1000000000) := by
  have h := checkLog_sound (w := (88304506413 / 588304506413)) (n := 12)
    (lo := (151242739 / 500000000)) (hi := (302485479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338304506413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338304506413 / 250000000000) = 1/(250000000000 / 338304506413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (151242739 / 500000000) (302485479 / 1000000000) (Real.log (338304506413 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (338304506413 / 250000000000) = -Real.log (250000000000 / 338304506413) := by
    rw [show ((338304506413 / 250000000000) : ℝ) = ((250000000000 / 338304506413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (874599 / 6250000) ≤ -Real.log (5000 / 5751) ∧
    -Real.log (5000 / 5751) ≤ (139935841 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 10751)) (n := 12)
    (lo := (874599 / 6250000)) (hi := (139935841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5751 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5751 / 5000) = 1/(5000 / 5751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (874599 / 6250000) (139935841 / 1000000000) (Real.log (5751 / 5000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5751 / 5000) = -Real.log (5000 / 5751) := by
    rw [show ((5751 / 5000) : ℝ) = ((5000 / 5751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (162754251 / 1000000000) ≤ -Real.log (4249 / 5000) ∧
    -Real.log (4249 / 5000) ≤ (40688563 / 250000000) := by
  have h := checkLog_sound (w := (751 / 9249)) (n := 12)
    (lo := (162754251 / 1000000000)) (hi := (40688563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4249) = 1/(4249 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-40688563 / 250000000) (-162754251 / 1000000000) (Real.log (4249 / 5000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37547 / 250000000) ≤ -Real.log (5000000 / 5000751) ∧
    -Real.log (5000000 / 5000751) ≤ (150189 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 10000751)) (n := 12)
    (lo := (37547 / 250000000)) (hi := (150189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000751 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000751 / 5000000) = 1/(5000000 / 5000751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (37547 / 250000000) (150189 / 1000000000) (Real.log (5000751 / 5000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5000751 / 5000000) = -Real.log (5000000 / 5000751) := by
    rw [show ((5000751 / 5000000) : ℝ) = ((5000000 / 5000751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_21_neg : (150211 / 1000000000) ≤ -Real.log (4999249 / 5000000) ∧
    -Real.log (4999249 / 5000000) ≤ (37553 / 250000000) := by
  have h := checkLog_sound (w := (751 / 9999249)) (n := 12)
    (lo := (150211 / 1000000000)) (hi := (37553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999249) = 1/(4999249 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_21 : Bounds (-37553 / 250000000) (-150211 / 1000000000) (Real.log (4999249 / 5000000)) := by
  have h := reflection_log_21_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_22_neg : (9072869 / 125000000) ≤ -Real.log (500000 / 537641) ∧
    -Real.log (500000 / 537641) ≤ (72582953 / 1000000000) := by
  have h := checkLog_sound (w := (37641 / 1037641)) (n := 12)
    (lo := (9072869 / 125000000)) (hi := (72582953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537641 / 500000) = 1/(500000 / 537641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_22 : Bounds (9072869 / 125000000) (72582953 / 1000000000) (Real.log (537641 / 500000)) := by
  have h := reflection_log_22_neg
  have he : Real.log (537641 / 500000) = -Real.log (500000 / 537641) := by
    rw [show ((537641 / 500000) : ℝ) = ((500000 / 537641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_23_neg : (19566613 / 250000000) ≤ -Real.log (462359 / 500000) ∧
    -Real.log (462359 / 500000) ≤ (78266453 / 1000000000) := by
  have h := checkLog_sound (w := (37641 / 962359)) (n := 12)
    (lo := (19566613 / 250000000)) (hi := (78266453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462359) = 1/(462359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_23 : Bounds (-78266453 / 1000000000) (-19566613 / 250000000) (Real.log (462359 / 500000)) := by
  have h := reflection_log_23_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_24_neg : (36384931 / 500000000) ≤ -Real.log (1000000 / 1075483) ∧
    -Real.log (1000000 / 1075483) ≤ (72769863 / 1000000000) := by
  have h := checkLog_sound (w := (75483 / 2075483)) (n := 12)
    (lo := (36384931 / 500000000)) (hi := (72769863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075483 / 1000000) = 1/(1000000 / 1075483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_24 : Bounds (36384931 / 500000000) (72769863 / 1000000000) (Real.log (1075483 / 1000000)) := by
  have h := reflection_log_24_neg
  have he : Real.log (1075483 / 1000000) = -Real.log (1000000 / 1075483) := by
    rw [show ((1075483 / 1000000) : ℝ) = ((1000000 / 1075483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_25_neg : (122631 / 1562500) ≤ -Real.log (924517 / 1000000) ∧
    -Real.log (924517 / 1000000) ≤ (78483841 / 1000000000) := by
  have h := checkLog_sound (w := (75483 / 1924517)) (n := 12)
    (lo := (122631 / 1562500)) (hi := (78483841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924517) = 1/(924517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_25 : Bounds (-78483841 / 1000000000) (-122631 / 1562500) (Real.log (924517 / 1000000)) := by
  have h := reflection_log_25_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_26_neg : (5713977 / 1000000000) ≤ -Real.log (994302316711 / 1000000000000) ∧
    -Real.log (994302316711 / 1000000000000) ≤ (2856989 / 500000000) := by
  have h := checkLog_sound (w := (5697683289 / 1994302316711)) (n := 12)
    (lo := (5713977 / 1000000000)) (hi := (2856989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994302316711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994302316711) = 1/(994302316711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_26 : Bounds (-2856989 / 500000000) (-5713977 / 1000000000) (Real.log (994302316711 / 1000000000000)) := by
  have h := reflection_log_26_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_27_neg : (11367 / 2000000) ≤ -Real.log (248583155119 / 250000000000) ∧
    -Real.log (248583155119 / 250000000000) ≤ (5683501 / 1000000000) := by
  have h := checkLog_sound (w := (1416844881 / 498583155119)) (n := 12)
    (lo := (11367 / 2000000)) (hi := (5683501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248583155119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248583155119) = 1/(248583155119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_27 : Bounds (-5683501 / 1000000000) (-11367 / 2000000) (Real.log (248583155119 / 250000000000)) := by
  have h := reflection_log_27_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_28_neg : (30169881 / 200000000) ≤ -Real.log (500000000000 / 581410765227) ∧
    -Real.log (500000000000 / 581410765227) ≤ (75424703 / 500000000) := by
  have h := checkLog_sound (w := (81410765227 / 1081410765227)) (n := 12)
    (lo := (30169881 / 200000000)) (hi := (75424703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581410765227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581410765227 / 500000000000) = 1/(500000000000 / 581410765227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_28 : Bounds (30169881 / 200000000) (75424703 / 500000000) (Real.log (581410765227 / 500000000000)) := by
  have h := reflection_log_28_neg
  have he : Real.log (581410765227 / 500000000000) = -Real.log (500000000000 / 581410765227) := by
    rw [show ((581410765227 / 500000000000) : ℝ) = ((500000000000 / 581410765227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_29_neg : (151253703 / 1000000000) ≤ -Real.log (500000000000 / 581645875631) ∧
    -Real.log (500000000000 / 581645875631) ≤ (18906713 / 125000000) := by
  have h := checkLog_sound (w := (81645875631 / 1081645875631)) (n := 12)
    (lo := (151253703 / 1000000000)) (hi := (18906713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581645875631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581645875631 / 500000000000) = 1/(500000000000 / 581645875631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_29 : Bounds (151253703 / 1000000000) (18906713 / 125000000) (Real.log (581645875631 / 500000000000)) := by
  have h := reflection_log_29_neg
  have he : Real.log (581645875631 / 500000000000) = -Real.log (500000000000 / 581645875631) := by
    rw [show ((581645875631 / 500000000000) : ℝ) = ((500000000000 / 581645875631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_30_neg : (151242739 / 500000000) ≤ -Real.log (20000000000 / 27064360513) ∧
    -Real.log (20000000000 / 27064360513) ≤ (302485479 / 1000000000) := by
  have h := checkLog_sound (w := (7064360513 / 47064360513)) (n := 12)
    (lo := (151242739 / 500000000)) (hi := (302485479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27064360513 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27064360513 / 20000000000) = 1/(20000000000 / 27064360513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_30 : Bounds (151242739 / 500000000) (302485479 / 1000000000) (Real.log (27064360513 / 20000000000)) := by
  have h := reflection_log_30_neg
  have he : Real.log (27064360513 / 20000000000) = -Real.log (20000000000 / 27064360513) := by
    rw [show ((27064360513 / 20000000000) : ℝ) = ((20000000000 / 27064360513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_31_neg : (302690091 / 1000000000) ≤ -Real.log (500000000000 / 676747469993) ∧
    -Real.log (500000000000 / 676747469993) ≤ (75672523 / 250000000) := by
  have h := checkLog_sound (w := (176747469993 / 1176747469993)) (n := 12)
    (lo := (302690091 / 1000000000)) (hi := (75672523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676747469993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676747469993 / 500000000000) = 1/(500000000000 / 676747469993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_31 : Bounds (302690091 / 1000000000) (75672523 / 250000000) (Real.log (676747469993 / 500000000000)) := by
  have h := reflection_log_31_neg
  have he : Real.log (676747469993 / 500000000000) = -Real.log (500000000000 / 676747469993) := by
    rw [show ((676747469993 / 500000000000) : ℝ) = ((500000000000 / 676747469993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_32_neg : (140022777 / 1000000000) ≤ -Real.log (10000 / 11503) ∧
    -Real.log (10000 / 11503) ≤ (70011389 / 500000000) := by
  have h := checkLog_sound (w := (1503 / 21503)) (n := 12)
    (lo := (140022777 / 1000000000)) (hi := (70011389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11503 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11503 / 10000) = 1/(10000 / 11503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_32 : Bounds (140022777 / 1000000000) (70011389 / 500000000) (Real.log (11503 / 10000)) := by
  have h := reflection_log_32_neg
  have he : Real.log (11503 / 10000) = -Real.log (10000 / 11503) := by
    rw [show ((11503 / 10000) : ℝ) = ((10000 / 11503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_33_neg : (40717983 / 250000000) ≤ -Real.log (8497 / 10000) ∧
    -Real.log (8497 / 10000) ≤ (162871933 / 1000000000) := by
  have h := checkLog_sound (w := (1503 / 18497)) (n := 12)
    (lo := (40717983 / 250000000)) (hi := (162871933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8497) = 1/(8497 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_33 : Bounds (-162871933 / 1000000000) (-40717983 / 250000000) (Real.log (8497 / 10000)) := by
  have h := reflection_log_33_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_34_neg : (9393 / 62500000) ≤ -Real.log (10000000 / 10001503) ∧
    -Real.log (10000000 / 10001503) ≤ (150289 / 1000000000) := by
  have h := checkLog_sound (w := (1503 / 20001503)) (n := 12)
    (lo := (9393 / 62500000)) (hi := (150289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001503 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001503 / 10000000) = 1/(10000000 / 10001503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_34 : Bounds (9393 / 62500000) (150289 / 1000000000) (Real.log (10001503 / 10000000)) := by
  have h := reflection_log_34_neg
  have he : Real.log (10001503 / 10000000) = -Real.log (10000000 / 10001503) := by
    rw [show ((10001503 / 10000000) : ℝ) = ((10000000 / 10001503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_35_neg : (150311 / 1000000000) ≤ -Real.log (9998497 / 10000000) ∧
    -Real.log (9998497 / 10000000) ≤ (18789 / 125000000) := by
  have h := checkLog_sound (w := (1503 / 19998497)) (n := 12)
    (lo := (150311 / 1000000000)) (hi := (18789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998497) = 1/(9998497 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_35 : Bounds (-18789 / 125000000) (-150311 / 1000000000) (Real.log (9998497 / 10000000)) := by
  have h := reflection_log_35_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_36_neg : (72629451 / 1000000000) ≤ -Real.log (250000 / 268833) ∧
    -Real.log (250000 / 268833) ≤ (18157363 / 250000000) := by
  have h := checkLog_sound (w := (18833 / 518833)) (n := 12)
    (lo := (72629451 / 1000000000)) (hi := (18157363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268833 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268833 / 250000) = 1/(250000 / 268833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_36 : Bounds (72629451 / 1000000000) (18157363 / 250000000) (Real.log (268833 / 250000)) := by
  have h := reflection_log_36_neg
  have he : Real.log (268833 / 250000) = -Real.log (250000 / 268833) := by
    rw [show ((268833 / 250000) : ℝ) = ((250000 / 268833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_37_neg : (19580131 / 250000000) ≤ -Real.log (231167 / 250000) ∧
    -Real.log (231167 / 250000) ≤ (3132821 / 40000000) := by
  have h := checkLog_sound (w := (18833 / 481167)) (n := 12)
    (lo := (19580131 / 250000000)) (hi := (3132821 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231167) = 1/(231167 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_37 : Bounds (-3132821 / 40000000) (-19580131 / 250000000) (Real.log (231167 / 250000)) := by
  have h := reflection_log_37_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_38_neg : (36408641 / 500000000) ≤ -Real.log (500000 / 537767) ∧
    -Real.log (500000 / 537767) ≤ (72817283 / 1000000000) := by
  have h := checkLog_sound (w := (37767 / 1037767)) (n := 12)
    (lo := (36408641 / 500000000)) (hi := (72817283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537767 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537767 / 500000) = 1/(500000 / 537767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_38 : Bounds (36408641 / 500000000) (72817283 / 1000000000) (Real.log (537767 / 500000)) := by
  have h := reflection_log_38_neg
  have he : Real.log (537767 / 500000) = -Real.log (500000 / 537767) := by
    rw [show ((537767 / 500000) : ℝ) = ((500000 / 537767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_39_neg : (15707801 / 200000000) ≤ -Real.log (462233 / 500000) ∧
    -Real.log (462233 / 500000) ≤ (39269503 / 500000000) := by
  have h := checkLog_sound (w := (37767 / 962233)) (n := 12)
    (lo := (15707801 / 200000000)) (hi := (39269503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462233) = 1/(462233 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_39 : Bounds (-39269503 / 500000000) (-15707801 / 200000000) (Real.log (462233 / 500000)) := by
  have h := reflection_log_39_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_40_neg : (5721723 / 1000000000) ≤ -Real.log (248573653711 / 250000000000) ∧
    -Real.log (248573653711 / 250000000000) ≤ (1430431 / 250000000) := by
  have h := checkLog_sound (w := (1426346289 / 498573653711)) (n := 12)
    (lo := (5721723 / 1000000000)) (hi := (1430431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248573653711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248573653711) = 1/(248573653711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_40 : Bounds (-1430431 / 250000000) (-5721723 / 1000000000) (Real.log (248573653711 / 250000000000)) := by
  have h := reflection_log_40_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_41_neg : (5691073 / 1000000000) ≤ -Real.log (62145318111 / 62500000000) ∧
    -Real.log (62145318111 / 62500000000) ≤ (2845537 / 500000000) := by
  have h := checkLog_sound (w := (354681889 / 124645318111)) (n := 12)
    (lo := (5691073 / 1000000000)) (hi := (2845537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62145318111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62145318111) = 1/(62145318111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_41 : Bounds (-2845537 / 500000000) (-5691073 / 1000000000) (Real.log (62145318111 / 62500000000)) := by
  have h := reflection_log_41_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_42_neg : (6037999 / 40000000) ≤ -Real.log (500000000000 / 581469240851) ∧
    -Real.log (500000000000 / 581469240851) ≤ (18868747 / 125000000) := by
  have h := checkLog_sound (w := (81469240851 / 1081469240851)) (n := 12)
    (lo := (6037999 / 40000000)) (hi := (18868747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581469240851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581469240851 / 500000000000) = 1/(500000000000 / 581469240851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_42 : Bounds (6037999 / 40000000) (18868747 / 125000000) (Real.log (581469240851 / 500000000000)) := by
  have h := reflection_log_42_neg
  have he : Real.log (581469240851 / 500000000000) = -Real.log (500000000000 / 581469240851) := by
    rw [show ((581469240851 / 500000000000) : ℝ) = ((500000000000 / 581469240851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_43_neg : (151356287 / 1000000000) ≤ -Real.log (50000000000 / 58170554677) ∧
    -Real.log (50000000000 / 58170554677) ≤ (1182471 / 7812500) := by
  have h := checkLog_sound (w := (8170554677 / 108170554677)) (n := 12)
    (lo := (151356287 / 1000000000)) (hi := (1182471 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58170554677 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58170554677 / 50000000000) = 1/(50000000000 / 58170554677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_43 : Bounds (151356287 / 1000000000) (1182471 / 7812500) (Real.log (58170554677 / 50000000000)) := by
  have h := reflection_log_43_neg
  have he : Real.log (58170554677 / 50000000000) = -Real.log (50000000000 / 58170554677) := by
    rw [show ((58170554677 / 50000000000) : ℝ) = ((50000000000 / 58170554677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_44_neg : (302690091 / 1000000000) ≤ -Real.log (62500000000 / 84593433749) ∧
    -Real.log (62500000000 / 84593433749) ≤ (75672523 / 250000000) := by
  have h := checkLog_sound (w := (22093433749 / 147093433749)) (n := 12)
    (lo := (302690091 / 1000000000)) (hi := (75672523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84593433749 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84593433749 / 62500000000) = 1/(62500000000 / 84593433749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_44 : Bounds (302690091 / 1000000000) (75672523 / 250000000) (Real.log (84593433749 / 62500000000)) := by
  have h := reflection_log_44_neg
  have he : Real.log (84593433749 / 62500000000) = -Real.log (62500000000 / 84593433749) := by
    rw [show ((84593433749 / 62500000000) : ℝ) = ((62500000000 / 84593433749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_45_neg : (30289471 / 100000000) ≤ -Real.log (500000000000 / 676885959751) ∧
    -Real.log (500000000000 / 676885959751) ≤ (302894711 / 1000000000) := by
  have h := checkLog_sound (w := (176885959751 / 1176885959751)) (n := 12)
    (lo := (30289471 / 100000000)) (hi := (302894711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676885959751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676885959751 / 500000000000) = 1/(500000000000 / 676885959751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_45 : Bounds (30289471 / 100000000) (302894711 / 1000000000) (Real.log (676885959751 / 500000000000)) := by
  have h := reflection_log_45_neg
  have he : Real.log (676885959751 / 500000000000) = -Real.log (500000000000 / 676885959751) := by
    rw [show ((676885959751 / 500000000000) : ℝ) = ((500000000000 / 676885959751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_46_neg : (140109707 / 1000000000) ≤ -Real.log (625 / 719) ∧
    -Real.log (625 / 719) ≤ (35027427 / 250000000) := by
  have h := checkLog_sound (w := (47 / 672)) (n := 12)
    (lo := (140109707 / 1000000000)) (hi := (35027427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719 / 625) = 1/(625 / 719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_46 : Bounds (140109707 / 1000000000) (35027427 / 250000000) (Real.log (719 / 625)) := by
  have h := reflection_log_46_neg
  have he : Real.log (719 / 625) = -Real.log (625 / 719) := by
    rw [show ((719 / 625) : ℝ) = ((625 / 719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_47_neg : (40747407 / 250000000) ≤ -Real.log (531 / 625) ∧
    -Real.log (531 / 625) ≤ (162989629 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 578)) (n := 12)
    (lo := (40747407 / 250000000)) (hi := (162989629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 531) = 1/(531 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_47 : Bounds (-162989629 / 1000000000) (-40747407 / 250000000) (Real.log (531 / 625)) := by
  have h := reflection_log_47_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_48_neg : (37597 / 250000000) ≤ -Real.log (312500 / 312547) ∧
    -Real.log (312500 / 312547) ≤ (150389 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 625047)) (n := 12)
    (lo := (37597 / 250000000)) (hi := (150389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312547 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312547 / 312500) = 1/(312500 / 312547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_48 : Bounds (37597 / 250000000) (150389 / 1000000000) (Real.log (312547 / 312500)) := by
  have h := reflection_log_48_neg
  have he : Real.log (312547 / 312500) = -Real.log (312500 / 312547) := by
    rw [show ((312547 / 312500) : ℝ) = ((312500 / 312547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_49_neg : (150411 / 1000000000) ≤ -Real.log (312453 / 312500) ∧
    -Real.log (312453 / 312500) ≤ (37603 / 250000000) := by
  have h := checkLog_sound (w := (47 / 624953)) (n := 12)
    (lo := (150411 / 1000000000)) (hi := (37603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312453) = 1/(312453 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_49 : Bounds (-37603 / 250000000) (-150411 / 1000000000) (Real.log (312453 / 312500)) := by
  have h := reflection_log_49_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_50_neg : (72676877 / 1000000000) ≤ -Real.log (1000000 / 1075383) ∧
    -Real.log (1000000 / 1075383) ≤ (36338439 / 500000000) := by
  have h := checkLog_sound (w := (75383 / 2075383)) (n := 12)
    (lo := (72676877 / 1000000000)) (hi := (36338439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075383 / 1000000) = 1/(1000000 / 1075383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_50 : Bounds (72676877 / 1000000000) (36338439 / 500000000) (Real.log (1075383 / 1000000)) := by
  have h := reflection_log_50_neg
  have he : Real.log (1075383 / 1000000) = -Real.log (1000000 / 1075383) := by
    rw [show ((1075383 / 1000000) : ℝ) = ((1000000 / 1075383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_51_neg : (78375681 / 1000000000) ≤ -Real.log (924617 / 1000000) ∧
    -Real.log (924617 / 1000000) ≤ (39187841 / 500000000) := by
  have h := checkLog_sound (w := (75383 / 1924617)) (n := 12)
    (lo := (78375681 / 1000000000)) (hi := (39187841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924617) = 1/(924617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_51 : Bounds (-39187841 / 500000000) (-78375681 / 1000000000) (Real.log (924617 / 1000000)) := by
  have h := reflection_log_51_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_52_neg : (72863769 / 1000000000) ≤ -Real.log (15625 / 16806) ∧
    -Real.log (15625 / 16806) ≤ (7286377 / 100000000) := by
  have h := checkLog_sound (w := (1181 / 32431)) (n := 12)
    (lo := (72863769 / 1000000000)) (hi := (7286377 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16806 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16806 / 15625) = 1/(15625 / 16806) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_52 : Bounds (72863769 / 1000000000) (7286377 / 100000000) (Real.log (16806 / 15625)) := by
  have h := reflection_log_52_neg
  have he : Real.log (16806 / 15625) = -Real.log (15625 / 16806) := by
    rw [show ((16806 / 15625) : ℝ) = ((15625 / 16806) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_53_neg : (19648273 / 250000000) ≤ -Real.log (14444 / 15625) ∧
    -Real.log (14444 / 15625) ≤ (78593093 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 30069)) (n := 12)
    (lo := (19648273 / 250000000)) (hi := (78593093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14444) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14444) = 1/(14444 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_53 : Bounds (-78593093 / 1000000000) (-19648273 / 250000000) (Real.log (14444 / 15625)) := by
  have h := reflection_log_53_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_54_neg : (2864661 / 500000000) ≤ -Real.log (242745864 / 244140625) ∧
    -Real.log (242745864 / 244140625) ≤ (5729323 / 1000000000) := by
  have h := checkLog_sound (w := (1394761 / 486886489)) (n := 12)
    (lo := (2864661 / 500000000)) (hi := (5729323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242745864) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242745864) = 1/(242745864 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_54 : Bounds (-5729323 / 1000000000) (-2864661 / 500000000) (Real.log (242745864 / 244140625)) := by
  have h := reflection_log_54_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_55_neg : (1424701 / 250000000) ≤ -Real.log (994317403311 / 1000000000000) ∧
    -Real.log (994317403311 / 1000000000000) ≤ (1139761 / 200000000) := by
  have h := checkLog_sound (w := (5682596689 / 1994317403311)) (n := 12)
    (lo := (1424701 / 250000000)) (hi := (1139761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994317403311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994317403311) = 1/(994317403311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_55 : Bounds (-1139761 / 200000000) (-1424701 / 250000000) (Real.log (994317403311 / 1000000000000)) := by
  have h := reflection_log_55_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_56_neg : (75526279 / 500000000) ≤ -Real.log (500000000000 / 581528892503) ∧
    -Real.log (500000000000 / 581528892503) ≤ (151052559 / 1000000000) := by
  have h := checkLog_sound (w := (81528892503 / 1081528892503)) (n := 12)
    (lo := (75526279 / 500000000)) (hi := (151052559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581528892503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581528892503 / 500000000000) = 1/(500000000000 / 581528892503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_56 : Bounds (75526279 / 500000000) (151052559 / 1000000000) (Real.log (581528892503 / 500000000000)) := by
  have h := reflection_log_56_neg
  have he : Real.log (581528892503 / 500000000000) = -Real.log (500000000000 / 581528892503) := by
    rw [show ((581528892503 / 500000000000) : ℝ) = ((500000000000 / 581528892503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_57_neg : (75728431 / 500000000) ≤ -Real.log (500000000000 / 581764054279) ∧
    -Real.log (500000000000 / 581764054279) ≤ (151456863 / 1000000000) := by
  have h := checkLog_sound (w := (81764054279 / 1081764054279)) (n := 12)
    (lo := (75728431 / 500000000)) (hi := (151456863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581764054279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581764054279 / 500000000000) = 1/(500000000000 / 581764054279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_57 : Bounds (75728431 / 500000000) (151456863 / 1000000000) (Real.log (581764054279 / 500000000000)) := by
  have h := reflection_log_57_neg
  have he : Real.log (581764054279 / 500000000000) = -Real.log (500000000000 / 581764054279) := by
    rw [show ((581764054279 / 500000000000) : ℝ) = ((500000000000 / 581764054279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_58_neg : (30289471 / 100000000) ≤ -Real.log (2000000000 / 2707543839) ∧
    -Real.log (2000000000 / 2707543839) ≤ (302894711 / 1000000000) := by
  have h := checkLog_sound (w := (707543839 / 4707543839)) (n := 12)
    (lo := (30289471 / 100000000)) (hi := (302894711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2707543839 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2707543839 / 2000000000) = 1/(2000000000 / 2707543839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_58 : Bounds (30289471 / 100000000) (302894711 / 1000000000) (Real.log (2707543839 / 2000000000)) := by
  have h := reflection_log_58_neg
  have he : Real.log (2707543839 / 2000000000) = -Real.log (2000000000 / 2707543839) := by
    rw [show ((2707543839 / 2000000000) : ℝ) = ((2000000000 / 2707543839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_59_neg : (37887417 / 125000000) ≤ -Real.log (50000000000 / 67702448211) ∧
    -Real.log (50000000000 / 67702448211) ≤ (303099337 / 1000000000) := by
  have h := checkLog_sound (w := (17702448211 / 117702448211)) (n := 12)
    (lo := (37887417 / 125000000)) (hi := (303099337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67702448211 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67702448211 / 50000000000) = 1/(50000000000 / 67702448211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_59 : Bounds (37887417 / 125000000) (303099337 / 1000000000) (Real.log (67702448211 / 50000000000)) := by
  have h := reflection_log_59_neg
  have he : Real.log (67702448211 / 50000000000) = -Real.log (50000000000 / 67702448211) := by
    rw [show ((67702448211 / 50000000000) : ℝ) = ((50000000000 / 67702448211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_60_neg : (14019663 / 100000000) ≤ -Real.log (2000 / 2301) ∧
    -Real.log (2000 / 2301) ≤ (140196631 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 4301)) (n := 12)
    (lo := (14019663 / 100000000)) (hi := (140196631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2301 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2301 / 2000) = 1/(2000 / 2301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_60 : Bounds (14019663 / 100000000) (140196631 / 1000000000) (Real.log (2301 / 2000)) := by
  have h := reflection_log_60_neg
  have he : Real.log (2301 / 2000) = -Real.log (2000 / 2301) := by
    rw [show ((2301 / 2000) : ℝ) = ((2000 / 2301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_61_neg : (163107337 / 1000000000) ≤ -Real.log (1699 / 2000) ∧
    -Real.log (1699 / 2000) ≤ (81553669 / 500000000) := by
  have h := checkLog_sound (w := (301 / 3699)) (n := 12)
    (lo := (163107337 / 1000000000)) (hi := (81553669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1699) = 1/(1699 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_61 : Bounds (-81553669 / 500000000) (-163107337 / 1000000000) (Real.log (1699 / 2000)) := by
  have h := reflection_log_61_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_62_neg : (18811 / 125000000) ≤ -Real.log (2000000 / 2000301) ∧
    -Real.log (2000000 / 2000301) ≤ (150489 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 4000301)) (n := 12)
    (lo := (18811 / 125000000)) (hi := (150489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000301 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000301 / 2000000) = 1/(2000000 / 2000301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_62 : Bounds (18811 / 125000000) (150489 / 1000000000) (Real.log (2000301 / 2000000)) := by
  have h := reflection_log_62_neg
  have he : Real.log (2000301 / 2000000) = -Real.log (2000000 / 2000301) := by
    rw [show ((2000301 / 2000000) : ℝ) = ((2000000 / 2000301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_63_neg : (150511 / 1000000000) ≤ -Real.log (1999699 / 2000000) ∧
    -Real.log (1999699 / 2000000) ≤ (9407 / 62500000) := by
  have h := checkLog_sound (w := (301 / 3999699)) (n := 12)
    (lo := (150511 / 1000000000)) (hi := (9407 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999699) = 1/(1999699 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_63 : Bounds (-9407 / 62500000) (-150511 / 1000000000) (Real.log (1999699 / 2000000)) := by
  have h := reflection_log_63_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
