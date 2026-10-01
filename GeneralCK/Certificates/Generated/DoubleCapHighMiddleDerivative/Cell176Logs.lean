import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell176
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

theorem reflection_log_1_neg : (302849663 / 1000000000) ≤ -Real.log (5120 / 6931) ∧
    -Real.log (5120 / 6931) ≤ (2366013 / 7812500) := by
  have h := checkLog_sound (w := (1811 / 12051)) (n := 12)
    (lo := (302849663 / 1000000000)) (hi := (2366013 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6931 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6931 / 5120) = 1/(5120 / 6931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (302849663 / 1000000000) (2366013 / 7812500) (Real.log (6931 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6931 / 5120) = -Real.log (5120 / 6931) := by
    rw [show ((6931 / 5120) : ℝ) = ((5120 / 6931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (43650841 / 100000000) ≤ -Real.log (3309 / 5120) ∧
    -Real.log (3309 / 5120) ≤ (436508411 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 8429)) (n := 12)
    (lo := (43650841 / 100000000)) (hi := (436508411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3309) = 1/(3309 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-436508411 / 1000000000) (-43650841 / 100000000) (Real.log (3309 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (75604183 / 250000000) ≤ -Real.log (320 / 433) ∧
    -Real.log (320 / 433) ≤ (302416733 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 753)) (n := 12)
    (lo := (75604183 / 250000000)) (hi := (302416733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433 / 320) = 1/(320 / 433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (75604183 / 250000000) (302416733 / 1000000000) (Real.log (433 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (433 / 320) = -Real.log (320 / 433) := by
    rw [show ((433 / 320) : ℝ) = ((320 / 433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (217801101 / 500000000) ≤ -Real.log (207 / 320) ∧
    -Real.log (207 / 320) ≤ (435602203 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 207) = 1/(207 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-435602203 / 1000000000) (-217801101 / 500000000) (Real.log (207 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (223995987 / 1000000000) ≤ -Real.log (500000 / 625533) ∧
    -Real.log (500000 / 625533) ≤ (55998997 / 250000000) := by
  have h := checkLog_sound (w := (125533 / 1125533)) (n := 12)
    (lo := (223995987 / 1000000000)) (hi := (55998997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625533 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625533 / 500000) = 1/(500000 / 625533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (223995987 / 1000000000) (55998997 / 250000000) (Real.log (625533 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (625533 / 500000) = -Real.log (500000 / 625533) := by
    rw [show ((625533 / 500000) : ℝ) = ((500000 / 625533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9034513 / 31250000) ≤ -Real.log (374467 / 500000) ∧
    -Real.log (374467 / 500000) ≤ (289104417 / 1000000000) := by
  have h := checkLog_sound (w := (125533 / 874467)) (n := 12)
    (lo := (9034513 / 31250000)) (hi := (289104417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374467) = 1/(374467 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-289104417 / 1000000000) (-9034513 / 31250000) (Real.log (374467 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224333243 / 1000000000) ≤ -Real.log (31250 / 39109) ∧
    -Real.log (31250 / 39109) ≤ (56083311 / 250000000) := by
  have h := checkLog_sound (w := (7859 / 70359)) (n := 12)
    (lo := (224333243 / 1000000000)) (hi := (56083311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39109 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39109 / 31250) = 1/(31250 / 39109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224333243 / 1000000000) (56083311 / 250000000) (Real.log (39109 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (39109 / 31250) = -Real.log (31250 / 39109) := by
    rw [show ((39109 / 31250) : ℝ) = ((31250 / 39109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (289668043 / 1000000000) ≤ -Real.log (23391 / 31250) ∧
    -Real.log (23391 / 31250) ≤ (72417011 / 250000000) := by
  have h := checkLog_sound (w := (7859 / 54641)) (n := 12)
    (lo := (289668043 / 1000000000)) (hi := (72417011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23391) = 1/(23391 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72417011 / 250000000) (-289668043 / 1000000000) (Real.log (23391 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (83047389 / 500000000) ≤ -Real.log (200000 / 236137) ∧
    -Real.log (200000 / 236137) ≤ (166094779 / 1000000000) := by
  have h := checkLog_sound (w := (36137 / 436137)) (n := 12)
    (lo := (83047389 / 500000000)) (hi := (166094779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236137 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236137 / 200000) = 1/(200000 / 236137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (83047389 / 500000000) (166094779 / 1000000000) (Real.log (236137 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236137 / 200000) = -Real.log (200000 / 236137) := by
    rw [show ((236137 / 200000) : ℝ) = ((200000 / 236137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199286653 / 1000000000) ≤ -Real.log (163863 / 200000) ∧
    -Real.log (163863 / 200000) ≤ (99643327 / 500000000) := by
  have h := checkLog_sound (w := (36137 / 363863)) (n := 12)
    (lo := (199286653 / 1000000000)) (hi := (99643327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163863) = 1/(163863 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-99643327 / 500000000) (-199286653 / 1000000000) (Real.log (163863 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166361537 / 1000000000) ≤ -Real.log (1000 / 1181) ∧
    -Real.log (1000 / 1181) ≤ (83180769 / 500000000) := by
  have h := checkLog_sound (w := (181 / 2181)) (n := 12)
    (lo := (166361537 / 1000000000)) (hi := (83180769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 1000) = 1/(1000 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166361537 / 1000000000) (83180769 / 500000000) (Real.log (1181 / 1000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181 / 1000) = -Real.log (1000 / 1181) := by
    rw [show ((1181 / 1000) : ℝ) = ((1000 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39934239 / 200000000) ≤ -Real.log (819 / 1000) ∧
    -Real.log (819 / 1000) ≤ (49917799 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1819)) (n := 12)
    (lo := (39934239 / 200000000)) (hi := (49917799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 819) = 1/(819 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49917799 / 250000000) (-39934239 / 200000000) (Real.log (819 / 1000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (369009467 / 500000000) ≤ -Real.log (250000000000 / 522946859903) ∧
    -Real.log (250000000000 / 522946859903) ≤ (92252367 / 125000000) := by
  have h := checkLog_sound (w := (22946859903 / 1022946859903)) (n := 12)
    (lo := (22435877 / 500000000)) (hi := (8974351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522946859903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(522946859903 / 500000000000) = 1/(250000000000 / 522946859903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (369009467 / 500000000) (92252367 / 125000000) (Real.log (522946859903 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (522946859903 / 250000000000) = -Real.log (250000000000 / 522946859903) := by
    rw [show ((522946859903 / 250000000000) : ℝ) = ((250000000000 / 522946859903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (739358073 / 1000000000) ≤ -Real.log (100000000000 / 209459051073) ∧
    -Real.log (100000000000 / 209459051073) ≤ (29574323 / 40000000) := by
  have h := checkLog_sound (w := (9459051073 / 409459051073)) (n := 12)
    (lo := (46210893 / 1000000000)) (hi := (23105447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209459051073 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209459051073 / 200000000000) = 1/(100000000000 / 209459051073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (739358073 / 1000000000) (29574323 / 40000000) (Real.log (209459051073 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (209459051073 / 100000000000) = -Real.log (100000000000 / 209459051073) := by
    rw [show ((209459051073 / 100000000000) : ℝ) = ((100000000000 / 209459051073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (128275101 / 250000000) ≤ -Real.log (250000000000 / 417615570931) ∧
    -Real.log (250000000000 / 417615570931) ≤ (102620081 / 200000000) := by
  have h := checkLog_sound (w := (167615570931 / 667615570931)) (n := 12)
    (lo := (128275101 / 250000000)) (hi := (102620081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417615570931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417615570931 / 250000000000) = 1/(250000000000 / 417615570931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (128275101 / 250000000) (102620081 / 200000000) (Real.log (417615570931 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (417615570931 / 250000000000) = -Real.log (250000000000 / 417615570931) := by
    rw [show ((417615570931 / 250000000000) : ℝ) = ((250000000000 / 417615570931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (257000643 / 500000000) ≤ -Real.log (250000000000 / 417991962721) ∧
    -Real.log (250000000000 / 417991962721) ≤ (514001287 / 1000000000) := by
  have h := checkLog_sound (w := (167991962721 / 667991962721)) (n := 12)
    (lo := (257000643 / 500000000)) (hi := (514001287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417991962721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417991962721 / 250000000000) = 1/(250000000000 / 417991962721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (257000643 / 500000000) (514001287 / 1000000000) (Real.log (417991962721 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (417991962721 / 250000000000) = -Real.log (250000000000 / 417991962721) := by
    rw [show ((417991962721 / 250000000000) : ℝ) = ((250000000000 / 417991962721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45672679 / 125000000) ≤ -Real.log (500000000000 / 720531785699) ∧
    -Real.log (500000000000 / 720531785699) ≤ (365381433 / 1000000000) := by
  have h := checkLog_sound (w := (220531785699 / 1220531785699)) (n := 12)
    (lo := (45672679 / 125000000)) (hi := (365381433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720531785699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720531785699 / 500000000000) = 1/(500000000000 / 720531785699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45672679 / 125000000) (365381433 / 1000000000) (Real.log (720531785699 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (720531785699 / 500000000000) = -Real.log (500000000000 / 720531785699) := by
    rw [show ((720531785699 / 500000000000) : ℝ) = ((500000000000 / 720531785699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (91508183 / 250000000) ≤ -Real.log (250000000000 / 360500610501) ∧
    -Real.log (250000000000 / 360500610501) ≤ (366032733 / 1000000000) := by
  have h := checkLog_sound (w := (110500610501 / 610500610501)) (n := 12)
    (lo := (91508183 / 250000000)) (hi := (366032733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360500610501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360500610501 / 250000000000) = 1/(250000000000 / 360500610501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (91508183 / 250000000) (366032733 / 1000000000) (Real.log (360500610501 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (360500610501 / 250000000000) = -Real.log (250000000000 / 360500610501) := by
    rw [show ((360500610501 / 250000000000) : ℝ) = ((250000000000 / 360500610501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33309657 / 1000000000) ≤ -Real.log (967239 / 1000000) ∧
    -Real.log (967239 / 1000000) ≤ (16654829 / 500000000) := by
  have h := checkLog_sound (w := (32761 / 1967239)) (n := 12)
    (lo := (33309657 / 1000000000)) (hi := (16654829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 967239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 967239) = 1/(967239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16654829 / 500000000) (-33309657 / 1000000000) (Real.log (967239 / 1000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (53107 / 1600000) ≤ -Real.log (38694117231 / 40000000000) ∧
    -Real.log (38694117231 / 40000000000) ≤ (8297969 / 250000000) := by
  have h := checkLog_sound (w := (1305882769 / 78694117231)) (n := 12)
    (lo := (53107 / 1600000)) (hi := (8297969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38694117231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38694117231) = 1/(38694117231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8297969 / 250000000) (-53107 / 1600000) (Real.log (38694117231 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell176
