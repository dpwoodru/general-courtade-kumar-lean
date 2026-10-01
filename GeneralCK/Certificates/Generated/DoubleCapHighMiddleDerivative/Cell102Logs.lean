import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell102
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

theorem reflection_log_1_neg : (270295469 / 1000000000) ≤ -Real.log (5120 / 6709) ∧
    -Real.log (5120 / 6709) ≤ (27029547 / 100000000) := by
  have h := checkLog_sound (w := (1589 / 11829)) (n := 12)
    (lo := (270295469 / 1000000000)) (hi := (27029547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6709 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6709 / 5120) = 1/(5120 / 6709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (270295469 / 1000000000) (27029547 / 100000000) (Real.log (6709 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6709 / 5120) = -Real.log (5120 / 6709) := by
    rw [show ((6709 / 5120) : ℝ) = ((5120 / 6709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (185786661 / 500000000) ≤ -Real.log (3531 / 5120) ∧
    -Real.log (3531 / 5120) ≤ (371573323 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 8651)) (n := 12)
    (lo := (185786661 / 500000000)) (hi := (371573323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3531) = 1/(3531 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-371573323 / 1000000000) (-185786661 / 500000000) (Real.log (3531 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16865513 / 62500000) ≤ -Real.log (2560 / 3353) ∧
    -Real.log (2560 / 3353) ≤ (269848209 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 5913)) (n := 12)
    (lo := (16865513 / 62500000)) (hi := (269848209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3353 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3353 / 2560) = 1/(2560 / 3353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16865513 / 62500000) (269848209 / 1000000000) (Real.log (3353 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3353 / 2560) = -Real.log (2560 / 3353) := by
    rw [show ((3353 / 2560) : ℝ) = ((2560 / 3353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74144813 / 200000000) ≤ -Real.log (1767 / 2560) ∧
    -Real.log (1767 / 2560) ≤ (185362033 / 500000000) := by
  have h := checkLog_sound (w := (793 / 4327)) (n := 12)
    (lo := (74144813 / 200000000)) (hi := (185362033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1767) = 1/(1767 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-185362033 / 500000000) (-74144813 / 200000000) (Real.log (1767 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99404527 / 500000000) ≤ -Real.log (1000000 / 1219949) ∧
    -Real.log (1000000 / 1219949) ≤ (39761811 / 200000000) := by
  have h := checkLog_sound (w := (219949 / 2219949)) (n := 12)
    (lo := (99404527 / 500000000)) (hi := (39761811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219949 / 1000000) = 1/(1000000 / 1219949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99404527 / 500000000) (39761811 / 200000000) (Real.log (1219949 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1219949 / 1000000) = -Real.log (1000000 / 1219949) := by
    rw [show ((1219949 / 1000000) : ℝ) = ((1000000 / 1219949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31049497 / 125000000) ≤ -Real.log (780051 / 1000000) ∧
    -Real.log (780051 / 1000000) ≤ (248395977 / 1000000000) := by
  have h := checkLog_sound (w := (219949 / 1780051)) (n := 12)
    (lo := (31049497 / 125000000)) (hi := (248395977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780051) = 1/(780051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248395977 / 1000000000) (-31049497 / 125000000) (Real.log (780051 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199154091 / 1000000000) ≤ -Real.log (100000 / 122037) ∧
    -Real.log (100000 / 122037) ≤ (49788523 / 250000000) := by
  have h := checkLog_sound (w := (22037 / 222037)) (n := 12)
    (lo := (199154091 / 1000000000)) (hi := (49788523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122037 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122037 / 100000) = 1/(100000 / 122037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199154091 / 1000000000) (49788523 / 250000000) (Real.log (122037 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (122037 / 100000) = -Real.log (100000 / 122037) := by
    rw [show ((122037 / 100000) : ℝ) = ((100000 / 122037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (24893583 / 100000000) ≤ -Real.log (77963 / 100000) ∧
    -Real.log (77963 / 100000) ≤ (248935831 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 177963)) (n := 12)
    (lo := (24893583 / 100000000)) (hi := (248935831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77963) = 1/(77963 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248935831 / 1000000000) (-24893583 / 100000000) (Real.log (77963 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (146384313 / 1000000000) ≤ -Real.log (1000000 / 1157641) ∧
    -Real.log (1000000 / 1157641) ≤ (73192157 / 500000000) := by
  have h := checkLog_sound (w := (157641 / 2157641)) (n := 12)
    (lo := (146384313 / 1000000000)) (hi := (73192157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157641 / 1000000) = 1/(1000000 / 1157641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (146384313 / 1000000000) (73192157 / 500000000) (Real.log (1157641 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1157641 / 1000000) = -Real.log (1000000 / 1157641) := by
    rw [show ((1157641 / 1000000) : ℝ) = ((1000000 / 1157641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (171548989 / 1000000000) ≤ -Real.log (842359 / 1000000) ∧
    -Real.log (842359 / 1000000) ≤ (17154899 / 100000000) := by
  have h := checkLog_sound (w := (157641 / 1842359)) (n := 12)
    (lo := (171548989 / 1000000000)) (hi := (17154899 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842359) = 1/(842359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17154899 / 100000000) (-171548989 / 1000000000) (Real.log (842359 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146652063 / 1000000000) ≤ -Real.log (1000000 / 1157951) ∧
    -Real.log (1000000 / 1157951) ≤ (4582877 / 31250000) := by
  have h := checkLog_sound (w := (157951 / 2157951)) (n := 12)
    (lo := (146652063 / 1000000000)) (hi := (4582877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157951 / 1000000) = 1/(1000000 / 1157951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146652063 / 1000000000) (4582877 / 31250000) (Real.log (1157951 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1157951 / 1000000) = -Real.log (1000000 / 1157951) := by
    rw [show ((1157951 / 1000000) : ℝ) = ((1000000 / 1157951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (171917071 / 1000000000) ≤ -Real.log (842049 / 1000000) ∧
    -Real.log (842049 / 1000000) ≤ (10744817 / 62500000) := by
  have h := checkLog_sound (w := (157951 / 1842049)) (n := 12)
    (lo := (171917071 / 1000000000)) (hi := (10744817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842049) = 1/(842049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10744817 / 62500000) (-171917071 / 1000000000) (Real.log (842049 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (320286137 / 500000000) ≤ -Real.log (500000000000 / 948783248443) ∧
    -Real.log (500000000000 / 948783248443) ≤ (25622891 / 40000000) := by
  have h := checkLog_sound (w := (448783248443 / 1448783248443)) (n := 12)
    (lo := (320286137 / 500000000)) (hi := (25622891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((948783248443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(948783248443 / 500000000000) = 1/(500000000000 / 948783248443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (320286137 / 500000000) (25622891 / 40000000) (Real.log (948783248443 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (948783248443 / 500000000000) = -Real.log (500000000000 / 948783248443) := by
    rw [show ((948783248443 / 500000000000) : ℝ) = ((500000000000 / 948783248443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (641868791 / 1000000000) ≤ -Real.log (100000000000 / 190002832059) ∧
    -Real.log (100000000000 / 190002832059) ≤ (80233599 / 125000000) := by
  have h := checkLog_sound (w := (90002832059 / 290002832059)) (n := 12)
    (lo := (641868791 / 1000000000)) (hi := (80233599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190002832059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190002832059 / 100000000000) = 1/(100000000000 / 190002832059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (641868791 / 1000000000) (80233599 / 125000000) (Real.log (190002832059 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (190002832059 / 100000000000) = -Real.log (100000000000 / 190002832059) := by
    rw [show ((190002832059 / 100000000000) : ℝ) = ((100000000000 / 190002832059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (447205031 / 1000000000) ≤ -Real.log (500000000000 / 781967461101) ∧
    -Real.log (500000000000 / 781967461101) ≤ (55900629 / 125000000) := by
  have h := checkLog_sound (w := (281967461101 / 1281967461101)) (n := 12)
    (lo := (447205031 / 1000000000)) (hi := (55900629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781967461101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781967461101 / 500000000000) = 1/(500000000000 / 781967461101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (447205031 / 1000000000) (55900629 / 125000000) (Real.log (781967461101 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (781967461101 / 500000000000) = -Real.log (500000000000 / 781967461101) := by
    rw [show ((781967461101 / 500000000000) : ℝ) = ((500000000000 / 781967461101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (224044961 / 500000000) ≤ -Real.log (500000000000 / 782659723203) ∧
    -Real.log (500000000000 / 782659723203) ≤ (448089923 / 1000000000) := by
  have h := checkLog_sound (w := (282659723203 / 1282659723203)) (n := 12)
    (lo := (224044961 / 500000000)) (hi := (448089923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782659723203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782659723203 / 500000000000) = 1/(500000000000 / 782659723203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (224044961 / 500000000) (448089923 / 1000000000) (Real.log (782659723203 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (782659723203 / 500000000000) = -Real.log (500000000000 / 782659723203) := by
    rw [show ((782659723203 / 500000000000) : ℝ) = ((500000000000 / 782659723203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (317933303 / 1000000000) ≤ -Real.log (100000000000 / 137428459837) ∧
    -Real.log (100000000000 / 137428459837) ≤ (39741663 / 125000000) := by
  have h := checkLog_sound (w := (37428459837 / 237428459837)) (n := 12)
    (lo := (317933303 / 1000000000)) (hi := (39741663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137428459837 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137428459837 / 100000000000) = 1/(100000000000 / 137428459837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (317933303 / 1000000000) (39741663 / 125000000) (Real.log (137428459837 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (137428459837 / 100000000000) = -Real.log (100000000000 / 137428459837) := by
    rw [show ((137428459837 / 100000000000) : ℝ) = ((100000000000 / 137428459837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (63713827 / 200000000) ≤ -Real.log (100000000000 / 137515869029) ∧
    -Real.log (100000000000 / 137515869029) ≤ (19910571 / 62500000) := by
  have h := checkLog_sound (w := (37515869029 / 237515869029)) (n := 12)
    (lo := (63713827 / 200000000)) (hi := (19910571 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137515869029 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137515869029 / 100000000000) = 1/(100000000000 / 137515869029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (63713827 / 200000000) (19910571 / 62500000) (Real.log (137515869029 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137515869029 / 100000000000) = -Real.log (100000000000 / 137515869029) := by
    rw [show ((137515869029 / 100000000000) : ℝ) = ((100000000000 / 137515869029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25265007 / 1000000000) ≤ -Real.log (975051481599 / 1000000000000) ∧
    -Real.log (975051481599 / 1000000000000) ≤ (1579063 / 62500000) := by
  have h := checkLog_sound (w := (24948518401 / 1975051481599)) (n := 12)
    (lo := (25265007 / 1000000000)) (hi := (1579063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975051481599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975051481599) = 1/(975051481599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1579063 / 62500000) (-25265007 / 1000000000) (Real.log (975051481599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1006587 / 40000000) ≤ -Real.log (975149315119 / 1000000000000) ∧
    -Real.log (975149315119 / 1000000000000) ≤ (6291169 / 250000000) := by
  have h := checkLog_sound (w := (24850684881 / 1975149315119)) (n := 12)
    (lo := (1006587 / 40000000)) (hi := (6291169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975149315119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975149315119) = 1/(975149315119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6291169 / 250000000) (-1006587 / 40000000) (Real.log (975149315119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell102
