import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell038
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

theorem reflection_log_1_neg : (60314927 / 250000000) ≤ -Real.log (5120 / 6517) ∧
    -Real.log (5120 / 6517) ≤ (241259709 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 11637)) (n := 12)
    (lo := (60314927 / 250000000)) (hi := (241259709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6517 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6517 / 5120) = 1/(5120 / 6517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60314927 / 250000000) (241259709 / 1000000000) (Real.log (6517 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6517 / 5120) = -Real.log (5120 / 6517) := by
    rw [show ((6517 / 5120) : ℝ) = ((5120 / 6517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79656161 / 250000000) ≤ -Real.log (3723 / 5120) ∧
    -Real.log (3723 / 5120) ≤ (63724929 / 200000000) := by
  have h := checkLog_sound (w := (1397 / 8843)) (n := 12)
    (lo := (79656161 / 250000000)) (hi := (63724929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3723) = 1/(3723 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63724929 / 200000000) (-79656161 / 250000000) (Real.log (3723 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (240799267 / 1000000000) ≤ -Real.log (2560 / 3257) ∧
    -Real.log (2560 / 3257) ≤ (60199817 / 250000000) := by
  have h := checkLog_sound (w := (697 / 5817)) (n := 12)
    (lo := (240799267 / 1000000000)) (hi := (60199817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2560) = 1/(2560 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (240799267 / 1000000000) (60199817 / 250000000) (Real.log (3257 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3257 / 2560) = -Real.log (2560 / 3257) := by
    rw [show ((3257 / 2560) : ℝ) = ((2560 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (158909583 / 500000000) ≤ -Real.log (1863 / 2560) ∧
    -Real.log (1863 / 2560) ≤ (317819167 / 1000000000) := by
  have h := checkLog_sound (w := (697 / 4423)) (n := 12)
    (lo := (158909583 / 500000000)) (hi := (317819167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1863) = 1/(1863 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-317819167 / 1000000000) (-158909583 / 500000000) (Real.log (1863 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88291729 / 500000000) ≤ -Real.log (500000 / 596567) ∧
    -Real.log (500000 / 596567) ≤ (176583459 / 1000000000) := by
  have h := checkLog_sound (w := (96567 / 1096567)) (n := 12)
    (lo := (88291729 / 500000000)) (hi := (176583459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596567 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596567 / 500000) = 1/(500000 / 596567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88291729 / 500000000) (176583459 / 1000000000) (Real.log (596567 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (596567 / 500000) = -Real.log (500000 / 596567) := by
    rw [show ((596567 / 500000) : ℝ) = ((500000 / 596567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214597671 / 1000000000) ≤ -Real.log (403433 / 500000) ∧
    -Real.log (403433 / 500000) ≤ (26824709 / 125000000) := by
  have h := checkLog_sound (w := (96567 / 903433)) (n := 12)
    (lo := (214597671 / 1000000000)) (hi := (26824709 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403433) = 1/(403433 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26824709 / 125000000) (-214597671 / 1000000000) (Real.log (403433 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (176934573 / 1000000000) ≤ -Real.log (1000000 / 1193553) ∧
    -Real.log (1000000 / 1193553) ≤ (88467287 / 500000000) := by
  have h := checkLog_sound (w := (193553 / 2193553)) (n := 12)
    (lo := (176934573 / 1000000000)) (hi := (88467287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193553 / 1000000) = 1/(1000000 / 1193553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (176934573 / 1000000000) (88467287 / 500000000) (Real.log (1193553 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1193553 / 1000000) = -Real.log (1000000 / 1193553) := by
    rw [show ((1193553 / 1000000) : ℝ) = ((1000000 / 1193553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (215117099 / 1000000000) ≤ -Real.log (806447 / 1000000) ∧
    -Real.log (806447 / 1000000) ≤ (2151171 / 10000000) := by
  have h := checkLog_sound (w := (193553 / 1806447)) (n := 12)
    (lo := (215117099 / 1000000000)) (hi := (2151171 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806447) = 1/(806447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2151171 / 10000000) (-215117099 / 1000000000) (Real.log (806447 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16158273 / 125000000) ≤ -Real.log (1000000 / 1137993) ∧
    -Real.log (1000000 / 1137993) ≤ (25853237 / 200000000) := by
  have h := checkLog_sound (w := (137993 / 2137993)) (n := 12)
    (lo := (16158273 / 125000000)) (hi := (25853237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137993 / 1000000) = 1/(1000000 / 1137993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16158273 / 125000000) (25853237 / 200000000) (Real.log (1137993 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1137993 / 1000000) = -Real.log (1000000 / 1137993) := by
    rw [show ((1137993 / 1000000) : ℝ) = ((1000000 / 1137993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (148491887 / 1000000000) ≤ -Real.log (862007 / 1000000) ∧
    -Real.log (862007 / 1000000) ≤ (9280743 / 62500000) := by
  have h := checkLog_sound (w := (137993 / 1862007)) (n := 12)
    (lo := (148491887 / 1000000000)) (hi := (9280743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862007) = 1/(862007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9280743 / 62500000) (-148491887 / 1000000000) (Real.log (862007 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64767521 / 500000000) ≤ -Real.log (1000000 / 1138299) ∧
    -Real.log (1000000 / 1138299) ≤ (129535043 / 1000000000) := by
  have h := checkLog_sound (w := (138299 / 2138299)) (n := 12)
    (lo := (64767521 / 500000000)) (hi := (129535043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138299 / 1000000) = 1/(1000000 / 1138299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64767521 / 500000000) (129535043 / 1000000000) (Real.log (1138299 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1138299 / 1000000) = -Real.log (1000000 / 1138299) := by
    rw [show ((1138299 / 1000000) : ℝ) = ((1000000 / 1138299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18605867 / 125000000) ≤ -Real.log (861701 / 1000000) ∧
    -Real.log (861701 / 1000000) ≤ (148846937 / 1000000000) := by
  have h := checkLog_sound (w := (138299 / 1861701)) (n := 12)
    (lo := (18605867 / 125000000)) (hi := (148846937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861701) = 1/(861701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-148846937 / 1000000000) (-18605867 / 125000000) (Real.log (861701 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (279309217 / 500000000) ≤ -Real.log (500000000000 / 874127750939) ∧
    -Real.log (500000000000 / 874127750939) ≤ (111723687 / 200000000) := by
  have h := checkLog_sound (w := (374127750939 / 1374127750939)) (n := 12)
    (lo := (279309217 / 500000000)) (hi := (111723687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((874127750939 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(874127750939 / 500000000000) = 1/(500000000000 / 874127750939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (279309217 / 500000000) (111723687 / 200000000) (Real.log (874127750939 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (874127750939 / 500000000000) = -Real.log (500000000000 / 874127750939) := by
    rw [show ((874127750939 / 500000000000) : ℝ) = ((500000000000 / 874127750939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8748193 / 15625000) ≤ -Real.log (250000000000 / 437617512759) ∧
    -Real.log (250000000000 / 437617512759) ≤ (559884353 / 1000000000) := by
  have h := checkLog_sound (w := (187617512759 / 687617512759)) (n := 12)
    (lo := (8748193 / 15625000)) (hi := (559884353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437617512759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437617512759 / 250000000000) = 1/(250000000000 / 437617512759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (8748193 / 15625000) (559884353 / 1000000000) (Real.log (437617512759 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (437617512759 / 250000000000) = -Real.log (250000000000 / 437617512759) := by
    rw [show ((437617512759 / 250000000000) : ℝ) = ((250000000000 / 437617512759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (39118113 / 100000000) ≤ -Real.log (50000000000 / 73936316563) ∧
    -Real.log (50000000000 / 73936316563) ≤ (391181131 / 1000000000) := by
  have h := checkLog_sound (w := (23936316563 / 123936316563)) (n := 12)
    (lo := (39118113 / 100000000)) (hi := (391181131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73936316563 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73936316563 / 50000000000) = 1/(50000000000 / 73936316563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39118113 / 100000000) (391181131 / 1000000000) (Real.log (73936316563 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (73936316563 / 50000000000) = -Real.log (50000000000 / 73936316563) := by
    rw [show ((73936316563 / 50000000000) : ℝ) = ((50000000000 / 73936316563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49006459 / 125000000) ≤ -Real.log (500000000000 / 740007092841) ∧
    -Real.log (500000000000 / 740007092841) ≤ (392051673 / 1000000000) := by
  have h := checkLog_sound (w := (240007092841 / 1240007092841)) (n := 12)
    (lo := (49006459 / 125000000)) (hi := (392051673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740007092841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740007092841 / 500000000000) = 1/(500000000000 / 740007092841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (49006459 / 125000000) (392051673 / 1000000000) (Real.log (740007092841 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (740007092841 / 500000000000) = -Real.log (500000000000 / 740007092841) := by
    rw [show ((740007092841 / 500000000000) : ℝ) = ((500000000000 / 740007092841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (34719759 / 125000000) ≤ -Real.log (500000000000 / 660083386793) ∧
    -Real.log (500000000000 / 660083386793) ≤ (277758073 / 1000000000) := by
  have h := checkLog_sound (w := (160083386793 / 1160083386793)) (n := 12)
    (lo := (34719759 / 125000000)) (hi := (277758073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660083386793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660083386793 / 500000000000) = 1/(500000000000 / 660083386793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (34719759 / 125000000) (277758073 / 1000000000) (Real.log (660083386793 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (660083386793 / 500000000000) = -Real.log (500000000000 / 660083386793) := by
    rw [show ((660083386793 / 500000000000) : ℝ) = ((500000000000 / 660083386793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (278381979 / 1000000000) ≤ -Real.log (250000000000 / 330247672917) ∧
    -Real.log (250000000000 / 330247672917) ≤ (13919099 / 50000000) := by
  have h := checkLog_sound (w := (80247672917 / 580247672917)) (n := 12)
    (lo := (278381979 / 1000000000)) (hi := (13919099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330247672917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330247672917 / 250000000000) = 1/(250000000000 / 330247672917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (278381979 / 1000000000) (13919099 / 50000000) (Real.log (330247672917 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330247672917 / 250000000000) = -Real.log (250000000000 / 330247672917) := by
    rw [show ((330247672917 / 250000000000) : ℝ) = ((250000000000 / 330247672917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19311893 / 1000000000) ≤ -Real.log (980873386599 / 1000000000000) ∧
    -Real.log (980873386599 / 1000000000000) ≤ (9655947 / 500000000) := by
  have h := checkLog_sound (w := (19126613401 / 1980873386599)) (n := 12)
    (lo := (19311893 / 1000000000)) (hi := (9655947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980873386599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980873386599) = 1/(980873386599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9655947 / 500000000) (-19311893 / 1000000000) (Real.log (980873386599 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19225703 / 1000000000) ≤ -Real.log (980957931951 / 1000000000000) ∧
    -Real.log (980957931951 / 1000000000000) ≤ (2403213 / 125000000) := by
  have h := checkLog_sound (w := (19042068049 / 1980957931951)) (n := 12)
    (lo := (19225703 / 1000000000)) (hi := (2403213 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980957931951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980957931951) = 1/(980957931951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2403213 / 125000000) (-19225703 / 1000000000) (Real.log (980957931951 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell038
