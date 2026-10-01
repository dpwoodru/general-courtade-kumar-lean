import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell169
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

theorem reflection_log_1_neg : (149907599 / 500000000) ≤ -Real.log (512 / 691) ∧
    -Real.log (512 / 691) ≤ (299815199 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1203)) (n := 12)
    (lo := (149907599 / 500000000)) (hi := (299815199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 512) = 1/(512 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (149907599 / 500000000) (299815199 / 1000000000) (Real.log (691 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (691 / 512) = -Real.log (512 / 691) := by
    rw [show ((691 / 512) : ℝ) = ((512 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86036427 / 200000000) ≤ -Real.log (333 / 512) ∧
    -Real.log (333 / 512) ≤ (53772767 / 125000000) := by
  have h := checkLog_sound (w := (179 / 845)) (n := 12)
    (lo := (86036427 / 200000000)) (hi := (53772767 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 333) = 1/(333 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-53772767 / 125000000) (-86036427 / 200000000) (Real.log (333 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (299380951 / 1000000000) ≤ -Real.log (5120 / 6907) ∧
    -Real.log (5120 / 6907) ≤ (37422619 / 125000000) := by
  have h := checkLog_sound (w := (1787 / 12027)) (n := 12)
    (lo := (299380951 / 1000000000)) (hi := (37422619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6907 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6907 / 5120) = 1/(5120 / 6907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (299380951 / 1000000000) (37422619 / 125000000) (Real.log (6907 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6907 / 5120) = -Real.log (5120 / 6907) := by
    rw [show ((6907 / 5120) : ℝ) = ((5120 / 6907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (429281639 / 1000000000) ≤ -Real.log (3333 / 5120) ∧
    -Real.log (3333 / 5120) ≤ (10732041 / 25000000) := by
  have h := checkLog_sound (w := (1787 / 8453)) (n := 12)
    (lo := (429281639 / 1000000000)) (hi := (10732041 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3333) = 1/(3333 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-10732041 / 25000000) (-429281639 / 1000000000) (Real.log (3333 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44327203 / 200000000) ≤ -Real.log (1000000 / 1248117) ∧
    -Real.log (1000000 / 1248117) ≤ (13852251 / 62500000) := by
  have h := checkLog_sound (w := (248117 / 2248117)) (n := 12)
    (lo := (44327203 / 200000000)) (hi := (13852251 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248117 / 1000000) = 1/(1000000 / 1248117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44327203 / 200000000) (13852251 / 62500000) (Real.log (1248117 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1248117 / 1000000) = -Real.log (1000000 / 1248117) := by
    rw [show ((1248117 / 1000000) : ℝ) = ((1000000 / 1248117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35646819 / 125000000) ≤ -Real.log (751883 / 1000000) ∧
    -Real.log (751883 / 1000000) ≤ (285174553 / 1000000000) := by
  have h := checkLog_sound (w := (248117 / 1751883)) (n := 12)
    (lo := (35646819 / 125000000)) (hi := (285174553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751883) = 1/(751883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-285174553 / 1000000000) (-35646819 / 125000000) (Real.log (751883 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (221974067 / 1000000000) ≤ -Real.log (1000000 / 1248539) ∧
    -Real.log (1000000 / 1248539) ≤ (55493517 / 250000000) := by
  have h := checkLog_sound (w := (248539 / 2248539)) (n := 12)
    (lo := (221974067 / 1000000000)) (hi := (55493517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248539 / 1000000) = 1/(1000000 / 1248539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (221974067 / 1000000000) (55493517 / 250000000) (Real.log (1248539 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1248539 / 1000000) = -Real.log (1000000 / 1248539) := by
    rw [show ((1248539 / 1000000) : ℝ) = ((1000000 / 1248539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (285735967 / 1000000000) ≤ -Real.log (751461 / 1000000) ∧
    -Real.log (751461 / 1000000) ≤ (8929249 / 31250000) := by
  have h := checkLog_sound (w := (248539 / 1751461)) (n := 12)
    (lo := (285735967 / 1000000000)) (hi := (8929249 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751461) = 1/(751461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8929249 / 31250000) (-285735967 / 1000000000) (Real.log (751461 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164233109 / 1000000000) ≤ -Real.log (1000000 / 1178489) ∧
    -Real.log (1000000 / 1178489) ≤ (16423311 / 100000000) := by
  have h := checkLog_sound (w := (178489 / 2178489)) (n := 12)
    (lo := (164233109 / 1000000000)) (hi := (16423311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178489 / 1000000) = 1/(1000000 / 1178489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164233109 / 1000000000) (16423311 / 100000000) (Real.log (1178489 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1178489 / 1000000) = -Real.log (1000000 / 1178489) := by
    rw [show ((1178489 / 1000000) : ℝ) = ((1000000 / 1178489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196609951 / 1000000000) ≤ -Real.log (821511 / 1000000) ∧
    -Real.log (821511 / 1000000) ≤ (6144061 / 31250000) := by
  have h := checkLog_sound (w := (178489 / 1821511)) (n := 12)
    (lo := (196609951 / 1000000000)) (hi := (6144061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821511) = 1/(821511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6144061 / 31250000) (-196609951 / 1000000000) (Real.log (821511 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41124879 / 250000000) ≤ -Real.log (1000000 / 1178803) ∧
    -Real.log (1000000 / 1178803) ≤ (164499517 / 1000000000) := by
  have h := checkLog_sound (w := (178803 / 2178803)) (n := 12)
    (lo := (41124879 / 250000000)) (hi := (164499517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178803 / 1000000) = 1/(1000000 / 1178803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41124879 / 250000000) (164499517 / 1000000000) (Real.log (1178803 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1178803 / 1000000) = -Real.log (1000000 / 1178803) := by
    rw [show ((1178803 / 1000000) : ℝ) = ((1000000 / 1178803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (196992247 / 1000000000) ≤ -Real.log (821197 / 1000000) ∧
    -Real.log (821197 / 1000000) ≤ (24624031 / 125000000) := by
  have h := checkLog_sound (w := (178803 / 1821197)) (n := 12)
    (lo := (196992247 / 1000000000)) (hi := (24624031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821197) = 1/(821197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24624031 / 125000000) (-196992247 / 1000000000) (Real.log (821197 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72866259 / 100000000) ≤ -Real.log (500000000000 / 1036153615361) ∧
    -Real.log (500000000000 / 1036153615361) ≤ (11385353 / 15625000) := by
  have h := checkLog_sound (w := (36153615361 / 2036153615361)) (n := 12)
    (lo := (3551541 / 100000000)) (hi := (35515411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036153615361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036153615361 / 1000000000000) = 1/(500000000000 / 1036153615361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72866259 / 100000000) (11385353 / 15625000) (Real.log (1036153615361 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1036153615361 / 500000000000) = -Real.log (500000000000 / 1036153615361) := by
    rw [show ((1036153615361 / 500000000000) : ℝ) = ((500000000000 / 1036153615361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (729997333 / 1000000000) ≤ -Real.log (250000000000 / 518768768769) ∧
    -Real.log (250000000000 / 518768768769) ≤ (145999467 / 200000000) := by
  have h := checkLog_sound (w := (18768768769 / 1018768768769)) (n := 12)
    (lo := (36850153 / 1000000000)) (hi := (18425077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518768768769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518768768769 / 500000000000) = 1/(250000000000 / 518768768769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (729997333 / 1000000000) (145999467 / 200000000) (Real.log (518768768769 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (518768768769 / 250000000000) = -Real.log (250000000000 / 518768768769) := by
    rw [show ((518768768769 / 250000000000) : ℝ) = ((250000000000 / 518768768769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (506810567 / 1000000000) ≤ -Real.log (20000000000 / 33199766453) ∧
    -Real.log (20000000000 / 33199766453) ≤ (63351321 / 125000000) := by
  have h := checkLog_sound (w := (13199766453 / 53199766453)) (n := 12)
    (lo := (506810567 / 1000000000)) (hi := (63351321 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33199766453 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33199766453 / 20000000000) = 1/(20000000000 / 33199766453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (506810567 / 1000000000) (63351321 / 125000000) (Real.log (33199766453 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (33199766453 / 20000000000) = -Real.log (20000000000 / 33199766453) := by
    rw [show ((33199766453 / 20000000000) : ℝ) = ((20000000000 / 33199766453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101542007 / 200000000) ≤ -Real.log (500000000000 / 830741049769) ∧
    -Real.log (500000000000 / 830741049769) ≤ (126927509 / 250000000) := by
  have h := checkLog_sound (w := (330741049769 / 1330741049769)) (n := 12)
    (lo := (101542007 / 200000000)) (hi := (126927509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830741049769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830741049769 / 500000000000) = 1/(500000000000 / 830741049769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101542007 / 200000000) (126927509 / 250000000) (Real.log (830741049769 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (830741049769 / 500000000000) = -Real.log (500000000000 / 830741049769) := by
    rw [show ((830741049769 / 500000000000) : ℝ) = ((500000000000 / 830741049769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (18042153 / 50000000) ≤ -Real.log (250000000000 / 358634577017) ∧
    -Real.log (250000000000 / 358634577017) ≤ (360843061 / 1000000000) := by
  have h := checkLog_sound (w := (108634577017 / 608634577017)) (n := 12)
    (lo := (18042153 / 50000000)) (hi := (360843061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358634577017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358634577017 / 250000000000) = 1/(250000000000 / 358634577017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18042153 / 50000000) (360843061 / 1000000000) (Real.log (358634577017 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (358634577017 / 250000000000) = -Real.log (250000000000 / 358634577017) := by
    rw [show ((358634577017 / 250000000000) : ℝ) = ((250000000000 / 358634577017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (361491763 / 1000000000) ≤ -Real.log (100000000000 / 143546919923) ∧
    -Real.log (100000000000 / 143546919923) ≤ (90372941 / 250000000) := by
  have h := checkLog_sound (w := (43546919923 / 243546919923)) (n := 12)
    (lo := (361491763 / 1000000000)) (hi := (90372941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143546919923 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143546919923 / 100000000000) = 1/(100000000000 / 143546919923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (361491763 / 1000000000) (90372941 / 250000000) (Real.log (143546919923 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (143546919923 / 100000000000) = -Real.log (100000000000 / 143546919923) := by
    rw [show ((143546919923 / 100000000000) : ℝ) = ((100000000000 / 143546919923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3249273 / 100000000) ≤ -Real.log (968029487191 / 1000000000000) ∧
    -Real.log (968029487191 / 1000000000000) ≤ (32492731 / 1000000000) := by
  have h := checkLog_sound (w := (31970512809 / 1968029487191)) (n := 12)
    (lo := (3249273 / 100000000)) (hi := (32492731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968029487191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968029487191) = 1/(968029487191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32492731 / 1000000000) (-3249273 / 100000000) (Real.log (968029487191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16188421 / 500000000) ≤ -Real.log (968141676879 / 1000000000000) ∧
    -Real.log (968141676879 / 1000000000000) ≤ (32376843 / 1000000000) := by
  have h := checkLog_sound (w := (31858323121 / 1968141676879)) (n := 12)
    (lo := (16188421 / 500000000)) (hi := (32376843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968141676879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968141676879) = 1/(968141676879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32376843 / 1000000000) (-16188421 / 500000000) (Real.log (968141676879 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell169
