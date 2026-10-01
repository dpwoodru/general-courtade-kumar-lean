import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0345
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

theorem reflection_log_1_neg : (213329929 / 1000000000) ≤ -Real.log (2048 / 2535) ∧
    -Real.log (2048 / 2535) ≤ (21332993 / 100000000) := by
  have h := checkLog_sound (w := (487 / 4583)) (n := 12)
    (lo := (213329929 / 1000000000)) (hi := (21332993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2535 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2535 / 2048) = 1/(2048 / 2535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (213329929 / 1000000000) (21332993 / 100000000) (Real.log (2535 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2535 / 2048) = -Real.log (2048 / 2535) := by
    rw [show ((2535 / 2048) : ℝ) = ((2048 / 2535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (54307413 / 200000000) ≤ -Real.log (1561 / 2048) ∧
    -Real.log (1561 / 2048) ≤ (135768533 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3609)) (n := 12)
    (lo := (54307413 / 200000000)) (hi := (135768533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1561) = 1/(1561 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-135768533 / 500000000) (-54307413 / 200000000) (Real.log (1561 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97263789 / 250000000) ≤ -Real.log (1024 / 1511) ∧
    -Real.log (1024 / 1511) ≤ (389055157 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 2535)) (n := 12)
    (lo := (97263789 / 250000000)) (hi := (389055157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 1024) = 1/(1024 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97263789 / 250000000) (389055157 / 1000000000) (Real.log (1511 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1511 / 1024) = -Real.log (1024 / 1511) := by
    rw [show ((1511 / 1024) : ℝ) = ((1024 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (645473711 / 1000000000) ≤ -Real.log (537 / 1024) ∧
    -Real.log (537 / 1024) ≤ (40342107 / 62500000) := by
  have h := checkLog_sound (w := (487 / 1561)) (n := 12)
    (lo := (645473711 / 1000000000)) (hi := (40342107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 537) = 1/(537 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-40342107 / 62500000) (-645473711 / 1000000000) (Real.log (537 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (388657989 / 1000000000) ≤ -Real.log (40 / 59) ∧
    -Real.log (40 / 59) ≤ (38865799 / 100000000) := by
  have h := checkLog_sound (w := (19 / 99)) (n := 12)
    (lo := (388657989 / 1000000000)) (hi := (38865799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 40) = 1/(40 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (388657989 / 1000000000) (38865799 / 100000000) (Real.log (59 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (59 / 40) = -Real.log (40 / 59) := by
    rw [show ((59 / 40) : ℝ) = ((40 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (80544627 / 125000000) ≤ -Real.log (21 / 40) ∧
    -Real.log (21 / 40) ≤ (644357017 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 21) = 1/(21 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-644357017 / 1000000000) (-80544627 / 125000000) (Real.log (21 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (146099677 / 500000000) ≤ -Real.log (100000 / 133937) ∧
    -Real.log (100000 / 133937) ≤ (58439871 / 200000000) := by
  have h := checkLog_sound (w := (33937 / 233937)) (n := 12)
    (lo := (146099677 / 500000000)) (hi := (58439871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133937 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133937 / 100000) = 1/(100000 / 133937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (146099677 / 500000000) (58439871 / 200000000) (Real.log (133937 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (133937 / 100000) = -Real.log (100000 / 133937) := by
    rw [show ((133937 / 100000) : ℝ) = ((100000 / 133937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (414561353 / 1000000000) ≤ -Real.log (66063 / 100000) ∧
    -Real.log (66063 / 100000) ≤ (207280677 / 500000000) := by
  have h := checkLog_sound (w := (33937 / 166063)) (n := 12)
    (lo := (414561353 / 1000000000)) (hi := (207280677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66063) = 1/(66063 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-207280677 / 500000000) (-414561353 / 1000000000) (Real.log (66063 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146259801 / 500000000) ≤ -Real.log (1000000 / 1339799) ∧
    -Real.log (1000000 / 1339799) ≤ (292519603 / 1000000000) := by
  have h := checkLog_sound (w := (339799 / 2339799)) (n := 12)
    (lo := (146259801 / 500000000)) (hi := (292519603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339799 / 1000000) = 1/(1000000 / 1339799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146259801 / 500000000) (292519603 / 1000000000) (Real.log (1339799 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1339799 / 1000000) = -Real.log (1000000 / 1339799) := by
    rw [show ((1339799 / 1000000) : ℝ) = ((1000000 / 1339799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6487671 / 15625000) ≤ -Real.log (660201 / 1000000) ∧
    -Real.log (660201 / 1000000) ≤ (83042189 / 200000000) := by
  have h := checkLog_sound (w := (339799 / 1660201)) (n := 12)
    (lo := (6487671 / 15625000)) (hi := (83042189 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660201) = 1/(660201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83042189 / 200000000) (-6487671 / 15625000) (Real.log (660201 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (221438899 / 1000000000) ≤ -Real.log (1000000 / 1247871) ∧
    -Real.log (1000000 / 1247871) ≤ (2214389 / 10000000) := by
  have h := checkLog_sound (w := (247871 / 2247871)) (n := 12)
    (lo := (221438899 / 1000000000)) (hi := (2214389 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247871 / 1000000) = 1/(1000000 / 1247871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (221438899 / 1000000000) (2214389 / 10000000) (Real.log (1247871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1247871 / 1000000) = -Real.log (1000000 / 1247871) := by
    rw [show ((1247871 / 1000000) : ℝ) = ((1000000 / 1247871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284847427 / 1000000000) ≤ -Real.log (752129 / 1000000) ∧
    -Real.log (752129 / 1000000) ≤ (71211857 / 250000000) := by
  have h := checkLog_sound (w := (247871 / 1752129)) (n := 12)
    (lo := (284847427 / 1000000000)) (hi := (71211857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 752129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 752129) = 1/(752129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-71211857 / 250000000) (-284847427 / 1000000000) (Real.log (752129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (221706519 / 1000000000) ≤ -Real.log (200000 / 249641) ∧
    -Real.log (200000 / 249641) ≤ (5542663 / 25000000) := by
  have h := checkLog_sound (w := (49641 / 449641)) (n := 12)
    (lo := (221706519 / 1000000000)) (hi := (5542663 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249641 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249641 / 200000) = 1/(200000 / 249641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221706519 / 1000000000) (5542663 / 25000000) (Real.log (249641 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (249641 / 200000) = -Real.log (200000 / 249641) := by
    rw [show ((249641 / 200000) : ℝ) = ((200000 / 249641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (142645799 / 500000000) ≤ -Real.log (150359 / 200000) ∧
    -Real.log (150359 / 200000) ≤ (285291599 / 1000000000) := by
  have h := checkLog_sound (w := (49641 / 350359)) (n := 12)
    (lo := (142645799 / 500000000)) (hi := (285291599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150359) = 1/(150359 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-285291599 / 1000000000) (-142645799 / 500000000) (Real.log (150359 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (706760707 / 1000000000) ≤ -Real.log (62500000000 / 126713326673) ∧
    -Real.log (62500000000 / 126713326673) ≤ (706760709 / 1000000000) := by
  have h := checkLog_sound (w := (1713326673 / 251713326673)) (n := 12)
    (lo := (13613527 / 1000000000)) (hi := (1701691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126713326673 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126713326673 / 125000000000) = 1/(62500000000 / 126713326673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (706760707 / 1000000000) (706760709 / 1000000000) (Real.log (126713326673 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126713326673 / 62500000000) = -Real.log (62500000000 / 126713326673) := by
    rw [show ((126713326673 / 62500000000) : ℝ) = ((62500000000 / 126713326673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (707730547 / 1000000000) ≤ -Real.log (50000000000 / 101469022313) ∧
    -Real.log (50000000000 / 101469022313) ≤ (707730549 / 1000000000) := by
  have h := checkLog_sound (w := (1469022313 / 201469022313)) (n := 12)
    (lo := (14583367 / 1000000000)) (hi := (1822921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101469022313 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(101469022313 / 100000000000) = 1/(50000000000 / 101469022313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (707730547 / 1000000000) (707730549 / 1000000000) (Real.log (101469022313 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (101469022313 / 50000000000) = -Real.log (50000000000 / 101469022313) := by
    rw [show ((101469022313 / 50000000000) : ℝ) = ((50000000000 / 101469022313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253143163 / 500000000) ≤ -Real.log (500000000000 / 829559158069) ∧
    -Real.log (500000000000 / 829559158069) ≤ (506286327 / 1000000000) := by
  have h := checkLog_sound (w := (329559158069 / 1329559158069)) (n := 12)
    (lo := (253143163 / 500000000)) (hi := (506286327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829559158069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829559158069 / 500000000000) = 1/(500000000000 / 829559158069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253143163 / 500000000) (506286327 / 1000000000) (Real.log (829559158069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (829559158069 / 500000000000) = -Real.log (500000000000 / 829559158069) := by
    rw [show ((829559158069 / 500000000000) : ℝ) = ((500000000000 / 829559158069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (506998117 / 1000000000) ≤ -Real.log (25000000000 / 41507492069) ∧
    -Real.log (25000000000 / 41507492069) ≤ (253499059 / 500000000) := by
  have h := checkLog_sound (w := (16507492069 / 66507492069)) (n := 12)
    (lo := (506998117 / 1000000000)) (hi := (253499059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41507492069 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41507492069 / 25000000000) = 1/(25000000000 / 41507492069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (506998117 / 1000000000) (253499059 / 500000000) (Real.log (41507492069 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (41507492069 / 25000000000) = -Real.log (25000000000 / 41507492069) := by
    rw [show ((41507492069 / 25000000000) : ℝ) = ((25000000000 / 41507492069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0345
