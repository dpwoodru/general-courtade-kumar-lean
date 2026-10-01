import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0004
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

theorem reflection_log_1_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_1_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10753943 / 25000000) ≤ -Real.log (80 / 123) ∧
    -Real.log (80 / 123) ≤ (430157721 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 203)) (n := 12)
    (lo := (10753943 / 25000000)) (hi := (430157721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 80) = 1/(80 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10753943 / 25000000) (430157721 / 1000000000) (Real.log (123 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (123 / 80) = -Real.log (80 / 123) := by
    rw [show ((123 / 80) : ℝ) = ((80 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (771108721 / 1000000000) ≤ -Real.log (37 / 80) ∧
    -Real.log (37 / 80) ≤ (771108723 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 37) = 1/(37 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-771108723 / 1000000000) (-771108721 / 1000000000) (Real.log (37 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95310179 / 1000000000) ≤ -Real.log (10 / 11) ∧
    -Real.log (10 / 11) ≤ (4765509 / 50000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 10) = 1/(10 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95310179 / 1000000000) (4765509 / 50000000) (Real.log (11 / 10)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11 / 10) = -Real.log (10 / 11) := by
    rw [show ((11 / 10) : ℝ) = ((10 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (21072103 / 200000000) ≤ -Real.log (9 / 10) ∧
    -Real.log (9 / 10) ≤ (26340129 / 250000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 9) = 1/(9 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26340129 / 250000000) (-21072103 / 200000000) (Real.log (9 / 10)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (72320661 / 1000000000) ≤ -Real.log (40 / 43) ∧
    -Real.log (40 / 43) ≤ (36160331 / 500000000) := by
  have h := checkLog_sound (w := (3 / 83)) (n := 12)
    (lo := (72320661 / 1000000000)) (hi := (36160331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 40) = 1/(40 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (72320661 / 1000000000) (36160331 / 500000000) (Real.log (43 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (43 / 40) = -Real.log (40 / 43) := by
    rw [show ((43 / 40) : ℝ) = ((40 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77961541 / 1000000000) ≤ -Real.log (37 / 40) ∧
    -Real.log (37 / 40) ≤ (38980771 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 37) = 1/(37 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38980771 / 500000000) (-77961541 / 1000000000) (Real.log (37 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (288668349 / 500000000) ≤ -Real.log (125000 / 222661) ∧
    -Real.log (125000 / 222661) ≤ (577336699 / 1000000000) := by
  have h := checkLog_sound (w := (97661 / 347661)) (n := 12)
    (lo := (288668349 / 500000000)) (hi := (577336699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222661 / 125000) = 1/(125000 / 222661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (288668349 / 500000000) (577336699 / 1000000000) (Real.log (222661 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (222661 / 125000) = -Real.log (125000 / 222661) := by
    rw [show ((222661 / 125000) : ℝ) = ((125000 / 222661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (759999741 / 500000000) ≤ -Real.log (27339 / 125000) ∧
    -Real.log (27339 / 125000) ≤ (303999897 / 200000000) := by
  have h := checkLog_sound (w := (3911 / 58589)) (n := 12)
    (lo := (66852561 / 500000000)) (hi := (133705123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 27339) = 1/(27339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-303999897 / 200000000) (-759999741 / 500000000) (Real.log (27339 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (577923741 / 1000000000) ≤ -Real.log (500000 / 891167) ∧
    -Real.log (500000 / 891167) ≤ (288961871 / 500000000) := by
  have h := checkLog_sound (w := (391167 / 1391167)) (n := 12)
    (lo := (577923741 / 1000000000)) (hi := (288961871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891167 / 500000) = 1/(500000 / 891167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (577923741 / 1000000000) (288961871 / 500000000) (Real.log (891167 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (891167 / 500000) = -Real.log (500000 / 891167) := by
    rw [show ((891167 / 500000) : ℝ) = ((500000 / 891167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3049587 / 2000000) ≤ -Real.log (108833 / 500000) ∧
    -Real.log (108833 / 500000) ≤ (1524793503 / 1000000000) := by
  have h := checkLog_sound (w := (16167 / 233833)) (n := 12)
    (lo := (6924957 / 50000000)) (hi := (138499141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108833) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 108833) = 1/(108833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1524793503 / 1000000000) (-3049587 / 2000000) (Real.log (108833 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (260001293 / 500000000) ≤ -Real.log (62500 / 105127) ∧
    -Real.log (62500 / 105127) ≤ (520002587 / 1000000000) := by
  have h := checkLog_sound (w := (42627 / 167627)) (n := 12)
    (lo := (260001293 / 500000000)) (hi := (520002587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105127 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105127 / 62500) = 1/(62500 / 105127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (260001293 / 500000000) (520002587 / 1000000000) (Real.log (105127 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (105127 / 62500) = -Real.log (62500 / 105127) := by
    rw [show ((105127 / 62500) : ℝ) = ((62500 / 105127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1145804529 / 1000000000) ≤ -Real.log (19873 / 62500) ∧
    -Real.log (19873 / 62500) ≤ (1145804531 / 1000000000) := by
  have h := checkLog_sound (w := (11377 / 51123)) (n := 12)
    (lo := (452657349 / 1000000000)) (hi := (9053147 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 19873) = 1/(19873 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1145804531 / 1000000000) (-1145804529 / 1000000000) (Real.log (19873 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131145443 / 250000000) ≤ -Real.log (125000 / 211219) ∧
    -Real.log (125000 / 211219) ≤ (524581773 / 1000000000) := by
  have h := checkLog_sound (w := (86219 / 336219)) (n := 12)
    (lo := (131145443 / 250000000)) (hi := (524581773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211219 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211219 / 125000) = 1/(125000 / 211219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131145443 / 250000000) (524581773 / 1000000000) (Real.log (211219 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (211219 / 125000) = -Real.log (125000 / 211219) := by
    rw [show ((211219 / 125000) : ℝ) = ((125000 / 211219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11703833 / 10000000) ≤ -Real.log (38781 / 125000) ∧
    -Real.log (38781 / 125000) ≤ (585191651 / 500000000) := by
  have h := checkLog_sound (w := (23719 / 101281)) (n := 12)
    (lo := (11930903 / 25000000)) (hi := (477236121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 38781) = 1/(38781 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-585191651 / 500000000) (-11703833 / 10000000) (Real.log (38781 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2097336179 / 1000000000) ≤ -Real.log (500000000000 / 4072222831851) ∧
    -Real.log (500000000000 / 4072222831851) ≤ (2097336183 / 1000000000) := by
  have h := checkLog_sound (w := (72222831851 / 8072222831851)) (n := 12)
    (lo := (17894639 / 1000000000)) (hi := (223683 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4072222831851 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4072222831851 / 4000000000000) = 1/(500000000000 / 4072222831851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2097336179 / 1000000000) (2097336183 / 1000000000) (Real.log (4072222831851 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4072222831851 / 500000000000) = -Real.log (500000000000 / 4072222831851) := by
    rw [show ((4072222831851 / 500000000000) : ℝ) = ((500000000000 / 4072222831851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52567931 / 25000000) ≤ -Real.log (250000000000 / 2047097387741) ∧
    -Real.log (250000000000 / 2047097387741) ≤ (525679311 / 250000000) := by
  have h := checkLog_sound (w := (47097387741 / 4047097387741)) (n := 12)
    (lo := (232757 / 10000000)) (hi := (23275701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047097387741 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2047097387741 / 2000000000000) = 1/(250000000000 / 2047097387741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52567931 / 25000000) (525679311 / 250000000) (Real.log (2047097387741 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2047097387741 / 250000000000) = -Real.log (250000000000 / 2047097387741) := by
    rw [show ((2047097387741 / 250000000000) : ℝ) = ((250000000000 / 2047097387741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (333161423 / 200000000) ≤ -Real.log (20000000000 / 105798822523) ∧
    -Real.log (20000000000 / 105798822523) ≤ (832903559 / 500000000) := by
  have h := checkLog_sound (w := (25798822523 / 185798822523)) (n := 12)
    (lo := (55902551 / 200000000)) (hi := (69878189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105798822523 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(105798822523 / 80000000000) = 1/(20000000000 / 105798822523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (333161423 / 200000000) (832903559 / 500000000) (Real.log (105798822523 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (105798822523 / 20000000000) = -Real.log (20000000000 / 105798822523) := by
    rw [show ((105798822523 / 20000000000) : ℝ) = ((20000000000 / 105798822523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (105935317 / 62500000) ≤ -Real.log (250000000000 / 1361613934659) ∧
    -Real.log (250000000000 / 1361613934659) ≤ (67798603 / 40000000) := by
  have h := checkLog_sound (w := (361613934659 / 2361613934659)) (n := 12)
    (lo := (38583839 / 125000000)) (hi := (308670713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361613934659 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1361613934659 / 1000000000000) = 1/(250000000000 / 1361613934659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (105935317 / 62500000) (67798603 / 40000000) (Real.log (1361613934659 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1361613934659 / 250000000000) = -Real.log (250000000000 / 1361613934659) := by
    rw [show ((1361613934659 / 250000000000) : ℝ) = ((250000000000 / 1361613934659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0004
