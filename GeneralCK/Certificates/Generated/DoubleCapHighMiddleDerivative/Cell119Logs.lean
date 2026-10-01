import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell119
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

theorem reflection_log_1_neg : (277868451 / 1000000000) ≤ -Real.log (128 / 169) ∧
    -Real.log (128 / 169) ≤ (69467113 / 250000000) := by
  have h := checkLog_sound (w := (41 / 297)) (n := 12)
    (lo := (277868451 / 1000000000)) (hi := (69467113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 128) = 1/(128 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (277868451 / 1000000000) (69467113 / 250000000) (Real.log (169 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (169 / 128) = -Real.log (128 / 169) := by
    rw [show ((169 / 128) : ℝ) = ((128 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (77224429 / 200000000) ≤ -Real.log (87 / 128) ∧
    -Real.log (87 / 128) ≤ (193061073 / 500000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 87) = 1/(87 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-193061073 / 500000000) (-77224429 / 200000000) (Real.log (87 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55484913 / 200000000) ≤ -Real.log (5120 / 6757) ∧
    -Real.log (5120 / 6757) ≤ (138712283 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 11877)) (n := 12)
    (lo := (55484913 / 200000000)) (hi := (138712283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6757 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6757 / 5120) = 1/(5120 / 6757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55484913 / 200000000) (138712283 / 500000000) (Real.log (6757 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6757 / 5120) = -Real.log (5120 / 6757) := by
    rw [show ((6757 / 5120) : ℝ) = ((5120 / 6757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (385260447 / 1000000000) ≤ -Real.log (3483 / 5120) ∧
    -Real.log (3483 / 5120) ≤ (12039389 / 31250000) := by
  have h := checkLog_sound (w := (1637 / 8603)) (n := 12)
    (lo := (385260447 / 1000000000)) (hi := (12039389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3483) = 1/(3483 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12039389 / 31250000) (-385260447 / 1000000000) (Real.log (3483 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51160563 / 250000000) ≤ -Real.log (500000 / 613543) ∧
    -Real.log (500000 / 613543) ≤ (204642253 / 1000000000) := by
  have h := checkLog_sound (w := (113543 / 1113543)) (n := 12)
    (lo := (51160563 / 250000000)) (hi := (204642253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613543 / 500000) = 1/(500000 / 613543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51160563 / 250000000) (204642253 / 1000000000) (Real.log (613543 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613543 / 500000) = -Real.log (500000 / 613543) := by
    rw [show ((613543 / 500000) : ℝ) = ((500000 / 613543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (257587491 / 1000000000) ≤ -Real.log (386457 / 500000) ∧
    -Real.log (386457 / 500000) ≤ (64396873 / 250000000) := by
  have h := checkLog_sound (w := (113543 / 886457)) (n := 12)
    (lo := (257587491 / 1000000000)) (hi := (64396873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386457) = 1/(386457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-64396873 / 250000000) (-257587491 / 1000000000) (Real.log (386457 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (204985283 / 1000000000) ≤ -Real.log (1000000 / 1227507) ∧
    -Real.log (1000000 / 1227507) ≤ (51246321 / 250000000) := by
  have h := checkLog_sound (w := (227507 / 2227507)) (n := 12)
    (lo := (204985283 / 1000000000)) (hi := (51246321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227507 / 1000000) = 1/(1000000 / 1227507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (204985283 / 1000000000) (51246321 / 250000000) (Real.log (1227507 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227507 / 1000000) = -Real.log (1000000 / 1227507) := by
    rw [show ((1227507 / 1000000) : ℝ) = ((1000000 / 1227507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (258132331 / 1000000000) ≤ -Real.log (772493 / 1000000) ∧
    -Real.log (772493 / 1000000) ≤ (64533083 / 250000000) := by
  have h := checkLog_sound (w := (227507 / 1772493)) (n := 12)
    (lo := (258132331 / 1000000000)) (hi := (64533083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772493) = 1/(772493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-64533083 / 250000000) (-258132331 / 1000000000) (Real.log (772493 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30183721 / 200000000) ≤ -Real.log (500000 / 581451) ∧
    -Real.log (500000 / 581451) ≤ (75459303 / 500000000) := by
  have h := checkLog_sound (w := (81451 / 1081451)) (n := 12)
    (lo := (30183721 / 200000000)) (hi := (75459303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581451 / 500000) = 1/(500000 / 581451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30183721 / 200000000) (75459303 / 500000000) (Real.log (581451 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581451 / 500000) = -Real.log (500000 / 581451) := by
    rw [show ((581451 / 500000) : ℝ) = ((500000 / 581451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17781413 / 100000000) ≤ -Real.log (418549 / 500000) ∧
    -Real.log (418549 / 500000) ≤ (177814131 / 1000000000) := by
  have h := checkLog_sound (w := (81451 / 918549)) (n := 12)
    (lo := (17781413 / 100000000)) (hi := (177814131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418549) = 1/(418549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177814131 / 1000000000) (-17781413 / 100000000) (Real.log (418549 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151186003 / 1000000000) ≤ -Real.log (1000000 / 1163213) ∧
    -Real.log (1000000 / 1163213) ≤ (37796501 / 250000000) := by
  have h := checkLog_sound (w := (163213 / 2163213)) (n := 12)
    (lo := (151186003 / 1000000000)) (hi := (37796501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163213 / 1000000) = 1/(1000000 / 1163213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151186003 / 1000000000) (37796501 / 250000000) (Real.log (1163213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163213 / 1000000) = -Real.log (1000000 / 1163213) := by
    rw [show ((1163213 / 1000000) : ℝ) = ((1000000 / 1163213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (178185721 / 1000000000) ≤ -Real.log (836787 / 1000000) ∧
    -Real.log (836787 / 1000000) ≤ (89092861 / 500000000) := by
  have h := checkLog_sound (w := (163213 / 1836787)) (n := 12)
    (lo := (178185721 / 1000000000)) (hi := (89092861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836787) = 1/(836787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89092861 / 500000000) (-178185721 / 1000000000) (Real.log (836787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (662685013 / 1000000000) ≤ -Real.log (500000000000 / 969997128911) ∧
    -Real.log (500000000000 / 969997128911) ≤ (331342507 / 500000000) := by
  have h := checkLog_sound (w := (469997128911 / 1469997128911)) (n := 12)
    (lo := (662685013 / 1000000000)) (hi := (331342507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969997128911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969997128911 / 500000000000) = 1/(500000000000 / 969997128911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (662685013 / 1000000000) (331342507 / 500000000) (Real.log (969997128911 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (969997128911 / 500000000000) = -Real.log (500000000000 / 969997128911) := by
    rw [show ((969997128911 / 500000000000) : ℝ) = ((500000000000 / 969997128911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (165997649 / 250000000) ≤ -Real.log (500000000000 / 971264367817) ∧
    -Real.log (500000000000 / 971264367817) ≤ (663990597 / 1000000000) := by
  have h := checkLog_sound (w := (471264367817 / 1471264367817)) (n := 12)
    (lo := (165997649 / 250000000)) (hi := (663990597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971264367817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971264367817 / 500000000000) = 1/(500000000000 / 971264367817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (165997649 / 250000000) (663990597 / 1000000000) (Real.log (971264367817 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (971264367817 / 500000000000) = -Real.log (500000000000 / 971264367817) := by
    rw [show ((971264367817 / 500000000000) : ℝ) = ((500000000000 / 971264367817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (28889359 / 62500000) ≤ -Real.log (100000000000 / 158761000577) ∧
    -Real.log (100000000000 / 158761000577) ≤ (92445949 / 200000000) := by
  have h := checkLog_sound (w := (58761000577 / 258761000577)) (n := 12)
    (lo := (28889359 / 62500000)) (hi := (92445949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158761000577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158761000577 / 100000000000) = 1/(100000000000 / 158761000577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28889359 / 62500000) (92445949 / 200000000) (Real.log (158761000577 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (158761000577 / 100000000000) = -Real.log (100000000000 / 158761000577) := by
    rw [show ((158761000577 / 100000000000) : ℝ) = ((100000000000 / 158761000577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (92623523 / 200000000) ≤ -Real.log (250000000000 / 397255056033) ∧
    -Real.log (250000000000 / 397255056033) ≤ (28944851 / 62500000) := by
  have h := checkLog_sound (w := (147255056033 / 647255056033)) (n := 12)
    (lo := (92623523 / 200000000)) (hi := (28944851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397255056033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397255056033 / 250000000000) = 1/(250000000000 / 397255056033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (92623523 / 200000000) (28944851 / 62500000) (Real.log (397255056033 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (397255056033 / 250000000000) = -Real.log (250000000000 / 397255056033) := by
    rw [show ((397255056033 / 250000000000) : ℝ) = ((250000000000 / 397255056033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (65746547 / 200000000) ≤ -Real.log (500000000000 / 694603260311) ∧
    -Real.log (500000000000 / 694603260311) ≤ (5136449 / 15625000) := by
  have h := checkLog_sound (w := (194603260311 / 1194603260311)) (n := 12)
    (lo := (65746547 / 200000000)) (hi := (5136449 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694603260311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694603260311 / 500000000000) = 1/(500000000000 / 694603260311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (65746547 / 200000000) (5136449 / 15625000) (Real.log (694603260311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (694603260311 / 500000000000) = -Real.log (500000000000 / 694603260311) := by
    rw [show ((694603260311 / 500000000000) : ℝ) = ((500000000000 / 694603260311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (82342931 / 250000000) ≤ -Real.log (500000000000 / 695047246193) ∧
    -Real.log (500000000000 / 695047246193) ≤ (13174869 / 40000000) := by
  have h := checkLog_sound (w := (195047246193 / 1195047246193)) (n := 12)
    (lo := (82342931 / 250000000)) (hi := (13174869 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695047246193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695047246193 / 500000000000) = 1/(500000000000 / 695047246193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (82342931 / 250000000) (13174869 / 40000000) (Real.log (695047246193 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695047246193 / 500000000000) = -Real.log (500000000000 / 695047246193) := by
    rw [show ((695047246193 / 500000000000) : ℝ) = ((500000000000 / 695047246193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26999717 / 1000000000) ≤ -Real.log (973361516631 / 1000000000000) ∧
    -Real.log (973361516631 / 1000000000000) ≤ (13499859 / 500000000) := by
  have h := checkLog_sound (w := (26638483369 / 1973361516631)) (n := 12)
    (lo := (26999717 / 1000000000)) (hi := (13499859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973361516631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973361516631) = 1/(973361516631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13499859 / 500000000) (-26999717 / 1000000000) (Real.log (973361516631 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1075821 / 40000000) ≤ -Real.log (243365734599 / 250000000000) ∧
    -Real.log (243365734599 / 250000000000) ≤ (13447763 / 500000000) := by
  have h := checkLog_sound (w := (6634265401 / 493365734599)) (n := 12)
    (lo := (1075821 / 40000000)) (hi := (13447763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243365734599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243365734599) = 1/(243365734599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13447763 / 500000000) (-1075821 / 40000000) (Real.log (243365734599 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell119
