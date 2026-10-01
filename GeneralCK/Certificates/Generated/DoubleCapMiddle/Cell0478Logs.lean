import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0478
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

theorem reflection_log_1_neg : (182565667 / 1000000000) ≤ -Real.log (10240 / 12291) ∧
    -Real.log (10240 / 12291) ≤ (45641417 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 22531)) (n := 12)
    (lo := (182565667 / 1000000000)) (hi := (45641417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12291 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12291 / 10240) = 1/(10240 / 12291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (182565667 / 1000000000) (45641417 / 250000000) (Real.log (12291 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12291 / 10240) = -Real.log (10240 / 12291) := by
    rw [show ((12291 / 10240) : ℝ) = ((10240 / 12291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (223509829 / 1000000000) ≤ -Real.log (8189 / 10240) ∧
    -Real.log (8189 / 10240) ≤ (22350983 / 100000000) := by
  have h := checkLog_sound (w := (2051 / 18429)) (n := 12)
    (lo := (223509829 / 1000000000)) (hi := (22350983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8189) = 1/(8189 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22350983 / 100000000) (-223509829 / 1000000000) (Real.log (8189 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (182443619 / 1000000000) ≤ -Real.log (20480 / 24579) ∧
    -Real.log (20480 / 24579) ≤ (9122181 / 50000000) := by
  have h := checkLog_sound (w := (4099 / 45059)) (n := 12)
    (lo := (182443619 / 1000000000)) (hi := (9122181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24579 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24579 / 20480) = 1/(20480 / 24579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (182443619 / 1000000000) (9122181 / 50000000) (Real.log (24579 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24579 / 20480) = -Real.log (20480 / 24579) := by
    rw [show ((24579 / 20480) : ℝ) = ((20480 / 24579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223326673 / 1000000000) ≤ -Real.log (16381 / 20480) ∧
    -Real.log (16381 / 20480) ≤ (111663337 / 500000000) := by
  have h := checkLog_sound (w := (4099 / 36861)) (n := 12)
    (lo := (223326673 / 1000000000)) (hi := (111663337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16381) = 1/(16381 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111663337 / 500000000) (-223326673 / 1000000000) (Real.log (16381 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13475627 / 40000000) ≤ -Real.log (5120 / 7171) ∧
    -Real.log (5120 / 7171) ≤ (84222669 / 250000000) := by
  have h := checkLog_sound (w := (2051 / 12291)) (n := 12)
    (lo := (13475627 / 40000000)) (hi := (84222669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7171 / 5120) = 1/(5120 / 7171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13475627 / 40000000) (84222669 / 250000000) (Real.log (7171 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7171 / 5120) = -Real.log (5120 / 7171) := by
    rw [show ((7171 / 5120) : ℝ) = ((5120 / 7171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (511802663 / 1000000000) ≤ -Real.log (3069 / 5120) ∧
    -Real.log (3069 / 5120) ≤ (63975333 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 8189)) (n := 12)
    (lo := (511802663 / 1000000000)) (hi := (63975333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3069) = 1/(3069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63975333 / 125000000) (-511802663 / 1000000000) (Real.log (3069 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168340739 / 500000000) ≤ -Real.log (10240 / 14339) ∧
    -Real.log (10240 / 14339) ≤ (336681479 / 1000000000) := by
  have h := checkLog_sound (w := (4099 / 24579)) (n := 12)
    (lo := (168340739 / 500000000)) (hi := (336681479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14339 / 10240) = 1/(10240 / 14339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168340739 / 500000000) (336681479 / 1000000000) (Real.log (14339 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14339 / 10240) = -Real.log (10240 / 14339) := by
    rw [show ((14339 / 10240) : ℝ) = ((10240 / 14339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63914253 / 125000000) ≤ -Real.log (6141 / 10240) ∧
    -Real.log (6141 / 10240) ≤ (20452561 / 40000000) := by
  have h := checkLog_sound (w := (4099 / 16381)) (n := 12)
    (lo := (63914253 / 125000000)) (hi := (20452561 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6141) = 1/(6141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20452561 / 40000000) (-63914253 / 125000000) (Real.log (6141 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12540893 / 50000000) ≤ -Real.log (250000 / 321269) ∧
    -Real.log (250000 / 321269) ≤ (250817861 / 1000000000) := by
  have h := checkLog_sound (w := (71269 / 571269)) (n := 12)
    (lo := (12540893 / 50000000)) (hi := (250817861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321269 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321269 / 250000) = 1/(250000 / 321269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12540893 / 50000000) (250817861 / 1000000000) (Real.log (321269 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321269 / 250000) = -Real.log (250000 / 321269) := by
    rw [show ((321269 / 250000) : ℝ) = ((250000 / 321269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (67115807 / 200000000) ≤ -Real.log (178731 / 250000) ∧
    -Real.log (178731 / 250000) ≤ (83894759 / 250000000) := by
  have h := checkLog_sound (w := (71269 / 428731)) (n := 12)
    (lo := (67115807 / 200000000)) (hi := (83894759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178731) = 1/(178731 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83894759 / 250000000) (-67115807 / 200000000) (Real.log (178731 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50196719 / 200000000) ≤ -Real.log (1000000 / 1285289) ∧
    -Real.log (1000000 / 1285289) ≤ (62745899 / 250000000) := by
  have h := checkLog_sound (w := (285289 / 2285289)) (n := 12)
    (lo := (50196719 / 200000000)) (hi := (62745899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285289 / 1000000) = 1/(1000000 / 1285289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50196719 / 200000000) (62745899 / 250000000) (Real.log (1285289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1285289 / 1000000) = -Real.log (1000000 / 1285289) := by
    rw [show ((1285289 / 1000000) : ℝ) = ((1000000 / 1285289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (335877013 / 1000000000) ≤ -Real.log (714711 / 1000000) ∧
    -Real.log (714711 / 1000000) ≤ (167938507 / 500000000) := by
  have h := checkLog_sound (w := (285289 / 1714711)) (n := 12)
    (lo := (335877013 / 1000000000)) (hi := (167938507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714711) = 1/(714711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-167938507 / 500000000) (-335877013 / 1000000000) (Real.log (714711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (93745751 / 500000000) ≤ -Real.log (50000 / 60311) ∧
    -Real.log (50000 / 60311) ≤ (187491503 / 1000000000) := by
  have h := checkLog_sound (w := (10311 / 110311)) (n := 12)
    (lo := (93745751 / 500000000)) (hi := (187491503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60311 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60311 / 50000) = 1/(50000 / 60311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (93745751 / 500000000) (187491503 / 1000000000) (Real.log (60311 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60311 / 50000) = -Real.log (50000 / 60311) := by
    rw [show ((60311 / 50000) : ℝ) = ((50000 / 60311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (115474467 / 500000000) ≤ -Real.log (39689 / 50000) ∧
    -Real.log (39689 / 50000) ≤ (46189787 / 200000000) := by
  have h := checkLog_sound (w := (10311 / 89689)) (n := 12)
    (lo := (115474467 / 500000000)) (hi := (46189787 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39689) = 1/(39689 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46189787 / 200000000) (-115474467 / 500000000) (Real.log (39689 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (187625797 / 1000000000) ≤ -Real.log (500000 / 603191) ∧
    -Real.log (500000 / 603191) ≤ (93812899 / 500000000) := by
  have h := checkLog_sound (w := (103191 / 1103191)) (n := 12)
    (lo := (187625797 / 1000000000)) (hi := (93812899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603191 / 500000) = 1/(500000 / 603191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187625797 / 1000000000) (93812899 / 500000000) (Real.log (603191 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603191 / 500000) = -Real.log (500000 / 603191) := by
    rw [show ((603191 / 500000) : ℝ) = ((500000 / 603191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231153041 / 1000000000) ≤ -Real.log (396809 / 500000) ∧
    -Real.log (396809 / 500000) ≤ (115576521 / 500000000) := by
  have h := checkLog_sound (w := (103191 / 896809)) (n := 12)
    (lo := (231153041 / 1000000000)) (hi := (115576521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396809) = 1/(396809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115576521 / 500000000) (-231153041 / 1000000000) (Real.log (396809 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18324903 / 31250000) ≤ -Real.log (500000000000 / 898750076931) ∧
    -Real.log (500000000000 / 898750076931) ≤ (586396897 / 1000000000) := by
  have h := checkLog_sound (w := (398750076931 / 1398750076931)) (n := 12)
    (lo := (18324903 / 31250000)) (hi := (586396897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((898750076931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(898750076931 / 500000000000) = 1/(500000000000 / 898750076931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18324903 / 31250000) (586396897 / 1000000000) (Real.log (898750076931 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (898750076931 / 500000000000) = -Real.log (500000000000 / 898750076931) := by
    rw [show ((898750076931 / 500000000000) : ℝ) = ((500000000000 / 898750076931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (586860609 / 1000000000) ≤ -Real.log (500000000000 / 899166936007) ∧
    -Real.log (500000000000 / 899166936007) ≤ (58686061 / 100000000) := by
  have h := checkLog_sound (w := (399166936007 / 1399166936007)) (n := 12)
    (lo := (586860609 / 1000000000)) (hi := (58686061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899166936007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899166936007 / 500000000000) = 1/(500000000000 / 899166936007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (586860609 / 1000000000) (58686061 / 100000000) (Real.log (899166936007 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (899166936007 / 500000000000) = -Real.log (500000000000 / 899166936007) := by
    rw [show ((899166936007 / 500000000000) : ℝ) = ((500000000000 / 899166936007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (418440437 / 1000000000) ≤ -Real.log (500000000000 / 759794905389) ∧
    -Real.log (500000000000 / 759794905389) ≤ (209220219 / 500000000) := by
  have h := checkLog_sound (w := (259794905389 / 1259794905389)) (n := 12)
    (lo := (418440437 / 1000000000)) (hi := (209220219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759794905389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759794905389 / 500000000000) = 1/(500000000000 / 759794905389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (418440437 / 1000000000) (209220219 / 500000000) (Real.log (759794905389 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (759794905389 / 500000000000) = -Real.log (500000000000 / 759794905389) := by
    rw [show ((759794905389 / 500000000000) : ℝ) = ((500000000000 / 759794905389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (418778839 / 1000000000) ≤ -Real.log (62500000000 / 95006508169) ∧
    -Real.log (62500000000 / 95006508169) ≤ (10469471 / 25000000) := by
  have h := checkLog_sound (w := (32506508169 / 157506508169)) (n := 12)
    (lo := (418778839 / 1000000000)) (hi := (10469471 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95006508169 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95006508169 / 62500000000) = 1/(62500000000 / 95006508169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (418778839 / 1000000000) (10469471 / 25000000) (Real.log (95006508169 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (95006508169 / 62500000000) = -Real.log (62500000000 / 95006508169) := by
    rw [show ((95006508169 / 62500000000) : ℝ) = ((62500000000 / 95006508169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0478
