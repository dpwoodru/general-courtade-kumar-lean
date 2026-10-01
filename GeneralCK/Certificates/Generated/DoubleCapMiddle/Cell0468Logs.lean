import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0468
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

theorem reflection_log_1_neg : (11486583 / 62500000) ≤ -Real.log (5120 / 6153) ∧
    -Real.log (5120 / 6153) ≤ (183785329 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 11273)) (n := 12)
    (lo := (11486583 / 62500000)) (hi := (183785329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6153 / 5120) = 1/(5120 / 6153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11486583 / 62500000) (183785329 / 1000000000) (Real.log (6153 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6153 / 5120) = -Real.log (5120 / 6153) := by
    rw [show ((6153 / 5120) : ℝ) = ((5120 / 6153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112671617 / 500000000) ≤ -Real.log (4087 / 5120) ∧
    -Real.log (4087 / 5120) ≤ (45068647 / 200000000) := by
  have h := checkLog_sound (w := (1033 / 9207)) (n := 12)
    (lo := (112671617 / 500000000)) (hi := (45068647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4087) = 1/(4087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45068647 / 200000000) (-112671617 / 500000000) (Real.log (4087 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (183663429 / 1000000000) ≤ -Real.log (20480 / 24609) ∧
    -Real.log (20480 / 24609) ≤ (18366343 / 100000000) := by
  have h := checkLog_sound (w := (4129 / 45089)) (n := 12)
    (lo := (183663429 / 1000000000)) (hi := (18366343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24609 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24609 / 20480) = 1/(20480 / 24609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (183663429 / 1000000000) (18366343 / 100000000) (Real.log (24609 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24609 / 20480) = -Real.log (20480 / 24609) := by
    rw [show ((24609 / 20480) : ℝ) = ((20480 / 24609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112579871 / 500000000) ≤ -Real.log (16351 / 20480) ∧
    -Real.log (16351 / 20480) ≤ (225159743 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 36831)) (n := 12)
    (lo := (112579871 / 500000000)) (hi := (225159743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16351) = 1/(16351 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-225159743 / 1000000000) (-112579871 / 500000000) (Real.log (16351 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (338980249 / 1000000000) ≤ -Real.log (2560 / 3593) ∧
    -Real.log (2560 / 3593) ≤ (1355921 / 4000000) := by
  have h := checkLog_sound (w := (1033 / 6153)) (n := 12)
    (lo := (338980249 / 1000000000)) (hi := (1355921 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3593 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3593 / 2560) = 1/(2560 / 3593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (338980249 / 1000000000) (1355921 / 4000000) (Real.log (3593 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3593 / 2560) = -Real.log (2560 / 3593) := by
    rw [show ((3593 / 2560) : ℝ) = ((2560 / 3593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64587779 / 125000000) ≤ -Real.log (1527 / 2560) ∧
    -Real.log (1527 / 2560) ≤ (516702233 / 1000000000) := by
  have h := checkLog_sound (w := (1033 / 4087)) (n := 12)
    (lo := (64587779 / 125000000)) (hi := (516702233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1527) = 1/(1527 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-516702233 / 1000000000) (-64587779 / 125000000) (Real.log (1527 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10586609 / 31250000) ≤ -Real.log (10240 / 14369) ∧
    -Real.log (10240 / 14369) ≤ (338771489 / 1000000000) := by
  have h := checkLog_sound (w := (4129 / 24609)) (n := 12)
    (lo := (10586609 / 31250000)) (hi := (338771489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14369 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14369 / 10240) = 1/(10240 / 14369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10586609 / 31250000) (338771489 / 1000000000) (Real.log (14369 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14369 / 10240) = -Real.log (10240 / 14369) := by
    rw [show ((14369 / 10240) : ℝ) = ((10240 / 14369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (516211193 / 1000000000) ≤ -Real.log (6111 / 10240) ∧
    -Real.log (6111 / 10240) ≤ (258105597 / 500000000) := by
  have h := checkLog_sound (w := (4129 / 16351)) (n := 12)
    (lo := (516211193 / 1000000000)) (hi := (258105597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6111) = 1/(6111 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258105597 / 500000000) (-516211193 / 1000000000) (Real.log (6111 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31558179 / 125000000) ≤ -Real.log (200000 / 257439) ∧
    -Real.log (200000 / 257439) ≤ (252465433 / 1000000000) := by
  have h := checkLog_sound (w := (57439 / 457439)) (n := 12)
    (lo := (31558179 / 125000000)) (hi := (252465433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257439 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257439 / 200000) = 1/(200000 / 257439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31558179 / 125000000) (252465433 / 1000000000) (Real.log (257439 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (257439 / 200000) = -Real.log (200000 / 257439) := by
    rw [show ((257439 / 200000) : ℝ) = ((200000 / 257439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84636847 / 250000000) ≤ -Real.log (142561 / 200000) ∧
    -Real.log (142561 / 200000) ≤ (338547389 / 1000000000) := by
  have h := checkLog_sound (w := (57439 / 342561)) (n := 12)
    (lo := (84636847 / 250000000)) (hi := (338547389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142561) = 1/(142561 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-338547389 / 1000000000) (-84636847 / 250000000) (Real.log (142561 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126315447 / 500000000) ≤ -Real.log (62500 / 80463) ∧
    -Real.log (62500 / 80463) ≤ (50526179 / 200000000) := by
  have h := checkLog_sound (w := (17963 / 142963)) (n := 12)
    (lo := (126315447 / 500000000)) (hi := (50526179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80463 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80463 / 62500) = 1/(62500 / 80463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126315447 / 500000000) (50526179 / 200000000) (Real.log (80463 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80463 / 62500) = -Real.log (62500 / 80463) := by
    rw [show ((80463 / 62500) : ℝ) = ((62500 / 80463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84711563 / 250000000) ≤ -Real.log (44537 / 62500) ∧
    -Real.log (44537 / 62500) ≤ (338846253 / 1000000000) := by
  have h := checkLog_sound (w := (17963 / 107037)) (n := 12)
    (lo := (84711563 / 250000000)) (hi := (338846253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44537) = 1/(44537 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-338846253 / 1000000000) (-84711563 / 250000000) (Real.log (44537 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188820393 / 1000000000) ≤ -Real.log (62500 / 75489) ∧
    -Real.log (62500 / 75489) ≤ (94410197 / 500000000) := by
  have h := checkLog_sound (w := (12989 / 137989)) (n := 12)
    (lo := (188820393 / 1000000000)) (hi := (94410197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75489 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75489 / 62500) = 1/(62500 / 75489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188820393 / 1000000000) (94410197 / 500000000) (Real.log (75489 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75489 / 62500) = -Real.log (62500 / 75489) := by
    rw [show ((75489 / 62500) : ℝ) = ((62500 / 75489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (232971689 / 1000000000) ≤ -Real.log (49511 / 62500) ∧
    -Real.log (49511 / 62500) ≤ (23297169 / 100000000) := by
  have h := checkLog_sound (w := (12989 / 112011)) (n := 12)
    (lo := (232971689 / 1000000000)) (hi := (23297169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49511) = 1/(49511 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-23297169 / 100000000) (-232971689 / 1000000000) (Real.log (49511 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18895451 / 100000000) ≤ -Real.log (500000 / 603993) ∧
    -Real.log (500000 / 603993) ≤ (188954511 / 1000000000) := by
  have h := checkLog_sound (w := (103993 / 1103993)) (n := 12)
    (lo := (18895451 / 100000000)) (hi := (188954511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603993 / 500000) = 1/(500000 / 603993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18895451 / 100000000) (188954511 / 1000000000) (Real.log (603993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (603993 / 500000) = -Real.log (500000 / 603993) := by
    rw [show ((603993 / 500000) : ℝ) = ((500000 / 603993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23317621 / 100000000) ≤ -Real.log (396007 / 500000) ∧
    -Real.log (396007 / 500000) ≤ (233176211 / 1000000000) := by
  have h := checkLog_sound (w := (103993 / 896007)) (n := 12)
    (lo := (23317621 / 100000000)) (hi := (233176211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396007) = 1/(396007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-233176211 / 1000000000) (-23317621 / 100000000) (Real.log (396007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (29550641 / 50000000) ≤ -Real.log (250000000000 / 451454114379) ∧
    -Real.log (250000000000 / 451454114379) ≤ (591012821 / 1000000000) := by
  have h := checkLog_sound (w := (201454114379 / 701454114379)) (n := 12)
    (lo := (29550641 / 50000000)) (hi := (591012821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451454114379 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451454114379 / 250000000000) = 1/(250000000000 / 451454114379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (29550641 / 50000000) (591012821 / 1000000000) (Real.log (451454114379 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (451454114379 / 250000000000) = -Real.log (250000000000 / 451454114379) := by
    rw [show ((451454114379 / 250000000000) : ℝ) = ((250000000000 / 451454114379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (591477147 / 1000000000) ≤ -Real.log (100000000000 / 180665514067) ∧
    -Real.log (100000000000 / 180665514067) ≤ (147869287 / 250000000) := by
  have h := checkLog_sound (w := (80665514067 / 280665514067)) (n := 12)
    (lo := (591477147 / 1000000000)) (hi := (147869287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180665514067 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180665514067 / 100000000000) = 1/(100000000000 / 180665514067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (591477147 / 1000000000) (147869287 / 250000000) (Real.log (180665514067 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (180665514067 / 100000000000) = -Real.log (100000000000 / 180665514067) := by
    rw [show ((180665514067 / 100000000000) : ℝ) = ((100000000000 / 180665514067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421792083 / 1000000000) ≤ -Real.log (10000000000 / 15246914827) ∧
    -Real.log (10000000000 / 15246914827) ≤ (105448021 / 250000000) := by
  have h := checkLog_sound (w := (5246914827 / 25246914827)) (n := 12)
    (lo := (421792083 / 1000000000)) (hi := (105448021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15246914827 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15246914827 / 10000000000) = 1/(10000000000 / 15246914827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421792083 / 1000000000) (105448021 / 250000000) (Real.log (15246914827 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15246914827 / 10000000000) = -Real.log (10000000000 / 15246914827) := by
    rw [show ((15246914827 / 10000000000) : ℝ) = ((10000000000 / 15246914827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2638317 / 6250000) ≤ -Real.log (50000000000 / 76260394387) ∧
    -Real.log (50000000000 / 76260394387) ≤ (422130721 / 1000000000) := by
  have h := checkLog_sound (w := (26260394387 / 126260394387)) (n := 12)
    (lo := (2638317 / 6250000)) (hi := (422130721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76260394387 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76260394387 / 50000000000) = 1/(50000000000 / 76260394387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2638317 / 6250000) (422130721 / 1000000000) (Real.log (76260394387 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76260394387 / 50000000000) = -Real.log (50000000000 / 76260394387) := by
    rw [show ((76260394387 / 50000000000) : ℝ) = ((50000000000 / 76260394387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0468
