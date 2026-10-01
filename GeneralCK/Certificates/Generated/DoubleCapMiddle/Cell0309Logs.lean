import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0309
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

theorem reflection_log_1_neg : (221814543 / 1000000000) ≤ -Real.log (10240 / 12783) ∧
    -Real.log (10240 / 12783) ≤ (13863409 / 62500000) := by
  have h := checkLog_sound (w := (2543 / 23023)) (n := 12)
    (lo := (221814543 / 1000000000)) (hi := (13863409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12783 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12783 / 10240) = 1/(10240 / 12783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221814543 / 1000000000) (13863409 / 62500000) (Real.log (12783 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12783 / 10240) = -Real.log (10240 / 12783) := by
    rw [show ((12783 / 10240) : ℝ) = ((10240 / 12783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (285470977 / 1000000000) ≤ -Real.log (7697 / 10240) ∧
    -Real.log (7697 / 10240) ≤ (142735489 / 500000000) := by
  have h := checkLog_sound (w := (2543 / 17937)) (n := 12)
    (lo := (285470977 / 1000000000)) (hi := (142735489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7697) = 1/(7697 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-142735489 / 500000000) (-285470977 / 1000000000) (Real.log (7697 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221579829 / 1000000000) ≤ -Real.log (512 / 639) ∧
    -Real.log (512 / 639) ≤ (22157983 / 100000000) := by
  have h := checkLog_sound (w := (127 / 1151)) (n := 12)
    (lo := (221579829 / 1000000000)) (hi := (22157983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639 / 512) = 1/(512 / 639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (221579829 / 1000000000) (22157983 / 100000000) (Real.log (639 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (639 / 512) = -Real.log (512 / 639) := by
    rw [show ((639 / 512) : ℝ) = ((512 / 639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28508129 / 100000000) ≤ -Real.log (385 / 512) ∧
    -Real.log (385 / 512) ≤ (285081291 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 897)) (n := 12)
    (lo := (28508129 / 100000000)) (hi := (285081291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 385) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 385) = 1/(385 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-285081291 / 1000000000) (-28508129 / 100000000) (Real.log (385 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50406139 / 125000000) ≤ -Real.log (5120 / 7663) ∧
    -Real.log (5120 / 7663) ≤ (403249113 / 1000000000) := by
  have h := checkLog_sound (w := (2543 / 12783)) (n := 12)
    (lo := (50406139 / 125000000)) (hi := (403249113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7663 / 5120) = 1/(5120 / 7663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50406139 / 125000000) (403249113 / 1000000000) (Real.log (7663 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7663 / 5120) = -Real.log (5120 / 7663) := by
    rw [show ((7663 / 5120) : ℝ) = ((5120 / 7663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (686528507 / 1000000000) ≤ -Real.log (2577 / 5120) ∧
    -Real.log (2577 / 5120) ≤ (171632127 / 250000000) := by
  have h := checkLog_sound (w := (2543 / 7697)) (n := 12)
    (lo := (686528507 / 1000000000)) (hi := (171632127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2577) = 1/(2577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-171632127 / 250000000) (-686528507 / 1000000000) (Real.log (2577 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50357193 / 125000000) ≤ -Real.log (256 / 383) ∧
    -Real.log (256 / 383) ≤ (80571509 / 200000000) := by
  have h := checkLog_sound (w := (127 / 639)) (n := 12)
    (lo := (50357193 / 125000000)) (hi := (80571509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383 / 256) = 1/(256 / 383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (50357193 / 125000000) (80571509 / 200000000) (Real.log (383 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (383 / 256) = -Real.log (256 / 383) := by
    rw [show ((383 / 256) : ℝ) = ((256 / 383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8567063 / 12500000) ≤ -Real.log (129 / 256) ∧
    -Real.log (129 / 256) ≤ (685365041 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 385)) (n := 12)
    (lo := (8567063 / 12500000)) (hi := (685365041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 129) = 1/(129 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-685365041 / 1000000000) (-8567063 / 12500000) (Real.log (129 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303662699 / 1000000000) ≤ -Real.log (250000 / 338703) ∧
    -Real.log (250000 / 338703) ≤ (3036627 / 10000000) := by
  have h := checkLog_sound (w := (88703 / 588703)) (n := 12)
    (lo := (303662699 / 1000000000)) (hi := (3036627 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338703 / 250000) = 1/(250000 / 338703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303662699 / 1000000000) (3036627 / 10000000) (Real.log (338703 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (338703 / 250000) = -Real.log (250000 / 338703) := by
    rw [show ((338703 / 250000) : ℝ) = ((250000 / 338703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (438213531 / 1000000000) ≤ -Real.log (161297 / 250000) ∧
    -Real.log (161297 / 250000) ≤ (109553383 / 250000000) := by
  have h := checkLog_sound (w := (88703 / 411297)) (n := 12)
    (lo := (438213531 / 1000000000)) (hi := (109553383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 161297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 161297) = 1/(161297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-109553383 / 250000000) (-438213531 / 1000000000) (Real.log (161297 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151990387 / 500000000) ≤ -Real.log (1000000 / 1355243) ∧
    -Real.log (1000000 / 1355243) ≤ (12159231 / 40000000) := by
  have h := checkLog_sound (w := (355243 / 2355243)) (n := 12)
    (lo := (151990387 / 500000000)) (hi := (12159231 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355243 / 1000000) = 1/(1000000 / 1355243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151990387 / 500000000) (12159231 / 40000000) (Real.log (1355243 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1355243 / 1000000) = -Real.log (1000000 / 1355243) := by
    rw [show ((1355243 / 1000000) : ℝ) = ((1000000 / 1355243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (438881777 / 1000000000) ≤ -Real.log (644757 / 1000000) ∧
    -Real.log (644757 / 1000000) ≤ (219440889 / 500000000) := by
  have h := checkLog_sound (w := (355243 / 1644757)) (n := 12)
    (lo := (438881777 / 1000000000)) (hi := (219440889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644757) = 1/(644757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219440889 / 500000000) (-438881777 / 1000000000) (Real.log (644757 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9242691 / 40000000) ≤ -Real.log (125000 / 157493) ∧
    -Real.log (125000 / 157493) ≤ (57766819 / 250000000) := by
  have h := checkLog_sound (w := (32493 / 282493)) (n := 12)
    (lo := (9242691 / 40000000)) (hi := (57766819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157493 / 125000) = 1/(125000 / 157493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9242691 / 40000000) (57766819 / 250000000) (Real.log (157493 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (157493 / 125000) = -Real.log (125000 / 157493) := by
    rw [show ((157493 / 125000) : ℝ) = ((125000 / 157493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (301029419 / 1000000000) ≤ -Real.log (92507 / 125000) ∧
    -Real.log (92507 / 125000) ≤ (15051471 / 50000000) := by
  have h := checkLog_sound (w := (32493 / 217507)) (n := 12)
    (lo := (301029419 / 1000000000)) (hi := (15051471 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92507) = 1/(92507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15051471 / 50000000) (-301029419 / 1000000000) (Real.log (92507 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (115668149 / 500000000) ≤ -Real.log (1000000 / 1260283) ∧
    -Real.log (1000000 / 1260283) ≤ (231336299 / 1000000000) := by
  have h := checkLog_sound (w := (260283 / 2260283)) (n := 12)
    (lo := (115668149 / 500000000)) (hi := (231336299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260283 / 1000000) = 1/(1000000 / 1260283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (115668149 / 500000000) (231336299 / 1000000000) (Real.log (1260283 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1260283 / 1000000) = -Real.log (1000000 / 1260283) := by
    rw [show ((1260283 / 1000000) : ℝ) = ((1000000 / 1260283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (150743799 / 500000000) ≤ -Real.log (739717 / 1000000) ∧
    -Real.log (739717 / 1000000) ≤ (301487599 / 1000000000) := by
  have h := checkLog_sound (w := (260283 / 1739717)) (n := 12)
    (lo := (150743799 / 500000000)) (hi := (301487599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739717) = 1/(739717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-301487599 / 1000000000) (-150743799 / 500000000) (Real.log (739717 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (74187623 / 100000000) ≤ -Real.log (31250000000 / 65620989541) ∧
    -Real.log (31250000000 / 65620989541) ≤ (92734529 / 125000000) := by
  have h := checkLog_sound (w := (3120989541 / 128120989541)) (n := 12)
    (lo := (974581 / 20000000)) (hi := (48729051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65620989541 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65620989541 / 62500000000) = 1/(31250000000 / 65620989541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74187623 / 100000000) (92734529 / 125000000) (Real.log (65620989541 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65620989541 / 31250000000) = -Real.log (31250000000 / 65620989541) := by
    rw [show ((65620989541 / 31250000000) : ℝ) = ((31250000000 / 65620989541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14857251 / 20000000) ≤ -Real.log (62500000000 / 131371489569) ∧
    -Real.log (62500000000 / 131371489569) ≤ (92857819 / 125000000) := by
  have h := checkLog_sound (w := (6371489569 / 256371489569)) (n := 12)
    (lo := (4971537 / 100000000)) (hi := (49715371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131371489569 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(131371489569 / 125000000000) = 1/(62500000000 / 131371489569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14857251 / 20000000) (92857819 / 125000000) (Real.log (131371489569 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (131371489569 / 62500000000) = -Real.log (62500000000 / 131371489569) := by
    rw [show ((131371489569 / 62500000000) : ℝ) = ((62500000000 / 131371489569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (106419339 / 200000000) ≤ -Real.log (500000000000 / 851249094663) ∧
    -Real.log (500000000000 / 851249094663) ≤ (66512087 / 125000000) := by
  have h := checkLog_sound (w := (351249094663 / 1351249094663)) (n := 12)
    (lo := (106419339 / 200000000)) (hi := (66512087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851249094663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851249094663 / 500000000000) = 1/(500000000000 / 851249094663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (106419339 / 200000000) (66512087 / 125000000) (Real.log (851249094663 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (851249094663 / 500000000000) = -Real.log (500000000000 / 851249094663) := by
    rw [show ((851249094663 / 500000000000) : ℝ) = ((500000000000 / 851249094663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (532823897 / 1000000000) ≤ -Real.log (500000000000 / 851868349653) ∧
    -Real.log (500000000000 / 851868349653) ≤ (266411949 / 500000000) := by
  have h := checkLog_sound (w := (351868349653 / 1351868349653)) (n := 12)
    (lo := (532823897 / 1000000000)) (hi := (266411949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851868349653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851868349653 / 500000000000) = 1/(500000000000 / 851868349653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (532823897 / 1000000000) (266411949 / 500000000) (Real.log (851868349653 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (851868349653 / 500000000000) = -Real.log (500000000000 / 851868349653) := by
    rw [show ((851868349653 / 500000000000) : ℝ) = ((500000000000 / 851868349653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0309
