import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0308
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

theorem reflection_log_1_neg : (111024601 / 500000000) ≤ -Real.log (5120 / 6393) ∧
    -Real.log (5120 / 6393) ≤ (222049203 / 1000000000) := by
  have h := checkLog_sound (w := (1273 / 11513)) (n := 12)
    (lo := (111024601 / 500000000)) (hi := (222049203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6393 / 5120) = 1/(5120 / 6393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111024601 / 500000000) (222049203 / 1000000000) (Real.log (6393 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6393 / 5120) = -Real.log (5120 / 6393) := by
    rw [show ((6393 / 5120) : ℝ) = ((5120 / 6393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57172163 / 200000000) ≤ -Real.log (3847 / 5120) ∧
    -Real.log (3847 / 5120) ≤ (17866301 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 8967)) (n := 12)
    (lo := (57172163 / 200000000)) (hi := (17866301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3847) = 1/(3847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17866301 / 62500000) (-57172163 / 200000000) (Real.log (3847 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (221814543 / 1000000000) ≤ -Real.log (10240 / 12783) ∧
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


theorem reflection_log_3 : Bounds (221814543 / 1000000000) (13863409 / 62500000) (Real.log (12783 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12783 / 10240) = -Real.log (10240 / 12783) := by
    rw [show ((12783 / 10240) : ℝ) = ((10240 / 12783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (285470977 / 1000000000) ≤ -Real.log (7697 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-142735489 / 500000000) (-285470977 / 1000000000) (Real.log (7697 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (403640527 / 1000000000) ≤ -Real.log (2560 / 3833) ∧
    -Real.log (2560 / 3833) ≤ (25227533 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 6393)) (n := 12)
    (lo := (403640527 / 1000000000)) (hi := (25227533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3833 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3833 / 2560) = 1/(2560 / 3833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (403640527 / 1000000000) (25227533 / 62500000) (Real.log (3833 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3833 / 2560) = -Real.log (2560 / 3833) := by
    rw [show ((3833 / 2560) : ℝ) = ((2560 / 3833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (687693329 / 1000000000) ≤ -Real.log (1287 / 2560) ∧
    -Real.log (1287 / 2560) ≤ (68769333 / 100000000) := by
  have h := checkLog_sound (w := (1273 / 3847)) (n := 12)
    (lo := (687693329 / 1000000000)) (hi := (68769333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1287) = 1/(1287 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-68769333 / 100000000) (-687693329 / 1000000000) (Real.log (1287 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (50406139 / 125000000) ≤ -Real.log (5120 / 7663) ∧
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


theorem reflection_log_7 : Bounds (50406139 / 125000000) (403249113 / 1000000000) (Real.log (7663 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7663 / 5120) = -Real.log (5120 / 7663) := by
    rw [show ((7663 / 5120) : ℝ) = ((5120 / 7663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (686528507 / 1000000000) ≤ -Real.log (2577 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-171632127 / 250000000) (-686528507 / 1000000000) (Real.log (2577 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75995009 / 250000000) ≤ -Real.log (500000 / 677621) ∧
    -Real.log (500000 / 677621) ≤ (303980037 / 1000000000) := by
  have h := checkLog_sound (w := (177621 / 1177621)) (n := 12)
    (lo := (75995009 / 250000000)) (hi := (303980037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677621 / 500000) = 1/(500000 / 677621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75995009 / 250000000) (303980037 / 1000000000) (Real.log (677621 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (677621 / 500000) = -Real.log (500000 / 677621) := by
    rw [show ((677621 / 500000) : ℝ) = ((500000 / 677621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219440113 / 500000000) ≤ -Real.log (322379 / 500000) ∧
    -Real.log (322379 / 500000) ≤ (438880227 / 1000000000) := by
  have h := checkLog_sound (w := (177621 / 822379)) (n := 12)
    (lo := (219440113 / 500000000)) (hi := (438880227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322379) = 1/(322379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-438880227 / 1000000000) (-219440113 / 500000000) (Real.log (322379 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (304298009 / 1000000000) ≤ -Real.log (1000000 / 1355673) ∧
    -Real.log (1000000 / 1355673) ≤ (30429801 / 100000000) := by
  have h := checkLog_sound (w := (355673 / 2355673)) (n := 12)
    (lo := (304298009 / 1000000000)) (hi := (30429801 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355673 / 1000000) = 1/(1000000 / 1355673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (304298009 / 1000000000) (30429801 / 100000000) (Real.log (1355673 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1355673 / 1000000) = -Real.log (1000000 / 1355673) := by
    rw [show ((1355673 / 1000000) : ℝ) = ((1000000 / 1355673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (439548917 / 1000000000) ≤ -Real.log (644327 / 1000000) ∧
    -Real.log (644327 / 1000000) ≤ (219774459 / 500000000) := by
  have h := checkLog_sound (w := (355673 / 1644327)) (n := 12)
    (lo := (439548917 / 1000000000)) (hi := (219774459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644327) = 1/(644327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-219774459 / 500000000) (-439548917 / 1000000000) (Real.log (644327 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (46267101 / 200000000) ≤ -Real.log (500000 / 630141) ∧
    -Real.log (500000 / 630141) ≤ (115667753 / 500000000) := by
  have h := checkLog_sound (w := (130141 / 1130141)) (n := 12)
    (lo := (46267101 / 200000000)) (hi := (115667753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630141 / 500000) = 1/(500000 / 630141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (46267101 / 200000000) (115667753 / 500000000) (Real.log (630141 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (630141 / 500000) = -Real.log (500000 / 630141) := by
    rw [show ((630141 / 500000) : ℝ) = ((500000 / 630141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150743123 / 500000000) ≤ -Real.log (369859 / 500000) ∧
    -Real.log (369859 / 500000) ≤ (301486247 / 1000000000) := by
  have h := checkLog_sound (w := (130141 / 869859)) (n := 12)
    (lo := (150743123 / 500000000)) (hi := (301486247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369859) = 1/(369859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-301486247 / 1000000000) (-150743123 / 500000000) (Real.log (369859 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231603663 / 1000000000) ≤ -Real.log (50000 / 63031) ∧
    -Real.log (50000 / 63031) ≤ (14475229 / 62500000) := by
  have h := checkLog_sound (w := (13031 / 113031)) (n := 12)
    (lo := (231603663 / 1000000000)) (hi := (14475229 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63031 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63031 / 50000) = 1/(50000 / 63031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231603663 / 1000000000) (14475229 / 62500000) (Real.log (63031 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63031 / 50000) = -Real.log (50000 / 63031) := by
    rw [show ((63031 / 50000) : ℝ) = ((50000 / 63031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (301943281 / 1000000000) ≤ -Real.log (36969 / 50000) ∧
    -Real.log (36969 / 50000) ≤ (150971641 / 500000000) := by
  have h := checkLog_sound (w := (13031 / 86969)) (n := 12)
    (lo := (301943281 / 1000000000)) (hi := (150971641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36969) = 1/(36969 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-150971641 / 500000000) (-301943281 / 1000000000) (Real.log (36969 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (742860261 / 1000000000) ≤ -Real.log (500000000000 / 1050969511041) ∧
    -Real.log (500000000000 / 1050969511041) ≤ (742860263 / 1000000000) := by
  have h := checkLog_sound (w := (50969511041 / 2050969511041)) (n := 12)
    (lo := (49713081 / 1000000000)) (hi := (24856541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1050969511041 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1050969511041 / 1000000000000) = 1/(500000000000 / 1050969511041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (742860261 / 1000000000) (742860263 / 1000000000) (Real.log (1050969511041 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1050969511041 / 500000000000) = -Real.log (500000000000 / 1050969511041) := by
    rw [show ((1050969511041 / 500000000000) : ℝ) = ((500000000000 / 1050969511041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (743846927 / 1000000000) ≤ -Real.log (15625000000 / 32875218057) ∧
    -Real.log (15625000000 / 32875218057) ≤ (743846929 / 1000000000) := by
  have h := checkLog_sound (w := (1625218057 / 64125218057)) (n := 12)
    (lo := (50699747 / 1000000000)) (hi := (12674937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32875218057 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32875218057 / 31250000000) = 1/(15625000000 / 32875218057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (743846927 / 1000000000) (743846929 / 1000000000) (Real.log (32875218057 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32875218057 / 15625000000) = -Real.log (15625000000 / 32875218057) := by
    rw [show ((32875218057 / 15625000000) : ℝ) = ((15625000000 / 32875218057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (532821751 / 1000000000) ≤ -Real.log (500000000000 / 851866522107) ∧
    -Real.log (500000000000 / 851866522107) ≤ (66602719 / 125000000) := by
  have h := checkLog_sound (w := (351866522107 / 1351866522107)) (n := 12)
    (lo := (532821751 / 1000000000)) (hi := (66602719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851866522107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851866522107 / 500000000000) = 1/(500000000000 / 851866522107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (532821751 / 1000000000) (66602719 / 125000000) (Real.log (851866522107 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (851866522107 / 500000000000) = -Real.log (500000000000 / 851866522107) := by
    rw [show ((851866522107 / 500000000000) : ℝ) = ((500000000000 / 851866522107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (106709389 / 200000000) ≤ -Real.log (500000000000 / 852484514053) ∧
    -Real.log (500000000000 / 852484514053) ≤ (266773473 / 500000000) := by
  have h := checkLog_sound (w := (352484514053 / 1352484514053)) (n := 12)
    (lo := (106709389 / 200000000)) (hi := (266773473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852484514053 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852484514053 / 500000000000) = 1/(500000000000 / 852484514053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (106709389 / 200000000) (266773473 / 500000000) (Real.log (852484514053 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (852484514053 / 500000000000) = -Real.log (500000000000 / 852484514053) := by
    rw [show ((852484514053 / 500000000000) : ℝ) = ((500000000000 / 852484514053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0308
