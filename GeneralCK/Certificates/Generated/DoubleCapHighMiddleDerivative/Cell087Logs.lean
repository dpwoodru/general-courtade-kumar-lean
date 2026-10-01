import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell087
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

theorem reflection_log_1_neg : (52713093 / 200000000) ≤ -Real.log (640 / 833) ∧
    -Real.log (640 / 833) ≤ (131782733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1473)) (n := 12)
    (lo := (52713093 / 200000000)) (hi := (131782733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833 / 640) = 1/(640 / 833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52713093 / 200000000) (131782733 / 500000000) (Real.log (833 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (833 / 640) = -Real.log (640 / 833) := by
    rw [show ((833 / 640) : ℝ) = ((640 / 833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358909581 / 1000000000) ≤ -Real.log (447 / 640) ∧
    -Real.log (447 / 640) ≤ (179454791 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 447) = 1/(447 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-179454791 / 500000000) (-358909581 / 1000000000) (Real.log (447 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16444699 / 62500000) ≤ -Real.log (5120 / 6661) ∧
    -Real.log (5120 / 6661) ≤ (52623037 / 200000000) := by
  have h := checkLog_sound (w := (1541 / 11781)) (n := 12)
    (lo := (16444699 / 62500000)) (hi := (52623037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6661 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6661 / 5120) = 1/(5120 / 6661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16444699 / 62500000) (52623037 / 200000000) (Real.log (6661 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6661 / 5120) = -Real.log (5120 / 6661) := by
    rw [show ((6661 / 5120) : ℝ) = ((5120 / 6661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358071007 / 1000000000) ≤ -Real.log (3579 / 5120) ∧
    -Real.log (3579 / 5120) ≤ (11189719 / 31250000) := by
  have h := checkLog_sound (w := (1541 / 8699)) (n := 12)
    (lo := (358071007 / 1000000000)) (hi := (11189719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3579) = 1/(3579 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11189719 / 31250000) (-358071007 / 1000000000) (Real.log (3579 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38727623 / 200000000) ≤ -Real.log (1000000 / 1213657) ∧
    -Real.log (1000000 / 1213657) ≤ (48409529 / 250000000) := by
  have h := checkLog_sound (w := (213657 / 2213657)) (n := 12)
    (lo := (38727623 / 200000000)) (hi := (48409529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213657 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213657 / 1000000) = 1/(1000000 / 1213657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38727623 / 200000000) (48409529 / 250000000) (Real.log (1213657 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1213657 / 1000000) = -Real.log (1000000 / 1213657) := by
    rw [show ((1213657 / 1000000) : ℝ) = ((1000000 / 1213657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (120181097 / 500000000) ≤ -Real.log (786343 / 1000000) ∧
    -Real.log (786343 / 1000000) ≤ (48072439 / 200000000) := by
  have h := checkLog_sound (w := (213657 / 1786343)) (n := 12)
    (lo := (120181097 / 500000000)) (hi := (48072439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786343) = 1/(786343 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-48072439 / 200000000) (-120181097 / 500000000) (Real.log (786343 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193984117 / 1000000000) ≤ -Real.log (1000000 / 1214077) ∧
    -Real.log (1000000 / 1214077) ≤ (96992059 / 500000000) := by
  have h := checkLog_sound (w := (214077 / 2214077)) (n := 12)
    (lo := (193984117 / 1000000000)) (hi := (96992059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214077 / 1000000) = 1/(1000000 / 1214077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193984117 / 1000000000) (96992059 / 500000000) (Real.log (1214077 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1214077 / 1000000) = -Real.log (1000000 / 1214077) := by
    rw [show ((1214077 / 1000000) : ℝ) = ((1000000 / 1214077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48179291 / 200000000) ≤ -Real.log (785923 / 1000000) ∧
    -Real.log (785923 / 1000000) ≤ (30112057 / 125000000) := by
  have h := checkLog_sound (w := (214077 / 1785923)) (n := 12)
    (lo := (48179291 / 200000000)) (hi := (30112057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785923) = 1/(785923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-30112057 / 125000000) (-48179291 / 200000000) (Real.log (785923 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142379383 / 1000000000) ≤ -Real.log (500000 / 576507) ∧
    -Real.log (500000 / 576507) ≤ (17797423 / 125000000) := by
  have h := checkLog_sound (w := (76507 / 1076507)) (n := 12)
    (lo := (142379383 / 1000000000)) (hi := (17797423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576507 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576507 / 500000) = 1/(500000 / 576507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142379383 / 1000000000) (17797423 / 125000000) (Real.log (576507 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576507 / 500000) = -Real.log (500000 / 576507) := by
    rw [show ((576507 / 500000) : ℝ) = ((500000 / 576507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (166071113 / 1000000000) ≤ -Real.log (423493 / 500000) ∧
    -Real.log (423493 / 500000) ≤ (83035557 / 500000000) := by
  have h := checkLog_sound (w := (76507 / 923493)) (n := 12)
    (lo := (166071113 / 1000000000)) (hi := (83035557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423493) = 1/(423493 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83035557 / 500000000) (-166071113 / 1000000000) (Real.log (423493 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7132367 / 50000000) ≤ -Real.log (1000000 / 1153323) ∧
    -Real.log (1000000 / 1153323) ≤ (142647341 / 1000000000) := by
  have h := checkLog_sound (w := (153323 / 2153323)) (n := 12)
    (lo := (7132367 / 50000000)) (hi := (142647341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153323 / 1000000) = 1/(1000000 / 1153323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7132367 / 50000000) (142647341 / 1000000000) (Real.log (1153323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153323 / 1000000) = -Real.log (1000000 / 1153323) := by
    rw [show ((1153323 / 1000000) : ℝ) = ((1000000 / 1153323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83218001 / 500000000) ≤ -Real.log (846677 / 1000000) ∧
    -Real.log (846677 / 1000000) ≤ (166436003 / 1000000000) := by
  have h := checkLog_sound (w := (153323 / 1846677)) (n := 12)
    (lo := (83218001 / 500000000)) (hi := (166436003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846677) = 1/(846677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-166436003 / 1000000000) (-83218001 / 500000000) (Real.log (846677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (621186191 / 1000000000) ≤ -Real.log (500000000000 / 930567197541) ∧
    -Real.log (500000000000 / 930567197541) ≤ (38824137 / 62500000) := by
  have h := checkLog_sound (w := (430567197541 / 1430567197541)) (n := 12)
    (lo := (621186191 / 1000000000)) (hi := (38824137 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930567197541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930567197541 / 500000000000) = 1/(500000000000 / 930567197541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (621186191 / 1000000000) (38824137 / 62500000) (Real.log (930567197541 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (930567197541 / 500000000000) = -Real.log (500000000000 / 930567197541) := by
    rw [show ((930567197541 / 500000000000) : ℝ) = ((500000000000 / 930567197541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (622475047 / 1000000000) ≤ -Real.log (31250000000 / 58235458613) ∧
    -Real.log (31250000000 / 58235458613) ≤ (77809381 / 125000000) := by
  have h := checkLog_sound (w := (26985458613 / 89485458613)) (n := 12)
    (lo := (622475047 / 1000000000)) (hi := (77809381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58235458613 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58235458613 / 31250000000) = 1/(31250000000 / 58235458613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (622475047 / 1000000000) (77809381 / 125000000) (Real.log (58235458613 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (58235458613 / 31250000000) = -Real.log (31250000000 / 58235458613) := by
    rw [show ((58235458613 / 31250000000) : ℝ) = ((31250000000 / 58235458613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (43400031 / 100000000) ≤ -Real.log (62500000000 / 96463709221) ∧
    -Real.log (62500000000 / 96463709221) ≤ (434000311 / 1000000000) := by
  have h := checkLog_sound (w := (33963709221 / 158963709221)) (n := 12)
    (lo := (43400031 / 100000000)) (hi := (434000311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96463709221 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96463709221 / 62500000000) = 1/(62500000000 / 96463709221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43400031 / 100000000) (434000311 / 1000000000) (Real.log (96463709221 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (96463709221 / 62500000000) = -Real.log (62500000000 / 96463709221) := by
    rw [show ((96463709221 / 62500000000) : ℝ) = ((62500000000 / 96463709221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (434880573 / 1000000000) ≤ -Real.log (250000000000 / 386194639933) ∧
    -Real.log (250000000000 / 386194639933) ≤ (217440287 / 500000000) := by
  have h := checkLog_sound (w := (136194639933 / 636194639933)) (n := 12)
    (lo := (434880573 / 1000000000)) (hi := (217440287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386194639933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386194639933 / 250000000000) = 1/(250000000000 / 386194639933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (434880573 / 1000000000) (217440287 / 500000000) (Real.log (386194639933 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (386194639933 / 250000000000) = -Real.log (250000000000 / 386194639933) := by
    rw [show ((386194639933 / 250000000000) : ℝ) = ((250000000000 / 386194639933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (4819539 / 15625000) ≤ -Real.log (250000000000 / 340328529633) ∧
    -Real.log (250000000000 / 340328529633) ≤ (308450497 / 1000000000) := by
  have h := checkLog_sound (w := (90328529633 / 590328529633)) (n := 12)
    (lo := (4819539 / 15625000)) (hi := (308450497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340328529633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340328529633 / 250000000000) = 1/(250000000000 / 340328529633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4819539 / 15625000) (308450497 / 1000000000) (Real.log (340328529633 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (340328529633 / 250000000000) = -Real.log (250000000000 / 340328529633) := by
    rw [show ((340328529633 / 250000000000) : ℝ) = ((250000000000 / 340328529633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309083343 / 1000000000) ≤ -Real.log (62500000000 / 85135993419) ∧
    -Real.log (62500000000 / 85135993419) ≤ (19317709 / 62500000) := by
  have h := checkLog_sound (w := (22635993419 / 147635993419)) (n := 12)
    (lo := (309083343 / 1000000000)) (hi := (19317709 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85135993419 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85135993419 / 62500000000) = 1/(62500000000 / 85135993419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309083343 / 1000000000) (19317709 / 62500000) (Real.log (85135993419 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (85135993419 / 62500000000) = -Real.log (62500000000 / 85135993419) := by
    rw [show ((85135993419 / 62500000000) : ℝ) = ((62500000000 / 85135993419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11894331 / 500000000) ≤ -Real.log (976492057671 / 1000000000000) ∧
    -Real.log (976492057671 / 1000000000000) ≤ (23788663 / 1000000000) := by
  have h := checkLog_sound (w := (23507942329 / 1976492057671)) (n := 12)
    (lo := (11894331 / 500000000)) (hi := (23788663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976492057671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976492057671) = 1/(976492057671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23788663 / 1000000000) (-11894331 / 500000000) (Real.log (976492057671 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23691729 / 1000000000) ≤ -Real.log (244146678951 / 250000000000) ∧
    -Real.log (244146678951 / 250000000000) ≤ (2369173 / 100000000) := by
  have h := checkLog_sound (w := (5853321049 / 494146678951)) (n := 12)
    (lo := (23691729 / 1000000000)) (hi := (2369173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244146678951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244146678951) = 1/(244146678951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2369173 / 100000000) (-23691729 / 1000000000) (Real.log (244146678951 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell087
