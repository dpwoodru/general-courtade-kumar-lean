import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell252
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

theorem reflection_log_1_neg : (335215867 / 1000000000) ≤ -Real.log (5120 / 7159) ∧
    -Real.log (5120 / 7159) ≤ (83803967 / 250000000) := by
  have h := checkLog_sound (w := (2039 / 12279)) (n := 12)
    (lo := (335215867 / 1000000000)) (hi := (83803967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7159 / 5120) = 1/(5120 / 7159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335215867 / 1000000000) (83803967 / 250000000) (Real.log (7159 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7159 / 5120) = -Real.log (5120 / 7159) := by
    rw [show ((7159 / 5120) : ℝ) = ((5120 / 7159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (507900219 / 1000000000) ≤ -Real.log (3081 / 5120) ∧
    -Real.log (3081 / 5120) ≤ (25395011 / 50000000) := by
  have h := checkLog_sound (w := (2039 / 8201)) (n := 12)
    (lo := (507900219 / 1000000000)) (hi := (25395011 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3081) = 1/(3081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-25395011 / 50000000) (-507900219 / 1000000000) (Real.log (3081 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167398363 / 500000000) ≤ -Real.log (1280 / 1789) ∧
    -Real.log (1280 / 1789) ≤ (334796727 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 3069)) (n := 12)
    (lo := (167398363 / 500000000)) (hi := (334796727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789 / 1280) = 1/(1280 / 1789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167398363 / 500000000) (334796727 / 1000000000) (Real.log (1789 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1789 / 1280) = -Real.log (1280 / 1789) := by
    rw [show ((1789 / 1280) : ℝ) = ((1280 / 1789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (506926983 / 1000000000) ≤ -Real.log (771 / 1280) ∧
    -Real.log (771 / 1280) ≤ (63365873 / 125000000) := by
  have h := checkLog_sound (w := (509 / 2051)) (n := 12)
    (lo := (506926983 / 1000000000)) (hi := (63365873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 771) = 1/(771 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63365873 / 125000000) (-506926983 / 1000000000) (Real.log (771 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124666789 / 500000000) ≤ -Real.log (100000 / 128317) ∧
    -Real.log (100000 / 128317) ≤ (249333579 / 1000000000) := by
  have h := checkLog_sound (w := (28317 / 228317)) (n := 12)
    (lo := (124666789 / 500000000)) (hi := (249333579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128317 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128317 / 100000) = 1/(100000 / 128317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124666789 / 500000000) (249333579 / 1000000000) (Real.log (128317 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (128317 / 100000) = -Real.log (100000 / 128317) := by
    rw [show ((128317 / 100000) : ℝ) = ((100000 / 128317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (66583313 / 200000000) ≤ -Real.log (71683 / 100000) ∧
    -Real.log (71683 / 100000) ≤ (166458283 / 500000000) := by
  have h := checkLog_sound (w := (28317 / 171683)) (n := 12)
    (lo := (66583313 / 200000000)) (hi := (166458283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 71683) = 1/(71683 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166458283 / 500000000) (-66583313 / 200000000) (Real.log (71683 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124832367 / 500000000) ≤ -Real.log (200000 / 256719) ∧
    -Real.log (200000 / 256719) ≤ (49932947 / 200000000) := by
  have h := checkLog_sound (w := (56719 / 456719)) (n := 12)
    (lo := (124832367 / 500000000)) (hi := (49932947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256719 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256719 / 200000) = 1/(200000 / 256719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124832367 / 500000000) (49932947 / 200000000) (Real.log (256719 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (256719 / 200000) = -Real.log (200000 / 256719) := by
    rw [show ((256719 / 200000) : ℝ) = ((200000 / 256719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (333509629 / 1000000000) ≤ -Real.log (143281 / 200000) ∧
    -Real.log (143281 / 200000) ≤ (33350963 / 100000000) := by
  have h := checkLog_sound (w := (56719 / 343281)) (n := 12)
    (lo := (333509629 / 1000000000)) (hi := (33350963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143281) = 1/(143281 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33350963 / 100000000) (-333509629 / 1000000000) (Real.log (143281 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186296147 / 1000000000) ≤ -Real.log (1000000 / 1204779) ∧
    -Real.log (1000000 / 1204779) ≤ (46574037 / 250000000) := by
  have h := checkLog_sound (w := (204779 / 2204779)) (n := 12)
    (lo := (186296147 / 1000000000)) (hi := (46574037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204779 / 1000000) = 1/(1000000 / 1204779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186296147 / 1000000000) (46574037 / 250000000) (Real.log (1204779 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204779 / 1000000) = -Real.log (1000000 / 1204779) := by
    rw [show ((1204779 / 1000000) : ℝ) = ((1000000 / 1204779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (45827043 / 200000000) ≤ -Real.log (795221 / 1000000) ∧
    -Real.log (795221 / 1000000) ≤ (14320951 / 62500000) := by
  have h := checkLog_sound (w := (204779 / 1795221)) (n := 12)
    (lo := (45827043 / 200000000)) (hi := (14320951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795221) = 1/(795221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14320951 / 62500000) (-45827043 / 200000000) (Real.log (795221 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186562551 / 1000000000) ≤ -Real.log (10000 / 12051) ∧
    -Real.log (10000 / 12051) ≤ (23320319 / 125000000) := by
  have h := checkLog_sound (w := (2051 / 22051)) (n := 12)
    (lo := (186562551 / 1000000000)) (hi := (23320319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12051 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12051 / 10000) = 1/(10000 / 12051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186562551 / 1000000000) (23320319 / 125000000) (Real.log (12051 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (12051 / 10000) = -Real.log (10000 / 12051) := by
    rw [show ((12051 / 10000) : ℝ) = ((10000 / 12051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (114769479 / 500000000) ≤ -Real.log (7949 / 10000) ∧
    -Real.log (7949 / 10000) ≤ (229538959 / 1000000000) := by
  have h := checkLog_sound (w := (2051 / 17949)) (n := 12)
    (lo := (114769479 / 500000000)) (hi := (229538959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7949) = 1/(7949 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-229538959 / 1000000000) (-114769479 / 500000000) (Real.log (7949 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (841723709 / 1000000000) ≤ -Real.log (12500000000 / 29004539559) ∧
    -Real.log (12500000000 / 29004539559) ≤ (841723711 / 1000000000) := by
  have h := checkLog_sound (w := (4004539559 / 54004539559)) (n := 12)
    (lo := (148576529 / 1000000000)) (hi := (14857653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29004539559 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(29004539559 / 25000000000) = 1/(12500000000 / 29004539559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (841723709 / 1000000000) (841723711 / 1000000000) (Real.log (29004539559 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (29004539559 / 12500000000) = -Real.log (12500000000 / 29004539559) := by
    rw [show ((29004539559 / 12500000000) : ℝ) = ((12500000000 / 29004539559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (421558043 / 500000000) ≤ -Real.log (100000000000 / 232359623499) ∧
    -Real.log (100000000000 / 232359623499) ≤ (105389511 / 125000000) := by
  have h := checkLog_sound (w := (32359623499 / 432359623499)) (n := 12)
    (lo := (74984453 / 500000000)) (hi := (149968907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232359623499 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232359623499 / 200000000000) = 1/(100000000000 / 232359623499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (421558043 / 500000000) (105389511 / 125000000) (Real.log (232359623499 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (232359623499 / 100000000000) = -Real.log (100000000000 / 232359623499) := by
    rw [show ((232359623499 / 100000000000) : ℝ) = ((100000000000 / 232359623499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (18195317 / 31250000) ≤ -Real.log (250000000000 / 447515449967) ∧
    -Real.log (250000000000 / 447515449967) ≤ (116450029 / 200000000) := by
  have h := checkLog_sound (w := (197515449967 / 697515449967)) (n := 12)
    (lo := (18195317 / 31250000)) (hi := (116450029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447515449967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447515449967 / 250000000000) = 1/(250000000000 / 447515449967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18195317 / 31250000) (116450029 / 200000000) (Real.log (447515449967 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (447515449967 / 250000000000) = -Real.log (250000000000 / 447515449967) := by
    rw [show ((447515449967 / 250000000000) : ℝ) = ((250000000000 / 447515449967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145793591 / 250000000) ≤ -Real.log (500000000000 / 895858487867) ∧
    -Real.log (500000000000 / 895858487867) ≤ (116634873 / 200000000) := by
  have h := checkLog_sound (w := (395858487867 / 1395858487867)) (n := 12)
    (lo := (145793591 / 250000000)) (hi := (116634873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895858487867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895858487867 / 500000000000) = 1/(500000000000 / 895858487867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (145793591 / 250000000) (116634873 / 200000000) (Real.log (895858487867 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (895858487867 / 500000000000) = -Real.log (500000000000 / 895858487867) := by
    rw [show ((895858487867 / 500000000000) : ℝ) = ((500000000000 / 895858487867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (415431363 / 1000000000) ≤ -Real.log (125000000000 / 189378015671) ∧
    -Real.log (125000000000 / 189378015671) ≤ (103857841 / 250000000) := by
  have h := checkLog_sound (w := (64378015671 / 314378015671)) (n := 12)
    (lo := (415431363 / 1000000000)) (hi := (103857841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189378015671 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189378015671 / 125000000000) = 1/(125000000000 / 189378015671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (415431363 / 1000000000) (103857841 / 250000000) (Real.log (189378015671 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (189378015671 / 125000000000) = -Real.log (125000000000 / 189378015671) := by
    rw [show ((189378015671 / 125000000000) : ℝ) = ((125000000000 / 189378015671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (416101509 / 1000000000) ≤ -Real.log (100000000000 / 151603975343) ∧
    -Real.log (100000000000 / 151603975343) ≤ (41610151 / 100000000) := by
  have h := checkLog_sound (w := (51603975343 / 251603975343)) (n := 12)
    (lo := (416101509 / 1000000000)) (hi := (41610151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151603975343 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151603975343 / 100000000000) = 1/(100000000000 / 151603975343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (416101509 / 1000000000) (41610151 / 100000000) (Real.log (151603975343 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (151603975343 / 100000000000) = -Real.log (100000000000 / 151603975343) := by
    rw [show ((151603975343 / 100000000000) : ℝ) = ((100000000000 / 151603975343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42976407 / 1000000000) ≤ -Real.log (95793399 / 100000000) ∧
    -Real.log (95793399 / 100000000) ≤ (5372051 / 125000000) := by
  have h := checkLog_sound (w := (4206601 / 195793399)) (n := 12)
    (lo := (42976407 / 1000000000)) (hi := (5372051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 95793399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 95793399) = 1/(95793399 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5372051 / 125000000) (-42976407 / 1000000000) (Real.log (95793399 / 100000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42839067 / 1000000000) ≤ -Real.log (958065561159 / 1000000000000) ∧
    -Real.log (958065561159 / 1000000000000) ≤ (10709767 / 250000000) := by
  have h := checkLog_sound (w := (41934438841 / 1958065561159)) (n := 12)
    (lo := (42839067 / 1000000000)) (hi := (10709767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958065561159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958065561159) = 1/(958065561159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10709767 / 250000000) (-42839067 / 1000000000) (Real.log (958065561159 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell252
