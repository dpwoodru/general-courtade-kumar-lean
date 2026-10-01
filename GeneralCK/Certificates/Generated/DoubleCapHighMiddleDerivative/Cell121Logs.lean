import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell121
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

theorem reflection_log_1_neg : (278755631 / 1000000000) ≤ -Real.log (2560 / 3383) ∧
    -Real.log (2560 / 3383) ≤ (17422227 / 62500000) := by
  have h := checkLog_sound (w := (823 / 5943)) (n := 12)
    (lo := (278755631 / 1000000000)) (hi := (17422227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3383 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3383 / 2560) = 1/(2560 / 3383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (278755631 / 1000000000) (17422227 / 62500000) (Real.log (3383 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3383 / 2560) = -Real.log (2560 / 3383) := by
    rw [show ((3383 / 2560) : ℝ) = ((2560 / 3383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (387847771 / 1000000000) ≤ -Real.log (1737 / 2560) ∧
    -Real.log (1737 / 2560) ≤ (96961943 / 250000000) := by
  have h := checkLog_sound (w := (823 / 4297)) (n := 12)
    (lo := (387847771 / 1000000000)) (hi := (96961943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1737) = 1/(1737 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-96961943 / 250000000) (-387847771 / 1000000000) (Real.log (1737 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (278312139 / 1000000000) ≤ -Real.log (5120 / 6763) ∧
    -Real.log (5120 / 6763) ≤ (13915607 / 50000000) := by
  have h := checkLog_sound (w := (1643 / 11883)) (n := 12)
    (lo := (278312139 / 1000000000)) (hi := (13915607 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6763 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6763 / 5120) = 1/(5120 / 6763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (278312139 / 1000000000) (13915607 / 50000000) (Real.log (6763 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6763 / 5120) = -Real.log (5120 / 6763) := by
    rw [show ((6763 / 5120) : ℝ) = ((5120 / 6763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (193492293 / 500000000) ≤ -Real.log (3477 / 5120) ∧
    -Real.log (3477 / 5120) ≤ (386984587 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 8597)) (n := 12)
    (lo := (193492293 / 500000000)) (hi := (386984587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3477) = 1/(3477 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-386984587 / 1000000000) (-193492293 / 500000000) (Real.log (3477 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (205326567 / 1000000000) ≤ -Real.log (500000 / 613963) ∧
    -Real.log (500000 / 613963) ≤ (25665821 / 125000000) := by
  have h := checkLog_sound (w := (113963 / 1113963)) (n := 12)
    (lo := (205326567 / 1000000000)) (hi := (25665821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613963 / 500000) = 1/(500000 / 613963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (205326567 / 1000000000) (25665821 / 125000000) (Real.log (613963 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613963 / 500000) = -Real.log (500000 / 613963) := by
    rw [show ((613963 / 500000) : ℝ) = ((500000 / 613963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (129337439 / 500000000) ≤ -Real.log (386037 / 500000) ∧
    -Real.log (386037 / 500000) ≤ (258674879 / 1000000000) := by
  have h := checkLog_sound (w := (113963 / 886037)) (n := 12)
    (lo := (129337439 / 500000000)) (hi := (258674879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386037) = 1/(386037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258674879 / 1000000000) (-129337439 / 500000000) (Real.log (386037 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (205670177 / 1000000000) ≤ -Real.log (250000 / 307087) ∧
    -Real.log (250000 / 307087) ≤ (102835089 / 500000000) := by
  have h := checkLog_sound (w := (57087 / 557087)) (n := 12)
    (lo := (205670177 / 1000000000)) (hi := (102835089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307087 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307087 / 250000) = 1/(250000 / 307087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (205670177 / 1000000000) (102835089 / 500000000) (Real.log (307087 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307087 / 250000) = -Real.log (250000 / 307087) := by
    rw [show ((307087 / 250000) : ℝ) = ((250000 / 307087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (259221607 / 1000000000) ≤ -Real.log (192913 / 250000) ∧
    -Real.log (192913 / 250000) ≤ (32402701 / 125000000) := by
  have h := checkLog_sound (w := (57087 / 442913)) (n := 12)
    (lo := (259221607 / 1000000000)) (hi := (32402701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192913) = 1/(192913 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32402701 / 125000000) (-259221607 / 1000000000) (Real.log (192913 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37862903 / 250000000) ≤ -Real.log (500000 / 581761) ∧
    -Real.log (500000 / 581761) ≤ (151451613 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 1081761)) (n := 12)
    (lo := (37862903 / 250000000)) (hi := (151451613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581761 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581761 / 500000) = 1/(500000 / 581761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37862903 / 250000000) (151451613 / 1000000000) (Real.log (581761 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581761 / 500000) = -Real.log (500000 / 581761) := by
    rw [show ((581761 / 500000) : ℝ) = ((500000 / 581761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89277529 / 500000000) ≤ -Real.log (418239 / 500000) ∧
    -Real.log (418239 / 500000) ≤ (178555059 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 918239)) (n := 12)
    (lo := (89277529 / 500000000)) (hi := (178555059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418239) = 1/(418239 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178555059 / 1000000000) (-89277529 / 500000000) (Real.log (418239 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37929717 / 250000000) ≤ -Real.log (1000000 / 1163833) ∧
    -Real.log (1000000 / 1163833) ≤ (151718869 / 1000000000) := by
  have h := checkLog_sound (w := (163833 / 2163833)) (n := 12)
    (lo := (37929717 / 250000000)) (hi := (151718869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163833 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163833 / 1000000) = 1/(1000000 / 1163833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37929717 / 250000000) (151718869 / 1000000000) (Real.log (1163833 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163833 / 1000000) = -Real.log (1000000 / 1163833) := by
    rw [show ((1163833 / 1000000) : ℝ) = ((1000000 / 1163833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7157077 / 40000000) ≤ -Real.log (836167 / 1000000) ∧
    -Real.log (836167 / 1000000) ≤ (89463463 / 500000000) := by
  have h := checkLog_sound (w := (163833 / 1836167)) (n := 12)
    (lo := (7157077 / 40000000)) (hi := (89463463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836167) = 1/(836167 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-89463463 / 500000000) (-7157077 / 40000000) (Real.log (836167 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26611869 / 40000000) ≤ -Real.log (1000000000 / 1945067587) ∧
    -Real.log (1000000000 / 1945067587) ≤ (332648363 / 500000000) := by
  have h := checkLog_sound (w := (945067587 / 2945067587)) (n := 12)
    (lo := (26611869 / 40000000)) (hi := (332648363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945067587 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945067587 / 1000000000) = 1/(1000000000 / 1945067587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26611869 / 40000000) (332648363 / 500000000) (Real.log (1945067587 / 1000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1945067587 / 1000000000) = -Real.log (1000000000 / 1945067587) := by
    rw [show ((1945067587 / 1000000000) : ℝ) = ((1000000000 / 1945067587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (333301701 / 500000000) ≤ -Real.log (50000000000 / 97380541163) ∧
    -Real.log (50000000000 / 97380541163) ≤ (666603403 / 1000000000) := by
  have h := checkLog_sound (w := (47380541163 / 147380541163)) (n := 12)
    (lo := (333301701 / 500000000)) (hi := (666603403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97380541163 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97380541163 / 50000000000) = 1/(50000000000 / 97380541163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (333301701 / 500000000) (666603403 / 1000000000) (Real.log (97380541163 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (97380541163 / 50000000000) = -Real.log (50000000000 / 97380541163) := by
    rw [show ((97380541163 / 50000000000) : ℝ) = ((50000000000 / 97380541163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92800289 / 200000000) ≤ -Real.log (250000000000 / 397606317529) ∧
    -Real.log (250000000000 / 397606317529) ≤ (232000723 / 500000000) := by
  have h := checkLog_sound (w := (147606317529 / 647606317529)) (n := 12)
    (lo := (92800289 / 200000000)) (hi := (232000723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397606317529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397606317529 / 250000000000) = 1/(250000000000 / 397606317529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92800289 / 200000000) (232000723 / 500000000) (Real.log (397606317529 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (397606317529 / 250000000000) = -Real.log (250000000000 / 397606317529) := by
    rw [show ((397606317529 / 250000000000) : ℝ) = ((250000000000 / 397606317529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58111473 / 125000000) ≤ -Real.log (500000000000 / 795920959189) ∧
    -Real.log (500000000000 / 795920959189) ≤ (92978357 / 200000000) := by
  have h := checkLog_sound (w := (295920959189 / 1295920959189)) (n := 12)
    (lo := (58111473 / 125000000)) (hi := (92978357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795920959189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795920959189 / 500000000000) = 1/(500000000000 / 795920959189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (58111473 / 125000000) (92978357 / 200000000) (Real.log (795920959189 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (795920959189 / 500000000000) = -Real.log (500000000000 / 795920959189) := by
    rw [show ((795920959189 / 500000000000) : ℝ) = ((500000000000 / 795920959189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (330006671 / 1000000000) ≤ -Real.log (500000000000 / 695488703827) ∧
    -Real.log (500000000000 / 695488703827) ≤ (20625417 / 62500000) := by
  have h := checkLog_sound (w := (195488703827 / 1195488703827)) (n := 12)
    (lo := (330006671 / 1000000000)) (hi := (20625417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695488703827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695488703827 / 500000000000) = 1/(500000000000 / 695488703827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (330006671 / 1000000000) (20625417 / 62500000) (Real.log (695488703827 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (695488703827 / 500000000000) = -Real.log (500000000000 / 695488703827) := by
    rw [show ((695488703827 / 500000000000) : ℝ) = ((500000000000 / 695488703827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (330645793 / 1000000000) ≤ -Real.log (500000000000 / 695933348243) ∧
    -Real.log (500000000000 / 695933348243) ≤ (165322897 / 500000000) := by
  have h := checkLog_sound (w := (195933348243 / 1195933348243)) (n := 12)
    (lo := (330645793 / 1000000000)) (hi := (165322897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695933348243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695933348243 / 500000000000) = 1/(500000000000 / 695933348243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (330645793 / 1000000000) (165322897 / 500000000) (Real.log (695933348243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695933348243 / 500000000000) = -Real.log (500000000000 / 695933348243) := by
    rw [show ((695933348243 / 500000000000) : ℝ) = ((500000000000 / 695933348243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3401007 / 125000000) ≤ -Real.log (973158748111 / 1000000000000) ∧
    -Real.log (973158748111 / 1000000000000) ≤ (27208057 / 1000000000) := by
  have h := checkLog_sound (w := (26841251889 / 1973158748111)) (n := 12)
    (lo := (3401007 / 125000000)) (hi := (27208057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973158748111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973158748111) = 1/(973158748111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27208057 / 1000000000) (-3401007 / 125000000) (Real.log (973158748111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13551723 / 500000000) ≤ -Real.log (243315138879 / 250000000000) ∧
    -Real.log (243315138879 / 250000000000) ≤ (27103447 / 1000000000) := by
  have h := checkLog_sound (w := (6684861121 / 493315138879)) (n := 12)
    (lo := (13551723 / 500000000)) (hi := (27103447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243315138879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243315138879) = 1/(243315138879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27103447 / 1000000000) (-13551723 / 500000000) (Real.log (243315138879 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell121
