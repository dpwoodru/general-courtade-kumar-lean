import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell072
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

theorem reflection_log_1_neg : (128394931 / 500000000) ≤ -Real.log (5120 / 6619) ∧
    -Real.log (5120 / 6619) ≤ (256789863 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 11739)) (n := 12)
    (lo := (128394931 / 500000000)) (hi := (256789863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6619 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6619 / 5120) = 1/(5120 / 6619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128394931 / 500000000) (256789863 / 1000000000) (Real.log (6619 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6619 / 5120) = -Real.log (5120 / 6619) := by
    rw [show ((6619 / 5120) : ℝ) = ((5120 / 6619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (21650263 / 62500000) ≤ -Real.log (3621 / 5120) ∧
    -Real.log (3621 / 5120) ≤ (346404209 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 8741)) (n := 12)
    (lo := (21650263 / 62500000)) (hi := (346404209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3621) = 1/(3621 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-346404209 / 1000000000) (-21650263 / 62500000) (Real.log (3621 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128168259 / 500000000) ≤ -Real.log (640 / 827) ∧
    -Real.log (640 / 827) ≤ (256336519 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1467)) (n := 12)
    (lo := (128168259 / 500000000)) (hi := (256336519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827 / 640) = 1/(640 / 827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128168259 / 500000000) (256336519 / 1000000000) (Real.log (827 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (827 / 640) = -Real.log (640 / 827) := by
    rw [show ((827 / 640) : ℝ) = ((640 / 827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6911521 / 20000000) ≤ -Real.log (453 / 640) ∧
    -Real.log (453 / 640) ≤ (345576051 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 453) = 1/(453 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345576051 / 1000000000) (-6911521 / 20000000) (Real.log (453 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47110903 / 250000000) ≤ -Real.log (1000000 / 1207369) ∧
    -Real.log (1000000 / 1207369) ≤ (188443613 / 1000000000) := by
  have h := checkLog_sound (w := (207369 / 2207369)) (n := 12)
    (lo := (47110903 / 250000000)) (hi := (188443613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207369 / 1000000) = 1/(1000000 / 1207369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47110903 / 250000000) (188443613 / 1000000000) (Real.log (1207369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1207369 / 1000000) = -Real.log (1000000 / 1207369) := by
    rw [show ((1207369 / 1000000) : ℝ) = ((1000000 / 1207369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (232397487 / 1000000000) ≤ -Real.log (792631 / 1000000) ∧
    -Real.log (792631 / 1000000) ≤ (14524843 / 62500000) := by
  have h := checkLog_sound (w := (207369 / 1792631)) (n := 12)
    (lo := (232397487 / 1000000000)) (hi := (14524843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792631) = 1/(792631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14524843 / 62500000) (-232397487 / 1000000000) (Real.log (792631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37758283 / 200000000) ≤ -Real.log (1000000 / 1207789) ∧
    -Real.log (1000000 / 1207789) ≤ (23598927 / 125000000) := by
  have h := checkLog_sound (w := (207789 / 2207789)) (n := 12)
    (lo := (37758283 / 200000000)) (hi := (23598927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207789 / 1000000) = 1/(1000000 / 1207789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37758283 / 200000000) (23598927 / 125000000) (Real.log (1207789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1207789 / 1000000) = -Real.log (1000000 / 1207789) := by
    rw [show ((1207789 / 1000000) : ℝ) = ((1000000 / 1207789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58231877 / 250000000) ≤ -Real.log (792211 / 1000000) ∧
    -Real.log (792211 / 1000000) ≤ (232927509 / 1000000000) := by
  have h := checkLog_sound (w := (207789 / 1792211)) (n := 12)
    (lo := (58231877 / 250000000)) (hi := (232927509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792211) = 1/(792211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-232927509 / 1000000000) (-58231877 / 250000000) (Real.log (792211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6918527 / 50000000) ≤ -Real.log (1000000 / 1148401) ∧
    -Real.log (1000000 / 1148401) ≤ (138370541 / 1000000000) := by
  have h := checkLog_sound (w := (148401 / 2148401)) (n := 12)
    (lo := (6918527 / 50000000)) (hi := (138370541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148401 / 1000000) = 1/(1000000 / 1148401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6918527 / 50000000) (138370541 / 1000000000) (Real.log (1148401 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1148401 / 1000000) = -Real.log (1000000 / 1148401) := by
    rw [show ((1148401 / 1000000) : ℝ) = ((1000000 / 1148401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1003997 / 6250000) ≤ -Real.log (851599 / 1000000) ∧
    -Real.log (851599 / 1000000) ≤ (160639521 / 1000000000) := by
  have h := checkLog_sound (w := (148401 / 1851599)) (n := 12)
    (lo := (1003997 / 6250000)) (hi := (160639521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851599) = 1/(851599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160639521 / 1000000000) (-1003997 / 6250000) (Real.log (851599 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138638703 / 1000000000) ≤ -Real.log (1000000 / 1148709) ∧
    -Real.log (1000000 / 1148709) ≤ (8664919 / 62500000) := by
  have h := checkLog_sound (w := (148709 / 2148709)) (n := 12)
    (lo := (138638703 / 1000000000)) (hi := (8664919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148709 / 1000000) = 1/(1000000 / 1148709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138638703 / 1000000000) (8664919 / 62500000) (Real.log (1148709 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1148709 / 1000000) = -Real.log (1000000 / 1148709) := by
    rw [show ((1148709 / 1000000) : ℝ) = ((1000000 / 1148709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80500629 / 500000000) ≤ -Real.log (851291 / 1000000) ∧
    -Real.log (851291 / 1000000) ≤ (161001259 / 1000000000) := by
  have h := checkLog_sound (w := (148709 / 1851291)) (n := 12)
    (lo := (80500629 / 500000000)) (hi := (161001259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851291) = 1/(851291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-161001259 / 1000000000) (-80500629 / 500000000) (Real.log (851291 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (601912569 / 1000000000) ≤ -Real.log (62500000000 / 114100441501) ∧
    -Real.log (62500000000 / 114100441501) ≤ (60191257 / 100000000) := by
  have h := checkLog_sound (w := (51600441501 / 176600441501)) (n := 12)
    (lo := (601912569 / 1000000000)) (hi := (60191257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114100441501 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114100441501 / 62500000000) = 1/(62500000000 / 114100441501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (601912569 / 1000000000) (60191257 / 100000000) (Real.log (114100441501 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (114100441501 / 62500000000) = -Real.log (62500000000 / 114100441501) := by
    rw [show ((114100441501 / 62500000000) : ℝ) = ((62500000000 / 114100441501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (60319407 / 100000000) ≤ -Real.log (500000000000 / 913974040321) ∧
    -Real.log (500000000000 / 913974040321) ≤ (603194071 / 1000000000) := by
  have h := checkLog_sound (w := (413974040321 / 1413974040321)) (n := 12)
    (lo := (60319407 / 100000000)) (hi := (603194071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913974040321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913974040321 / 500000000000) = 1/(500000000000 / 913974040321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (60319407 / 100000000) (603194071 / 1000000000) (Real.log (913974040321 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (913974040321 / 500000000000) = -Real.log (500000000000 / 913974040321) := by
    rw [show ((913974040321 / 500000000000) : ℝ) = ((500000000000 / 913974040321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (420841099 / 1000000000) ≤ -Real.log (20000000000 / 30464844297) ∧
    -Real.log (20000000000 / 30464844297) ≤ (4208411 / 10000000) := by
  have h := checkLog_sound (w := (10464844297 / 50464844297)) (n := 12)
    (lo := (420841099 / 1000000000)) (hi := (4208411 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30464844297 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30464844297 / 20000000000) = 1/(20000000000 / 30464844297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (420841099 / 1000000000) (4208411 / 10000000) (Real.log (30464844297 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30464844297 / 20000000000) = -Real.log (20000000000 / 30464844297) := by
    rw [show ((30464844297 / 20000000000) : ℝ) = ((20000000000 / 30464844297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (421718923 / 1000000000) ≤ -Real.log (62500000000 / 95286246341) ∧
    -Real.log (62500000000 / 95286246341) ≤ (105429731 / 250000000) := by
  have h := checkLog_sound (w := (32786246341 / 157786246341)) (n := 12)
    (lo := (421718923 / 1000000000)) (hi := (105429731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95286246341 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95286246341 / 62500000000) = 1/(62500000000 / 95286246341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (421718923 / 1000000000) (105429731 / 250000000) (Real.log (95286246341 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (95286246341 / 62500000000) = -Real.log (62500000000 / 95286246341) := by
    rw [show ((95286246341 / 62500000000) : ℝ) = ((62500000000 / 95286246341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14950503 / 50000000) ≤ -Real.log (62500000000 / 84282699369) ∧
    -Real.log (62500000000 / 84282699369) ≤ (299010061 / 1000000000) := by
  have h := checkLog_sound (w := (21782699369 / 146782699369)) (n := 12)
    (lo := (14950503 / 50000000)) (hi := (299010061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84282699369 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84282699369 / 62500000000) = 1/(62500000000 / 84282699369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14950503 / 50000000) (299010061 / 1000000000) (Real.log (84282699369 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84282699369 / 62500000000) = -Real.log (62500000000 / 84282699369) := by
    rw [show ((84282699369 / 62500000000) : ℝ) = ((62500000000 / 84282699369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (299639961 / 1000000000) ≤ -Real.log (500000000000 / 674686446821) ∧
    -Real.log (500000000000 / 674686446821) ≤ (149819981 / 500000000) := by
  have h := checkLog_sound (w := (174686446821 / 1174686446821)) (n := 12)
    (lo := (299639961 / 1000000000)) (hi := (149819981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674686446821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674686446821 / 500000000000) = 1/(500000000000 / 674686446821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (299639961 / 1000000000) (149819981 / 500000000) (Real.log (674686446821 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (674686446821 / 500000000000) = -Real.log (500000000000 / 674686446821) := by
    rw [show ((674686446821 / 500000000000) : ℝ) = ((500000000000 / 674686446821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4472511 / 200000000) ≤ -Real.log (977885633319 / 1000000000000) ∧
    -Real.log (977885633319 / 1000000000000) ≤ (5590639 / 250000000) := by
  have h := checkLog_sound (w := (22114366681 / 1977885633319)) (n := 12)
    (lo := (4472511 / 200000000)) (hi := (5590639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977885633319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977885633319) = 1/(977885633319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5590639 / 250000000) (-4472511 / 200000000) (Real.log (977885633319 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1113449 / 50000000) ≤ -Real.log (977977143199 / 1000000000000) ∧
    -Real.log (977977143199 / 1000000000000) ≤ (22268981 / 1000000000) := by
  have h := checkLog_sound (w := (22022856801 / 1977977143199)) (n := 12)
    (lo := (1113449 / 50000000)) (hi := (22268981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977977143199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977977143199) = 1/(977977143199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22268981 / 1000000000) (-1113449 / 50000000) (Real.log (977977143199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell072
