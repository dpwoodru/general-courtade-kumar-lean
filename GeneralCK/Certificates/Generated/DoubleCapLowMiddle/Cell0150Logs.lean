import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150
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

theorem reflection_log_1_neg : (130684643 / 200000000) ≤ -Real.log (12800 / 24603) ∧
    -Real.log (12800 / 24603) ≤ (40838951 / 62500000) := by
  have h := checkLog_sound (w := (11803 / 37403)) (n := 12)
    (lo := (130684643 / 200000000)) (hi := (40838951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 12800) = 1/(12800 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130684643 / 200000000) (40838951 / 62500000) (Real.log (24603 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24603 / 12800) = -Real.log (12800 / 24603) := by
    rw [show ((24603 / 12800) : ℝ) = ((12800 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1276224839 / 500000000) ≤ -Real.log (997 / 12800) ∧
    -Real.log (997 / 12800) ≤ (1276224841 / 500000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 997) = 1/(997 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1276224841 / 500000000) (-1276224839 / 500000000) (Real.log (997 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (652650653 / 1000000000) ≤ -Real.log (1600 / 3073) ∧
    -Real.log (1600 / 3073) ≤ (326325327 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4673)) (n := 12)
    (lo := (652650653 / 1000000000)) (hi := (326325327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3073 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3073 / 1600) = 1/(1600 / 3073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (652650653 / 1000000000) (326325327 / 500000000) (Real.log (3073 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3073 / 1600) = -Real.log (1600 / 3073) := by
    rw [show ((3073 / 1600) : ℝ) = ((1600 / 3073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126678591 / 50000000) ≤ -Real.log (127 / 1600) ∧
    -Real.log (127 / 1600) ≤ (158348239 / 62500000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 127) = 1/(127 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) (Real.log (127 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (306027873 / 500000000) ≤ -Real.log (6400 / 11803) ∧
    -Real.log (6400 / 11803) ≤ (612055747 / 1000000000) := by
  have h := checkLog_sound (w := (5403 / 18203)) (n := 12)
    (lo := (306027873 / 500000000)) (hi := (612055747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 6400) = 1/(6400 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (306027873 / 500000000) (612055747 / 1000000000) (Real.log (11803 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11803 / 6400) = -Real.log (6400 / 11803) := by
    rw [show ((11803 / 6400) : ℝ) = ((6400 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (929651249 / 500000000) ≤ -Real.log (997 / 6400) ∧
    -Real.log (997 / 6400) ≤ (1859302501 / 1000000000) := by
  have h := checkLog_sound (w := (603 / 2597)) (n := 12)
    (lo := (236504069 / 500000000)) (hi := (473008139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 997) = 1/(997 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1859302501 / 1000000000) (-929651249 / 500000000) (Real.log (997 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (38152793 / 62500000) ≤ -Real.log (800 / 1473) ∧
    -Real.log (800 / 1473) ≤ (610444689 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 2273)) (n := 12)
    (lo := (38152793 / 62500000)) (hi := (610444689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 800) = 1/(800 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (38152793 / 62500000) (610444689 / 1000000000) (Real.log (1473 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1473 / 800) = -Real.log (800 / 1473) := by
    rw [show ((1473 / 800) : ℝ) = ((800 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5751327 / 3125000) ≤ -Real.log (127 / 800) ∧
    -Real.log (127 / 800) ≤ (1840424643 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 127) = 1/(127 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) (Real.log (127 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (330765301 / 500000000) ≤ -Real.log (250000 / 484439) ∧
    -Real.log (250000 / 484439) ≤ (661530603 / 1000000000) := by
  have h := checkLog_sound (w := (234439 / 734439)) (n := 12)
    (lo := (330765301 / 500000000)) (hi := (661530603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484439 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484439 / 250000) = 1/(250000 / 484439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (330765301 / 500000000) (661530603 / 1000000000) (Real.log (484439 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (484439 / 250000) = -Real.log (250000 / 484439) := by
    rw [show ((484439 / 250000) : ℝ) = ((250000 / 484439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2776693131 / 1000000000) ≤ -Real.log (15561 / 250000) ∧
    -Real.log (15561 / 250000) ≤ (173543321 / 62500000) := by
  have h := checkLog_sound (w := (32 / 15593)) (n := 12)
    (lo := (4104411 / 1000000000)) (hi := (1026103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15561) = 1/(15561 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-173543321 / 62500000) (-2776693131 / 1000000000) (Real.log (15561 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (662077993 / 1000000000) ≤ -Real.log (1000000 / 1938817) ∧
    -Real.log (1000000 / 1938817) ≤ (331038997 / 500000000) := by
  have h := checkLog_sound (w := (938817 / 2938817)) (n := 12)
    (lo := (662077993 / 1000000000)) (hi := (331038997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1938817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1938817 / 1000000) = 1/(1000000 / 1938817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (662077993 / 1000000000) (331038997 / 500000000) (Real.log (1938817 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1938817 / 1000000) = -Real.log (1000000 / 1938817) := by
    rw [show ((1938817 / 1000000) : ℝ) = ((1000000 / 1938817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2793885903 / 1000000000) ≤ -Real.log (61183 / 1000000) ∧
    -Real.log (61183 / 1000000) ≤ (698471477 / 250000000) := by
  have h := checkLog_sound (w := (1317 / 123683)) (n := 12)
    (lo := (21297183 / 1000000000)) (hi := (665537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61183) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 61183) = 1/(61183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-698471477 / 250000000) (-2793885903 / 1000000000) (Real.log (61183 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (660816119 / 1000000000) ≤ -Real.log (250000 / 484093) ∧
    -Real.log (250000 / 484093) ≤ (16520403 / 25000000) := by
  have h := checkLog_sound (w := (234093 / 734093)) (n := 12)
    (lo := (660816119 / 1000000000)) (hi := (16520403 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484093 / 250000) = 1/(250000 / 484093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (660816119 / 1000000000) (16520403 / 25000000) (Real.log (484093 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (484093 / 250000) = -Real.log (250000 / 484093) := by
    rw [show ((484093 / 250000) : ℝ) = ((250000 / 484093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (688675413 / 250000000) ≤ -Real.log (15907 / 250000) ∧
    -Real.log (15907 / 250000) ≤ (344337707 / 125000000) := by
  have h := checkLog_sound (w := (15343 / 47157)) (n := 12)
    (lo := (42203757 / 62500000)) (hi := (675260113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15907) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 15907) = 1/(15907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-344337707 / 125000000) (-688675413 / 250000000) (Real.log (15907 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (661394353 / 1000000000) ≤ -Real.log (250000 / 484373) ∧
    -Real.log (250000 / 484373) ≤ (330697177 / 500000000) := by
  have h := checkLog_sound (w := (234373 / 734373)) (n := 12)
    (lo := (661394353 / 1000000000)) (hi := (330697177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484373 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484373 / 250000) = 1/(250000 / 484373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (661394353 / 1000000000) (330697177 / 500000000) (Real.log (484373 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (484373 / 250000) = -Real.log (250000 / 484373) := by
    rw [show ((484373 / 250000) : ℝ) = ((250000 / 484373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (346557591 / 125000000) ≤ -Real.log (15627 / 250000) ∧
    -Real.log (15627 / 250000) ≤ (693115183 / 250000000) := by
  have h := checkLog_sound (w := (15623 / 46877)) (n := 12)
    (lo := (173254797 / 250000000)) (hi := (693019189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 15627) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 15627) = 1/(15627 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-693115183 / 250000000) (-346557591 / 125000000) (Real.log (15627 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1719111867 / 500000000) ≤ -Real.log (500000000000 / 15565805539489) ∧
    -Real.log (500000000000 / 15565805539489) ≤ (3438223739 / 1000000000) := by
  have h := checkLog_sound (w := (7565805539489 / 23565805539489)) (n := 12)
    (lo := (332817507 / 500000000)) (hi := (133127003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15565805539489 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15565805539489 / 8000000000000) = 1/(500000000000 / 15565805539489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1719111867 / 500000000) (3438223739 / 1000000000) (Real.log (15565805539489 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15565805539489 / 500000000000) = -Real.log (500000000000 / 15565805539489) := by
    rw [show ((15565805539489 / 500000000000) : ℝ) = ((500000000000 / 15565805539489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (431995487 / 125000000) ≤ -Real.log (500000000000 / 15844409394767) ∧
    -Real.log (500000000000 / 15844409394767) ≤ (3455963901 / 1000000000) := by
  have h := checkLog_sound (w := (7844409394767 / 23844409394767)) (n := 12)
    (lo := (85421897 / 125000000)) (hi := (683375177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15844409394767 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15844409394767 / 8000000000000) = 1/(500000000000 / 15844409394767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (431995487 / 125000000) (3455963901 / 1000000000) (Real.log (15844409394767 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15844409394767 / 500000000000) = -Real.log (500000000000 / 15844409394767) := by
    rw [show ((15844409394767 / 500000000000) : ℝ) = ((500000000000 / 15844409394767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (341551777 / 100000000) ≤ -Real.log (125000000000 / 3804087822971) ∧
    -Real.log (125000000000 / 3804087822971) ≤ (136620711 / 40000000) := by
  have h := checkLog_sound (w := (1804087822971 / 5804087822971)) (n := 12)
    (lo := (12858581 / 20000000)) (hi := (642929051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3804087822971 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3804087822971 / 2000000000000) = 1/(125000000000 / 3804087822971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (341551777 / 100000000) (136620711 / 40000000) (Real.log (3804087822971 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3804087822971 / 125000000000) = -Real.log (125000000000 / 3804087822971) := by
    rw [show ((3804087822971 / 125000000000) : ℝ) = ((125000000000 / 3804087822971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3433855081 / 1000000000) ≤ -Real.log (500000000000 / 15497952262111) ∧
    -Real.log (500000000000 / 15497952262111) ≤ (1716927543 / 500000000) := by
  have h := checkLog_sound (w := (7497952262111 / 23497952262111)) (n := 12)
    (lo := (661266361 / 1000000000)) (hi := (330633181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15497952262111 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15497952262111 / 8000000000000) = 1/(500000000000 / 15497952262111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3433855081 / 1000000000) (1716927543 / 500000000) (Real.log (15497952262111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (15497952262111 / 500000000000) = -Real.log (500000000000 / 15497952262111) := by
    rw [show ((15497952262111 / 500000000000) : ℝ) = ((500000000000 / 15497952262111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0150
