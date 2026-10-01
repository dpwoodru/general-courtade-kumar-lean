import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_128_neg : (303917901 / 1000000000) ≤ -Real.log (250000000000 / 338789448893) ∧
    -Real.log (250000000000 / 338789448893) ≤ (151958951 / 500000000) := by
  have h := checkLog_sound (w := (88789448893 / 588789448893)) (n := 12)
    (lo := (303917901 / 1000000000)) (hi := (151958951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338789448893 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338789448893 / 250000000000) = 1/(250000000000 / 338789448893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_128 : Bounds (303917901 / 1000000000) (151958951 / 500000000) (Real.log (338789448893 / 250000000000)) := by
  have h := reflection_log_128_neg
  have he : Real.log (338789448893 / 250000000000) = -Real.log (250000000000 / 338789448893) := by
    rw [show ((338789448893 / 250000000000) : ℝ) = ((250000000000 / 338789448893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_129_neg : (152061279 / 500000000) ≤ -Real.log (125000000000 / 169429395831) ∧
    -Real.log (125000000000 / 169429395831) ≤ (304122559 / 1000000000) := by
  have h := checkLog_sound (w := (44429395831 / 294429395831)) (n := 12)
    (lo := (152061279 / 500000000)) (hi := (304122559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169429395831 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169429395831 / 125000000000) = 1/(125000000000 / 169429395831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_129 : Bounds (152061279 / 500000000) (304122559 / 1000000000) (Real.log (169429395831 / 125000000000)) := by
  have h := reflection_log_129_neg
  have he : Real.log (169429395831 / 125000000000) = -Real.log (125000000000 / 169429395831) := by
    rw [show ((169429395831 / 125000000000) : ℝ) = ((125000000000 / 169429395831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_130_neg : (140631129 / 1000000000) ≤ -Real.log (1000 / 1151) ∧
    -Real.log (1000 / 1151) ≤ (14063113 / 100000000) := by
  have h := checkLog_sound (w := (151 / 2151)) (n := 12)
    (lo := (140631129 / 1000000000)) (hi := (14063113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 1000) = 1/(1000 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_130 : Bounds (140631129 / 1000000000) (14063113 / 100000000) (Real.log (1151 / 1000)) := by
  have h := reflection_log_130_neg
  have he : Real.log (1151 / 1000) = -Real.log (1000 / 1151) := by
    rw [show ((1151 / 1000) : ℝ) = ((1000 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_131_neg : (40924023 / 250000000) ≤ -Real.log (849 / 1000) ∧
    -Real.log (849 / 1000) ≤ (163696093 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 1849)) (n := 12)
    (lo := (40924023 / 250000000)) (hi := (163696093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 849) = 1/(849 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_131 : Bounds (-163696093 / 1000000000) (-40924023 / 250000000) (Real.log (849 / 1000)) := by
  have h := reflection_log_131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_132_neg : (37747 / 250000000) ≤ -Real.log (1000000 / 1000151) ∧
    -Real.log (1000000 / 1000151) ≤ (150989 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 2000151)) (n := 12)
    (lo := (37747 / 250000000)) (hi := (150989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000151 / 1000000) = 1/(1000000 / 1000151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_132 : Bounds (37747 / 250000000) (150989 / 1000000000) (Real.log (1000151 / 1000000)) := by
  have h := reflection_log_132_neg
  have he : Real.log (1000151 / 1000000) = -Real.log (1000000 / 1000151) := by
    rw [show ((1000151 / 1000000) : ℝ) = ((1000000 / 1000151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_133_neg : (151011 / 1000000000) ≤ -Real.log (999849 / 1000000) ∧
    -Real.log (999849 / 1000000) ≤ (37753 / 250000000) := by
  have h := checkLog_sound (w := (151 / 1999849)) (n := 12)
    (lo := (151011 / 1000000000)) (hi := (37753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999849) = 1/(999849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_133 : Bounds (-37753 / 250000000) (-151011 / 1000000000) (Real.log (999849 / 1000000)) := by
  have h := reflection_log_133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_134_neg : (73146367 / 1000000000) ≤ -Real.log (62500 / 67243) ∧
    -Real.log (62500 / 67243) ≤ (142864 / 1953125) := by
  have h := checkLog_sound (w := (4743 / 129743)) (n := 12)
    (lo := (73146367 / 1000000000)) (hi := (142864 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67243 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67243 / 62500) = 1/(62500 / 67243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_134 : Bounds (73146367 / 1000000000) (142864 / 1953125) (Real.log (67243 / 62500)) := by
  have h := reflection_log_134_neg
  have he : Real.log (67243 / 62500) = -Real.log (62500 / 67243) := by
    rw [show ((67243 / 62500) : ℝ) = ((62500 / 67243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_135_neg : (39461001 / 500000000) ≤ -Real.log (57757 / 62500) ∧
    -Real.log (57757 / 62500) ≤ (78922003 / 1000000000) := by
  have h := checkLog_sound (w := (4743 / 120257)) (n := 12)
    (lo := (39461001 / 500000000)) (hi := (78922003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57757) = 1/(57757 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_135 : Bounds (-78922003 / 1000000000) (-39461001 / 500000000) (Real.log (57757 / 62500)) := by
  have h := reflection_log_135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_136_neg : (1155127 / 200000000) ≤ -Real.log (3883753951 / 3906250000) ∧
    -Real.log (3883753951 / 3906250000) ≤ (1443909 / 250000000) := by
  have h := checkLog_sound (w := (22496049 / 7790003951)) (n := 12)
    (lo := (1155127 / 200000000)) (hi := (1443909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3883753951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3883753951) = 1/(3883753951 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_136 : Bounds (-1443909 / 250000000) (-1155127 / 200000000) (Real.log (3883753951 / 3906250000)) := by
  have h := reflection_log_136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_137_neg : (30332407 / 200000000) ≤ -Real.log (62500000000 / 72735428653) ∧
    -Real.log (62500000000 / 72735428653) ≤ (37915509 / 250000000) := by
  have h := checkLog_sound (w := (10235428653 / 135235428653)) (n := 12)
    (lo := (30332407 / 200000000)) (hi := (37915509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72735428653 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72735428653 / 62500000000) = 1/(62500000000 / 72735428653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_137 : Bounds (30332407 / 200000000) (37915509 / 250000000) (Real.log (72735428653 / 62500000000)) := by
  have h := reflection_log_137_neg
  have he : Real.log (72735428653 / 62500000000) = -Real.log (62500000000 / 72735428653) := by
    rw [show ((72735428653 / 62500000000) : ℝ) = ((62500000000 / 72735428653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_138_neg : (152068369 / 1000000000) ≤ -Real.log (500000000000 / 582119916201) ∧
    -Real.log (500000000000 / 582119916201) ≤ (15206837 / 100000000) := by
  have h := checkLog_sound (w := (82119916201 / 1082119916201)) (n := 12)
    (lo := (152068369 / 1000000000)) (hi := (15206837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582119916201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582119916201 / 500000000000) = 1/(500000000000 / 582119916201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_138 : Bounds (152068369 / 1000000000) (15206837 / 100000000) (Real.log (582119916201 / 500000000000)) := by
  have h := reflection_log_138_neg
  have he : Real.log (582119916201 / 500000000000) = -Real.log (500000000000 / 582119916201) := by
    rw [show ((582119916201 / 500000000000) : ℝ) = ((500000000000 / 582119916201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_139_neg : (152061279 / 500000000) ≤ -Real.log (500000000000 / 677717583323) ∧
    -Real.log (500000000000 / 677717583323) ≤ (304122559 / 1000000000) := by
  have h := checkLog_sound (w := (177717583323 / 1177717583323)) (n := 12)
    (lo := (152061279 / 500000000)) (hi := (304122559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677717583323 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677717583323 / 500000000000) = 1/(500000000000 / 677717583323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_139 : Bounds (152061279 / 500000000) (304122559 / 1000000000) (Real.log (677717583323 / 500000000000)) := by
  have h := reflection_log_139_neg
  have he : Real.log (677717583323 / 500000000000) = -Real.log (500000000000 / 677717583323) := by
    rw [show ((677717583323 / 500000000000) : ℝ) = ((500000000000 / 677717583323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_140_neg : (152163611 / 500000000) ≤ -Real.log (125000000000 / 169464075383) ∧
    -Real.log (125000000000 / 169464075383) ≤ (304327223 / 1000000000) := by
  have h := checkLog_sound (w := (44464075383 / 294464075383)) (n := 12)
    (lo := (152163611 / 500000000)) (hi := (304327223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169464075383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169464075383 / 125000000000) = 1/(125000000000 / 169464075383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_140 : Bounds (152163611 / 500000000) (304327223 / 1000000000) (Real.log (169464075383 / 125000000000)) := by
  have h := reflection_log_140_neg
  have he : Real.log (169464075383 / 125000000000) = -Real.log (125000000000 / 169464075383) := by
    rw [show ((169464075383 / 125000000000) : ℝ) = ((125000000000 / 169464075383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_141_neg : (70359003 / 500000000) ≤ -Real.log (10000 / 11511) ∧
    -Real.log (10000 / 11511) ≤ (140718007 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 21511)) (n := 12)
    (lo := (70359003 / 500000000)) (hi := (140718007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11511 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11511 / 10000) = 1/(10000 / 11511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_141 : Bounds (70359003 / 500000000) (140718007 / 1000000000) (Real.log (11511 / 10000)) := by
  have h := reflection_log_141_neg
  have he : Real.log (11511 / 10000) = -Real.log (10000 / 11511) := by
    rw [show ((11511 / 10000) : ℝ) = ((10000 / 11511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_142_neg : (32762777 / 200000000) ≤ -Real.log (8489 / 10000) ∧
    -Real.log (8489 / 10000) ≤ (81906943 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 18489)) (n := 12)
    (lo := (32762777 / 200000000)) (hi := (81906943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8489) = 1/(8489 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_142 : Bounds (-81906943 / 500000000) (-32762777 / 200000000) (Real.log (8489 / 10000)) := by
  have h := reflection_log_142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_143_neg : (9443 / 62500000) ≤ -Real.log (10000000 / 10001511) ∧
    -Real.log (10000000 / 10001511) ≤ (151089 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 20001511)) (n := 12)
    (lo := (9443 / 62500000)) (hi := (151089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001511 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001511 / 10000000) = 1/(10000000 / 10001511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_143 : Bounds (9443 / 62500000) (151089 / 1000000000) (Real.log (10001511 / 10000000)) := by
  have h := reflection_log_143_neg
  have he : Real.log (10001511 / 10000000) = -Real.log (10000000 / 10001511) := by
    rw [show ((10001511 / 10000000) : ℝ) = ((10000000 / 10001511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_144_neg : (151111 / 1000000000) ≤ -Real.log (9998489 / 10000000) ∧
    -Real.log (9998489 / 10000000) ≤ (18889 / 125000000) := by
  have h := checkLog_sound (w := (1511 / 19998489)) (n := 12)
    (lo := (151111 / 1000000000)) (hi := (18889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998489) = 1/(9998489 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_144 : Bounds (-18889 / 125000000) (-151111 / 1000000000) (Real.log (9998489 / 10000000)) := by
  have h := reflection_log_144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_145_neg : (9125751 / 125000000) ≤ -Real.log (1000000 / 1075737) ∧
    -Real.log (1000000 / 1075737) ≤ (73006009 / 1000000000) := by
  have h := checkLog_sound (w := (75737 / 2075737)) (n := 12)
    (lo := (9125751 / 125000000)) (hi := (73006009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075737 / 1000000) = 1/(1000000 / 1075737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_145 : Bounds (9125751 / 125000000) (73006009 / 1000000000) (Real.log (1075737 / 1000000)) := by
  have h := reflection_log_145_neg
  have he : Real.log (1075737 / 1000000) = -Real.log (1000000 / 1075737) := by
    rw [show ((1075737 / 1000000) : ℝ) = ((1000000 / 1075737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_146_neg : (15751723 / 200000000) ≤ -Real.log (924263 / 1000000) ∧
    -Real.log (924263 / 1000000) ≤ (9844827 / 125000000) := by
  have h := checkLog_sound (w := (75737 / 1924263)) (n := 12)
    (lo := (15751723 / 200000000)) (hi := (9844827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924263) = 1/(924263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_146 : Bounds (-9844827 / 125000000) (-15751723 / 200000000) (Real.log (924263 / 1000000)) := by
  have h := reflection_log_146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_147_neg : (9149221 / 125000000) ≤ -Real.log (1000000 / 1075939) ∧
    -Real.log (1000000 / 1075939) ≤ (73193769 / 1000000000) := by
  have h := checkLog_sound (w := (75939 / 2075939)) (n := 12)
    (lo := (9149221 / 125000000)) (hi := (73193769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075939 / 1000000) = 1/(1000000 / 1075939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_147 : Bounds (9149221 / 125000000) (73193769 / 1000000000) (Real.log (1075939 / 1000000)) := by
  have h := reflection_log_147_neg
  have he : Real.log (1075939 / 1000000) = -Real.log (1000000 / 1075939) := by
    rw [show ((1075939 / 1000000) : ℝ) = ((1000000 / 1075939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_148_neg : (9872149 / 125000000) ≤ -Real.log (924061 / 1000000) ∧
    -Real.log (924061 / 1000000) ≤ (78977193 / 1000000000) := by
  have h := checkLog_sound (w := (75939 / 1924061)) (n := 12)
    (lo := (9872149 / 125000000)) (hi := (78977193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924061) = 1/(924061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_148 : Bounds (-78977193 / 1000000000) (-9872149 / 125000000) (Real.log (924061 / 1000000)) := by
  have h := reflection_log_148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_149_neg : (5783423 / 1000000000) ≤ -Real.log (994233268279 / 1000000000000) ∧
    -Real.log (994233268279 / 1000000000000) ≤ (45183 / 7812500) := by
  have h := checkLog_sound (w := (5766731721 / 1994233268279)) (n := 12)
    (lo := (5783423 / 1000000000)) (hi := (45183 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994233268279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994233268279) = 1/(994233268279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_149 : Bounds (-45183 / 7812500) (-5783423 / 1000000000) (Real.log (994233268279 / 1000000000000)) := by
  have h := reflection_log_149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_150_neg : (5752607 / 1000000000) ≤ -Real.log (994263906831 / 1000000000000) ∧
    -Real.log (994263906831 / 1000000000000) ≤ (179769 / 31250000) := by
  have h := checkLog_sound (w := (5736093169 / 1994263906831)) (n := 12)
    (lo := (5752607 / 1000000000)) (hi := (179769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994263906831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994263906831) = 1/(994263906831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_150 : Bounds (-179769 / 31250000) (-5752607 / 1000000000) (Real.log (994263906831 / 1000000000000)) := by
  have h := reflection_log_150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_151_neg : (151764623 / 1000000000) ≤ -Real.log (500000000000 / 581943126577) ∧
    -Real.log (500000000000 / 581943126577) ≤ (9485289 / 62500000) := by
  have h := checkLog_sound (w := (81943126577 / 1081943126577)) (n := 12)
    (lo := (151764623 / 1000000000)) (hi := (9485289 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581943126577 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581943126577 / 500000000000) = 1/(500000000000 / 581943126577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_151 : Bounds (151764623 / 1000000000) (9485289 / 62500000) (Real.log (581943126577 / 500000000000)) := by
  have h := reflection_log_151_neg
  have he : Real.log (581943126577 / 500000000000) = -Real.log (500000000000 / 581943126577) := by
    rw [show ((581943126577 / 500000000000) : ℝ) = ((500000000000 / 581943126577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_152_neg : (1902137 / 12500000) ≤ -Real.log (62500000000 / 72772454957) ∧
    -Real.log (62500000000 / 72772454957) ≤ (152170961 / 1000000000) := by
  have h := checkLog_sound (w := (10272454957 / 135272454957)) (n := 12)
    (lo := (1902137 / 12500000)) (hi := (152170961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72772454957 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72772454957 / 62500000000) = 1/(62500000000 / 72772454957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_152 : Bounds (1902137 / 12500000) (152170961 / 1000000000) (Real.log (72772454957 / 62500000000)) := by
  have h := reflection_log_152_neg
  have he : Real.log (72772454957 / 62500000000) = -Real.log (62500000000 / 72772454957) := by
    rw [show ((72772454957 / 62500000000) : ℝ) = ((62500000000 / 72772454957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_153_neg : (152163611 / 500000000) ≤ -Real.log (500000000000 / 677856301531) ∧
    -Real.log (500000000000 / 677856301531) ≤ (304327223 / 1000000000) := by
  have h := checkLog_sound (w := (177856301531 / 1177856301531)) (n := 12)
    (lo := (152163611 / 500000000)) (hi := (304327223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677856301531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677856301531 / 500000000000) = 1/(500000000000 / 677856301531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_153 : Bounds (152163611 / 500000000) (304327223 / 1000000000) (Real.log (677856301531 / 500000000000)) := by
  have h := reflection_log_153_neg
  have he : Real.log (677856301531 / 500000000000) = -Real.log (500000000000 / 677856301531) := by
    rw [show ((677856301531 / 500000000000) : ℝ) = ((500000000000 / 677856301531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_154_neg : (76132973 / 250000000) ≤ -Real.log (500000000000 / 677995052421) ∧
    -Real.log (500000000000 / 677995052421) ≤ (304531893 / 1000000000) := by
  have h := checkLog_sound (w := (177995052421 / 1177995052421)) (n := 12)
    (lo := (76132973 / 250000000)) (hi := (304531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677995052421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677995052421 / 500000000000) = 1/(500000000000 / 677995052421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_154 : Bounds (76132973 / 250000000) (304531893 / 1000000000) (Real.log (677995052421 / 500000000000)) := by
  have h := reflection_log_154_neg
  have he : Real.log (677995052421 / 500000000000) = -Real.log (500000000000 / 677995052421) := by
    rw [show ((677995052421 / 500000000000) : ℝ) = ((500000000000 / 677995052421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_155_neg : (35201219 / 250000000) ≤ -Real.log (1250 / 1439) ∧
    -Real.log (1250 / 1439) ≤ (140804877 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 2689)) (n := 12)
    (lo := (35201219 / 250000000)) (hi := (140804877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1250) = 1/(1250 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_155 : Bounds (35201219 / 250000000) (140804877 / 1000000000) (Real.log (1439 / 1250)) := by
  have h := reflection_log_155_neg
  have he : Real.log (1439 / 1250) = -Real.log (1250 / 1439) := by
    rw [show ((1439 / 1250) : ℝ) = ((1250 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_156_neg : (163931691 / 1000000000) ≤ -Real.log (1061 / 1250) ∧
    -Real.log (1061 / 1250) ≤ (40982923 / 250000000) := by
  have h := checkLog_sound (w := (189 / 2311)) (n := 12)
    (lo := (163931691 / 1000000000)) (hi := (40982923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1061) = 1/(1061 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_156 : Bounds (-40982923 / 250000000) (-163931691 / 1000000000) (Real.log (1061 / 1250)) := by
  have h := reflection_log_156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_157_neg : (37797 / 250000000) ≤ -Real.log (1250000 / 1250189) ∧
    -Real.log (1250000 / 1250189) ≤ (151189 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 2500189)) (n := 12)
    (lo := (37797 / 250000000)) (hi := (151189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250189 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250189 / 1250000) = 1/(1250000 / 1250189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_157 : Bounds (37797 / 250000000) (151189 / 1000000000) (Real.log (1250189 / 1250000)) := by
  have h := reflection_log_157_neg
  have he : Real.log (1250189 / 1250000) = -Real.log (1250000 / 1250189) := by
    rw [show ((1250189 / 1250000) : ℝ) = ((1250000 / 1250189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_158_neg : (151211 / 1000000000) ≤ -Real.log (1249811 / 1250000) ∧
    -Real.log (1249811 / 1250000) ≤ (37803 / 250000000) := by
  have h := checkLog_sound (w := (189 / 2499811)) (n := 12)
    (lo := (151211 / 1000000000)) (hi := (37803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249811) = 1/(1249811 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_158 : Bounds (-37803 / 250000000) (-151211 / 1000000000) (Real.log (1249811 / 1250000)) := by
  have h := reflection_log_158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_159_neg : (4577573 / 62500000) ≤ -Real.log (100000 / 107599) ∧
    -Real.log (100000 / 107599) ≤ (73241169 / 1000000000) := by
  have h := checkLog_sound (w := (7599 / 207599)) (n := 12)
    (lo := (4577573 / 62500000)) (hi := (73241169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107599 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107599 / 100000) = 1/(100000 / 107599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_159 : Bounds (4577573 / 62500000) (73241169 / 1000000000) (Real.log (107599 / 100000)) := by
  have h := reflection_log_159_neg
  have he : Real.log (107599 / 100000) = -Real.log (100000 / 107599) := by
    rw [show ((107599 / 100000) : ℝ) = ((100000 / 107599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_160_neg : (1234881 / 15625000) ≤ -Real.log (92401 / 100000) ∧
    -Real.log (92401 / 100000) ≤ (15806477 / 200000000) := by
  have h := checkLog_sound (w := (7599 / 192401)) (n := 12)
    (lo := (1234881 / 15625000)) (hi := (15806477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92401) = 1/(92401 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_160 : Bounds (-15806477 / 200000000) (-1234881 / 15625000) (Real.log (92401 / 100000)) := by
  have h := reflection_log_160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_161_neg : (361951 / 62500000) ≤ -Real.log (9942255199 / 10000000000) ∧
    -Real.log (9942255199 / 10000000000) ≤ (5791217 / 1000000000) := by
  have h := checkLog_sound (w := (57744801 / 19942255199)) (n := 12)
    (lo := (361951 / 62500000)) (hi := (5791217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9942255199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9942255199) = 1/(9942255199 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_161 : Bounds (-5791217 / 1000000000) (-361951 / 62500000) (Real.log (9942255199 / 10000000000)) := by
  have h := reflection_log_161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_162_neg : (151865201 / 1000000000) ≤ -Real.log (50000000000 / 58200165979) ∧
    -Real.log (50000000000 / 58200165979) ≤ (75932601 / 500000000) := by
  have h := checkLog_sound (w := (8200165979 / 108200165979)) (n := 12)
    (lo := (151865201 / 1000000000)) (hi := (75932601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58200165979 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58200165979 / 50000000000) = 1/(50000000000 / 58200165979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_162 : Bounds (151865201 / 1000000000) (75932601 / 500000000) (Real.log (58200165979 / 50000000000)) := by
  have h := reflection_log_162_neg
  have he : Real.log (58200165979 / 50000000000) = -Real.log (50000000000 / 58200165979) := by
    rw [show ((58200165979 / 50000000000) : ℝ) = ((50000000000 / 58200165979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_163_neg : (9517097 / 62500000) ≤ -Real.log (62500000000 / 72779921213) ∧
    -Real.log (62500000000 / 72779921213) ≤ (152273553 / 1000000000) := by
  have h := checkLog_sound (w := (10279921213 / 135279921213)) (n := 12)
    (lo := (9517097 / 62500000)) (hi := (152273553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72779921213 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72779921213 / 62500000000) = 1/(62500000000 / 72779921213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_163 : Bounds (9517097 / 62500000) (152273553 / 1000000000) (Real.log (72779921213 / 62500000000)) := by
  have h := reflection_log_163_neg
  have he : Real.log (72779921213 / 62500000000) = -Real.log (62500000000 / 72779921213) := by
    rw [show ((72779921213 / 62500000000) : ℝ) = ((62500000000 / 72779921213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_164_neg : (76132973 / 250000000) ≤ -Real.log (25000000000 / 33899752621) ∧
    -Real.log (25000000000 / 33899752621) ≤ (304531893 / 1000000000) := by
  have h := checkLog_sound (w := (8899752621 / 58899752621)) (n := 12)
    (lo := (76132973 / 250000000)) (hi := (304531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33899752621 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33899752621 / 25000000000) = 1/(25000000000 / 33899752621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_164 : Bounds (76132973 / 250000000) (304531893 / 1000000000) (Real.log (33899752621 / 25000000000)) := by
  have h := reflection_log_164_neg
  have he : Real.log (33899752621 / 25000000000) = -Real.log (25000000000 / 33899752621) := by
    rw [show ((33899752621 / 25000000000) : ℝ) = ((25000000000 / 33899752621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_165_neg : (38092071 / 125000000) ≤ -Real.log (125000000000 / 169533459001) ∧
    -Real.log (125000000000 / 169533459001) ≤ (304736569 / 1000000000) := by
  have h := checkLog_sound (w := (44533459001 / 294533459001)) (n := 12)
    (lo := (38092071 / 125000000)) (hi := (304736569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169533459001 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169533459001 / 125000000000) = 1/(125000000000 / 169533459001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_165 : Bounds (38092071 / 125000000) (304736569 / 1000000000) (Real.log (169533459001 / 125000000000)) := by
  have h := reflection_log_165_neg
  have he : Real.log (169533459001 / 125000000000) = -Real.log (125000000000 / 169533459001) := by
    rw [show ((169533459001 / 125000000000) : ℝ) = ((125000000000 / 169533459001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_166_neg : (70445869 / 500000000) ≤ -Real.log (10000 / 11513) ∧
    -Real.log (10000 / 11513) ≤ (140891739 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 21513)) (n := 12)
    (lo := (70445869 / 500000000)) (hi := (140891739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11513 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11513 / 10000) = 1/(10000 / 11513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_166 : Bounds (70445869 / 500000000) (140891739 / 1000000000) (Real.log (11513 / 10000)) := by
  have h := reflection_log_166_neg
  have he : Real.log (11513 / 10000) = -Real.log (10000 / 11513) := by
    rw [show ((11513 / 10000) : ℝ) = ((10000 / 11513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_167_neg : (20506189 / 125000000) ≤ -Real.log (8487 / 10000) ∧
    -Real.log (8487 / 10000) ≤ (164049513 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 18487)) (n := 12)
    (lo := (20506189 / 125000000)) (hi := (164049513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8487) = 1/(8487 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_167 : Bounds (-164049513 / 1000000000) (-20506189 / 125000000) (Real.log (8487 / 10000)) := by
  have h := reflection_log_167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_168_neg : (18911 / 125000000) ≤ -Real.log (10000000 / 10001513) ∧
    -Real.log (10000000 / 10001513) ≤ (151289 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 20001513)) (n := 12)
    (lo := (18911 / 125000000)) (hi := (151289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001513 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001513 / 10000000) = 1/(10000000 / 10001513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_168 : Bounds (18911 / 125000000) (151289 / 1000000000) (Real.log (10001513 / 10000000)) := by
  have h := reflection_log_168_neg
  have he : Real.log (10001513 / 10000000) = -Real.log (10000000 / 10001513) := by
    rw [show ((10001513 / 10000000) : ℝ) = ((10000000 / 10001513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_169_neg : (151311 / 1000000000) ≤ -Real.log (9998487 / 10000000) ∧
    -Real.log (9998487 / 10000000) ≤ (9457 / 62500000) := by
  have h := checkLog_sound (w := (1513 / 19998487)) (n := 12)
    (lo := (151311 / 1000000000)) (hi := (9457 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998487) = 1/(9998487 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_169 : Bounds (-9457 / 62500000) (-151311 / 1000000000) (Real.log (9998487 / 10000000)) := by
  have h := reflection_log_169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_170_neg : (14657527 / 200000000) ≤ -Real.log (25000 / 26901) ∧
    -Real.log (25000 / 26901) ≤ (18321909 / 250000000) := by
  have h := checkLog_sound (w := (1901 / 51901)) (n := 12)
    (lo := (14657527 / 200000000)) (hi := (18321909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26901 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26901 / 25000) = 1/(25000 / 26901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_170 : Bounds (14657527 / 200000000) (18321909 / 250000000) (Real.log (26901 / 25000)) := by
  have h := reflection_log_170_neg
  have he : Real.log (26901 / 25000) = -Real.log (25000 / 26901) := by
    rw [show ((26901 / 25000) : ℝ) = ((25000 / 26901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_171_neg : (39543249 / 500000000) ≤ -Real.log (23099 / 25000) ∧
    -Real.log (23099 / 25000) ≤ (79086499 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 48099)) (n := 12)
    (lo := (39543249 / 500000000)) (hi := (79086499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23099) = 1/(23099 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_171 : Bounds (-79086499 / 1000000000) (-39543249 / 500000000) (Real.log (23099 / 25000)) := by
  have h := reflection_log_171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_172_neg : (2899431 / 500000000) ≤ -Real.log (621386199 / 625000000) ∧
    -Real.log (621386199 / 625000000) ≤ (5798863 / 1000000000) := by
  have h := checkLog_sound (w := (3613801 / 1246386199)) (n := 12)
    (lo := (2899431 / 500000000)) (hi := (5798863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621386199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621386199) = 1/(621386199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_172 : Bounds (-5798863 / 1000000000) (-2899431 / 500000000) (Real.log (621386199 / 625000000)) := by
  have h := reflection_log_172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_173_neg : (15196779 / 100000000) ≤ -Real.log (31250000000 / 36378835637) ∧
    -Real.log (31250000000 / 36378835637) ≤ (151967791 / 1000000000) := by
  have h := checkLog_sound (w := (5128835637 / 67628835637)) (n := 12)
    (lo := (15196779 / 100000000)) (hi := (151967791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36378835637 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36378835637 / 31250000000) = 1/(31250000000 / 36378835637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_173 : Bounds (15196779 / 100000000) (151967791 / 1000000000) (Real.log (36378835637 / 31250000000)) := by
  have h := reflection_log_173_neg
  have he : Real.log (36378835637 / 31250000000) = -Real.log (31250000000 / 36378835637) := by
    rw [show ((36378835637 / 31250000000) : ℝ) = ((31250000000 / 36378835637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_174_neg : (76187067 / 500000000) ≤ -Real.log (3906250000 / 4549202617) ∧
    -Real.log (3906250000 / 4549202617) ≤ (30474827 / 200000000) := by
  have h := checkLog_sound (w := (642952617 / 8455452617)) (n := 12)
    (lo := (76187067 / 500000000)) (hi := (30474827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4549202617 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4549202617 / 3906250000) = 1/(3906250000 / 4549202617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_174 : Bounds (76187067 / 500000000) (30474827 / 200000000) (Real.log (4549202617 / 3906250000)) := by
  have h := reflection_log_174_neg
  have he : Real.log (4549202617 / 3906250000) = -Real.log (3906250000 / 4549202617) := by
    rw [show ((4549202617 / 3906250000) : ℝ) = ((3906250000 / 4549202617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_175_neg : (38092071 / 125000000) ≤ -Real.log (500000000000 / 678133836003) ∧
    -Real.log (500000000000 / 678133836003) ≤ (304736569 / 1000000000) := by
  have h := checkLog_sound (w := (178133836003 / 1178133836003)) (n := 12)
    (lo := (38092071 / 125000000)) (hi := (304736569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678133836003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678133836003 / 500000000000) = 1/(500000000000 / 678133836003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_175 : Bounds (38092071 / 125000000) (304736569 / 1000000000) (Real.log (678133836003 / 500000000000)) := by
  have h := reflection_log_175_neg
  have he : Real.log (678133836003 / 500000000000) = -Real.log (500000000000 / 678133836003) := by
    rw [show ((678133836003 / 500000000000) : ℝ) = ((500000000000 / 678133836003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_176_neg : (243953 / 800000) ≤ -Real.log (125000000000 / 169568163073) ∧
    -Real.log (125000000000 / 169568163073) ≤ (304941251 / 1000000000) := by
  have h := checkLog_sound (w := (44568163073 / 294568163073)) (n := 12)
    (lo := (243953 / 800000)) (hi := (304941251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169568163073 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169568163073 / 125000000000) = 1/(125000000000 / 169568163073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_176 : Bounds (243953 / 800000) (304941251 / 1000000000) (Real.log (169568163073 / 125000000000)) := by
  have h := reflection_log_176_neg
  have he : Real.log (169568163073 / 125000000000) = -Real.log (125000000000 / 169568163073) := by
    rw [show ((169568163073 / 125000000000) : ℝ) = ((125000000000 / 169568163073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_177_neg : (140978593 / 1000000000) ≤ -Real.log (5000 / 5757) ∧
    -Real.log (5000 / 5757) ≤ (70489297 / 500000000) := by
  have h := checkLog_sound (w := (757 / 10757)) (n := 12)
    (lo := (140978593 / 1000000000)) (hi := (70489297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5757 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5757 / 5000) = 1/(5000 / 5757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_177 : Bounds (140978593 / 1000000000) (70489297 / 500000000) (Real.log (5757 / 5000)) := by
  have h := reflection_log_177_neg
  have he : Real.log (5757 / 5000) = -Real.log (5000 / 5757) := by
    rw [show ((5757 / 5000) : ℝ) = ((5000 / 5757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_178_neg : (82083673 / 500000000) ≤ -Real.log (4243 / 5000) ∧
    -Real.log (4243 / 5000) ≤ (164167347 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 9243)) (n := 12)
    (lo := (82083673 / 500000000)) (hi := (164167347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4243) = 1/(4243 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_178 : Bounds (-164167347 / 1000000000) (-82083673 / 500000000) (Real.log (4243 / 5000)) := by
  have h := reflection_log_178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_179_neg : (37847 / 250000000) ≤ -Real.log (5000000 / 5000757) ∧
    -Real.log (5000000 / 5000757) ≤ (151389 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 10000757)) (n := 12)
    (lo := (37847 / 250000000)) (hi := (151389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000757 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000757 / 5000000) = 1/(5000000 / 5000757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_179 : Bounds (37847 / 250000000) (151389 / 1000000000) (Real.log (5000757 / 5000000)) := by
  have h := reflection_log_179_neg
  have he : Real.log (5000757 / 5000000) = -Real.log (5000000 / 5000757) := by
    rw [show ((5000757 / 5000000) : ℝ) = ((5000000 / 5000757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_180_neg : (151411 / 1000000000) ≤ -Real.log (4999243 / 5000000) ∧
    -Real.log (4999243 / 5000000) ≤ (37853 / 250000000) := by
  have h := checkLog_sound (w := (757 / 9999243)) (n := 12)
    (lo := (151411 / 1000000000)) (hi := (37853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999243) = 1/(4999243 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_180 : Bounds (-37853 / 250000000) (-151411 / 1000000000) (Real.log (4999243 / 5000000)) := by
  have h := reflection_log_180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_181_neg : (2285853 / 31250000) ≤ -Real.log (1000000 / 1075889) ∧
    -Real.log (1000000 / 1075889) ≤ (73147297 / 1000000000) := by
  have h := checkLog_sound (w := (75889 / 2075889)) (n := 12)
    (lo := (2285853 / 31250000)) (hi := (73147297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075889 / 1000000) = 1/(1000000 / 1075889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_181 : Bounds (2285853 / 31250000) (73147297 / 1000000000) (Real.log (1075889 / 1000000)) := by
  have h := reflection_log_181_neg
  have he : Real.log (1075889 / 1000000) = -Real.log (1000000 / 1075889) := by
    rw [show ((1075889 / 1000000) : ℝ) = ((1000000 / 1075889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_182_neg : (19730771 / 250000000) ≤ -Real.log (924111 / 1000000) ∧
    -Real.log (924111 / 1000000) ≤ (15784617 / 200000000) := by
  have h := checkLog_sound (w := (75889 / 1924111)) (n := 12)
    (lo := (19730771 / 250000000)) (hi := (15784617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924111) = 1/(924111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_182 : Bounds (-15784617 / 200000000) (-19730771 / 250000000) (Real.log (924111 / 1000000)) := by
  have h := reflection_log_182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_183_neg : (7333503 / 100000000) ≤ -Real.log (1000000 / 1076091) ∧
    -Real.log (1000000 / 1076091) ≤ (73335031 / 1000000000) := by
  have h := checkLog_sound (w := (76091 / 2076091)) (n := 12)
    (lo := (7333503 / 100000000)) (hi := (73335031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076091 / 1000000) = 1/(1000000 / 1076091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_183 : Bounds (7333503 / 100000000) (73335031 / 1000000000) (Real.log (1076091 / 1000000)) := by
  have h := reflection_log_183_neg
  have he : Real.log (1076091 / 1000000) = -Real.log (1000000 / 1076091) := by
    rw [show ((1076091 / 1000000) : ℝ) = ((1000000 / 1076091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_184_neg : (79141697 / 1000000000) ≤ -Real.log (923909 / 1000000) ∧
    -Real.log (923909 / 1000000) ≤ (39570849 / 500000000) := by
  have h := checkLog_sound (w := (76091 / 1923909)) (n := 12)
    (lo := (79141697 / 1000000000)) (hi := (39570849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923909) = 1/(923909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_184 : Bounds (-39570849 / 500000000) (-79141697 / 1000000000) (Real.log (923909 / 1000000)) := by
  have h := reflection_log_184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_185_neg : (2903333 / 500000000) ≤ -Real.log (994210159719 / 1000000000000) ∧
    -Real.log (994210159719 / 1000000000000) ≤ (5806667 / 1000000000) := by
  have h := checkLog_sound (w := (5789840281 / 1994210159719)) (n := 12)
    (lo := (2903333 / 500000000)) (hi := (5806667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994210159719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994210159719) = 1/(994210159719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_185 : Bounds (-5806667 / 1000000000) (-2903333 / 500000000) (Real.log (994210159719 / 1000000000000)) := by
  have h := reflection_log_185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_186_neg : (1443947 / 250000000) ≤ -Real.log (994240859679 / 1000000000000) ∧
    -Real.log (994240859679 / 1000000000000) ≤ (5775789 / 1000000000) := by
  have h := checkLog_sound (w := (5759140321 / 1994240859679)) (n := 12)
    (lo := (1443947 / 250000000)) (hi := (5775789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994240859679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994240859679) = 1/(994240859679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_186 : Bounds (-5775789 / 1000000000) (-1443947 / 250000000) (Real.log (994240859679 / 1000000000000)) := by
  have h := reflection_log_186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_187_neg : (152070381 / 1000000000) ≤ -Real.log (100000000000 / 116424217437) ∧
    -Real.log (100000000000 / 116424217437) ≤ (76035191 / 500000000) := by
  have h := checkLog_sound (w := (16424217437 / 216424217437)) (n := 12)
    (lo := (152070381 / 1000000000)) (hi := (76035191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116424217437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116424217437 / 100000000000) = 1/(100000000000 / 116424217437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_187 : Bounds (152070381 / 1000000000) (76035191 / 500000000) (Real.log (116424217437 / 100000000000)) := by
  have h := reflection_log_187_neg
  have he : Real.log (116424217437 / 100000000000) = -Real.log (100000000000 / 116424217437) := by
    rw [show ((116424217437 / 100000000000) : ℝ) = ((100000000000 / 116424217437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_188_neg : (152476727 / 1000000000) ≤ -Real.log (125000000000 / 145589419521) ∧
    -Real.log (125000000000 / 145589419521) ≤ (19059591 / 125000000) := by
  have h := checkLog_sound (w := (20589419521 / 270589419521)) (n := 12)
    (lo := (152476727 / 1000000000)) (hi := (19059591 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145589419521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145589419521 / 125000000000) = 1/(125000000000 / 145589419521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_188 : Bounds (152476727 / 1000000000) (19059591 / 125000000) (Real.log (145589419521 / 125000000000)) := by
  have h := reflection_log_188_neg
  have he : Real.log (145589419521 / 125000000000) = -Real.log (125000000000 / 145589419521) := by
    rw [show ((145589419521 / 125000000000) : ℝ) = ((125000000000 / 145589419521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_189_neg : (243953 / 800000) ≤ -Real.log (500000000000 / 678272652291) ∧
    -Real.log (500000000000 / 678272652291) ≤ (304941251 / 1000000000) := by
  have h := checkLog_sound (w := (178272652291 / 1178272652291)) (n := 12)
    (lo := (243953 / 800000)) (hi := (304941251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678272652291 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678272652291 / 500000000000) = 1/(500000000000 / 678272652291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_189 : Bounds (243953 / 800000) (304941251 / 1000000000) (Real.log (678272652291 / 500000000000)) := by
  have h := reflection_log_189_neg
  have he : Real.log (678272652291 / 500000000000) = -Real.log (500000000000 / 678272652291) := by
    rw [show ((678272652291 / 500000000000) : ℝ) = ((500000000000 / 678272652291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_190_neg : (305145939 / 1000000000) ≤ -Real.log (500000000000 / 678411501297) ∧
    -Real.log (500000000000 / 678411501297) ≤ (15257297 / 50000000) := by
  have h := checkLog_sound (w := (178411501297 / 1178411501297)) (n := 12)
    (lo := (305145939 / 1000000000)) (hi := (15257297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678411501297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678411501297 / 500000000000) = 1/(500000000000 / 678411501297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_190 : Bounds (305145939 / 1000000000) (15257297 / 50000000) (Real.log (678411501297 / 500000000000)) := by
  have h := reflection_log_190_neg
  have he : Real.log (678411501297 / 500000000000) = -Real.log (500000000000 / 678411501297) := by
    rw [show ((678411501297 / 500000000000) : ℝ) = ((500000000000 / 678411501297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_191_neg : (881659 / 6250000) ≤ -Real.log (2000 / 2303) ∧
    -Real.log (2000 / 2303) ≤ (141065441 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 4303)) (n := 12)
    (lo := (881659 / 6250000)) (hi := (141065441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2303 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2303 / 2000) = 1/(2000 / 2303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_191 : Bounds (881659 / 6250000) (141065441 / 1000000000) (Real.log (2303 / 2000)) := by
  have h := reflection_log_191_neg
  have he : Real.log (2303 / 2000) = -Real.log (2000 / 2303) := by
    rw [show ((2303 / 2000) : ℝ) = ((2000 / 2303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
