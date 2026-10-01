import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11136_neg : (4283693 / 100000000) ≤ -Real.log (239516902231 / 250000000000) ∧
    -Real.log (239516902231 / 250000000000) ≤ (42836931 / 1000000000) := by
  have h := checkLog_sound (w := (10483097769 / 489516902231)) (n := 12)
    (lo := (4283693 / 100000000)) (hi := (42836931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239516902231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239516902231) = 1/(239516902231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11136 : Bounds (-42836931 / 1000000000) (-4283693 / 100000000) (Real.log (239516902231 / 250000000000)) := by
  have h := reflection_log_11136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11137_neg : (16616837 / 40000000) ≤ -Real.log (500000000000 / 757504156051) ∧
    -Real.log (500000000000 / 757504156051) ≤ (207710463 / 500000000) := by
  have h := checkLog_sound (w := (257504156051 / 1257504156051)) (n := 12)
    (lo := (16616837 / 40000000)) (hi := (207710463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757504156051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757504156051 / 500000000000) = 1/(500000000000 / 757504156051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11137 : Bounds (16616837 / 40000000) (207710463 / 500000000) (Real.log (757504156051 / 500000000000)) := by
  have h := reflection_log_11137_neg
  have he : Real.log (757504156051 / 500000000000) = -Real.log (500000000000 / 757504156051) := by
    rw [show ((757504156051 / 500000000000) : ℝ) = ((500000000000 / 757504156051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11138_neg : (417371073 / 1000000000) ≤ -Real.log (250000000000 / 379491421291) ∧
    -Real.log (250000000000 / 379491421291) ≤ (208685537 / 500000000) := by
  have h := checkLog_sound (w := (129491421291 / 629491421291)) (n := 12)
    (lo := (417371073 / 1000000000)) (hi := (208685537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379491421291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379491421291 / 250000000000) = 1/(250000000000 / 379491421291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11138 : Bounds (417371073 / 1000000000) (208685537 / 500000000) (Real.log (379491421291 / 250000000000)) := by
  have h := reflection_log_11138_neg
  have he : Real.log (379491421291 / 250000000000) = -Real.log (250000000000 / 379491421291) := by
    rw [show ((379491421291 / 250000000000) : ℝ) = ((250000000000 / 379491421291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11139_neg : (210635119 / 250000000) ≤ -Real.log (250000000000 / 580564784053) ∧
    -Real.log (250000000000 / 580564784053) ≤ (421270239 / 500000000) := by
  have h := checkLog_sound (w := (80564784053 / 1080564784053)) (n := 12)
    (lo := (9337081 / 62500000)) (hi := (149393297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580564784053 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(580564784053 / 500000000000) = 1/(250000000000 / 580564784053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11139 : Bounds (210635119 / 250000000) (421270239 / 500000000) (Real.log (580564784053 / 250000000000)) := by
  have h := reflection_log_11139_neg
  have he : Real.log (580564784053 / 250000000000) = -Real.log (250000000000 / 580564784053) := by
    rw [show ((580564784053 / 250000000000) : ℝ) = ((250000000000 / 580564784053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11140_neg : (844918039 / 1000000000) ≤ -Real.log (15625000000 / 36371672213) ∧
    -Real.log (15625000000 / 36371672213) ≤ (844918041 / 1000000000) := by
  have h := checkLog_sound (w := (5121672213 / 67621672213)) (n := 12)
    (lo := (151770859 / 1000000000)) (hi := (7588543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36371672213 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(36371672213 / 31250000000) = 1/(15625000000 / 36371672213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11140 : Bounds (844918039 / 1000000000) (844918041 / 1000000000) (Real.log (36371672213 / 15625000000)) := by
  have h := reflection_log_11140_neg
  have he : Real.log (36371672213 / 15625000000) = -Real.log (15625000000 / 36371672213) := by
    rw [show ((36371672213 / 15625000000) : ℝ) = ((15625000000 / 36371672213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11141_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11141 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_11141_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11142_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11142 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_11142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11143_neg : (4999 / 12500000) ≤ -Real.log (2500 / 2501) ∧
    -Real.log (2500 / 2501) ≤ (399921 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5001)) (n := 12)
    (lo := (4999 / 12500000)) (hi := (399921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2501 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2501 / 2500) = 1/(2500 / 2501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11143 : Bounds (4999 / 12500000) (399921 / 1000000000) (Real.log (2501 / 2500)) := by
  have h := reflection_log_11143_neg
  have he : Real.log (2501 / 2500) = -Real.log (2500 / 2501) := by
    rw [show ((2501 / 2500) : ℝ) = ((2500 / 2501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11144_neg : (5001 / 12500000) ≤ -Real.log (2499 / 2500) ∧
    -Real.log (2499 / 2500) ≤ (400081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4999)) (n := 12)
    (lo := (5001 / 12500000)) (hi := (400081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2499) = 1/(2499 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11144 : Bounds (-400081 / 1000000000) (-5001 / 12500000) (Real.log (2499 / 2500)) := by
  have h := reflection_log_11144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11145_neg : (186745091 / 1000000000) ≤ -Real.log (25000 / 30133) ∧
    -Real.log (25000 / 30133) ≤ (46686273 / 250000000) := by
  have h := checkLog_sound (w := (5133 / 55133)) (n := 12)
    (lo := (186745091 / 1000000000)) (hi := (46686273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30133 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30133 / 25000) = 1/(25000 / 30133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11145 : Bounds (186745091 / 1000000000) (46686273 / 250000000) (Real.log (30133 / 25000)) := by
  have h := reflection_log_11145_neg
  have he : Real.log (30133 / 25000) = -Real.log (25000 / 30133) := by
    rw [show ((30133 / 25000) : ℝ) = ((25000 / 30133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11146_neg : (229815761 / 1000000000) ≤ -Real.log (19867 / 25000) ∧
    -Real.log (19867 / 25000) ≤ (114907881 / 500000000) := by
  have h := checkLog_sound (w := (5133 / 44867)) (n := 12)
    (lo := (229815761 / 1000000000)) (hi := (114907881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19867) = 1/(19867 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11146 : Bounds (-114907881 / 500000000) (-229815761 / 1000000000) (Real.log (19867 / 25000)) := by
  have h := reflection_log_11146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11147_neg : (93760259 / 500000000) ≤ -Real.log (200000 / 241251) ∧
    -Real.log (200000 / 241251) ≤ (187520519 / 1000000000) := by
  have h := checkLog_sound (w := (41251 / 441251)) (n := 12)
    (lo := (93760259 / 500000000)) (hi := (187520519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241251 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241251 / 200000) = 1/(200000 / 241251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11147 : Bounds (93760259 / 500000000) (187520519 / 1000000000) (Real.log (241251 / 200000)) := by
  have h := reflection_log_11147_neg
  have he : Real.log (241251 / 200000) = -Real.log (200000 / 241251) := by
    rw [show ((241251 / 200000) : ℝ) = ((200000 / 241251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11148_neg : (57748257 / 250000000) ≤ -Real.log (158749 / 200000) ∧
    -Real.log (158749 / 200000) ≤ (230993029 / 1000000000) := by
  have h := checkLog_sound (w := (41251 / 358749)) (n := 12)
    (lo := (57748257 / 250000000)) (hi := (230993029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158749) = 1/(158749 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11148 : Bounds (-230993029 / 1000000000) (-57748257 / 250000000) (Real.log (158749 / 200000)) := by
  have h := reflection_log_11148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11149_neg : (43472509 / 1000000000) ≤ -Real.log (38298354999 / 40000000000) ∧
    -Real.log (38298354999 / 40000000000) ≤ (4347251 / 100000000) := by
  have h := checkLog_sound (w := (1701645001 / 78298354999)) (n := 12)
    (lo := (43472509 / 1000000000)) (hi := (4347251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38298354999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38298354999) = 1/(38298354999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11149 : Bounds (-4347251 / 100000000) (-43472509 / 1000000000) (Real.log (38298354999 / 40000000000)) := by
  have h := reflection_log_11149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11150_neg : (43070669 / 1000000000) ≤ -Real.log (598652311 / 625000000) ∧
    -Real.log (598652311 / 625000000) ≤ (4307067 / 100000000) := by
  have h := checkLog_sound (w := (26347689 / 1223652311)) (n := 12)
    (lo := (43070669 / 1000000000)) (hi := (4307067 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 598652311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 598652311) = 1/(598652311 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11150 : Bounds (-4307067 / 100000000) (-43070669 / 1000000000) (Real.log (598652311 / 625000000)) := by
  have h := reflection_log_11150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11151_neg : (104140213 / 250000000) ≤ -Real.log (100000000000 / 151673629637) ∧
    -Real.log (100000000000 / 151673629637) ≤ (416560853 / 1000000000) := by
  have h := checkLog_sound (w := (51673629637 / 251673629637)) (n := 12)
    (lo := (104140213 / 250000000)) (hi := (416560853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151673629637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151673629637 / 100000000000) = 1/(100000000000 / 151673629637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11151 : Bounds (104140213 / 250000000) (416560853 / 1000000000) (Real.log (151673629637 / 100000000000)) := by
  have h := reflection_log_11151_neg
  have he : Real.log (151673629637 / 100000000000) = -Real.log (100000000000 / 151673629637) := by
    rw [show ((151673629637 / 100000000000) : ℝ) = ((100000000000 / 151673629637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11152_neg : (209256773 / 500000000) ≤ -Real.log (500000000000 / 759850455751) ∧
    -Real.log (500000000000 / 759850455751) ≤ (418513547 / 1000000000) := by
  have h := checkLog_sound (w := (259850455751 / 1259850455751)) (n := 12)
    (lo := (209256773 / 500000000)) (hi := (418513547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759850455751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759850455751 / 500000000000) = 1/(500000000000 / 759850455751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11152 : Bounds (209256773 / 500000000) (418513547 / 1000000000) (Real.log (759850455751 / 500000000000)) := by
  have h := reflection_log_11152_neg
  have he : Real.log (759850455751 / 500000000000) = -Real.log (500000000000 / 759850455751) := by
    rw [show ((759850455751 / 500000000000) : ℝ) = ((500000000000 / 759850455751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11153_neg : (844918039 / 1000000000) ≤ -Real.log (100000000000 / 232778702163) ∧
    -Real.log (100000000000 / 232778702163) ≤ (844918041 / 1000000000) := by
  have h := checkLog_sound (w := (32778702163 / 432778702163)) (n := 12)
    (lo := (151770859 / 1000000000)) (hi := (7588543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232778702163 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232778702163 / 200000000000) = 1/(100000000000 / 232778702163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11153 : Bounds (844918039 / 1000000000) (844918041 / 1000000000) (Real.log (232778702163 / 100000000000)) := by
  have h := reflection_log_11153_neg
  have he : Real.log (232778702163 / 100000000000) = -Real.log (100000000000 / 232778702163) := by
    rw [show ((232778702163 / 100000000000) : ℝ) = ((100000000000 / 232778702163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11154_neg : (847297859 / 1000000000) ≤ -Real.log (500000000000 / 1166666666667) ∧
    -Real.log (500000000000 / 1166666666667) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (166666666667 / 2166666666667)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166666666667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166666666667 / 1000000000000) = 1/(500000000000 / 1166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11154 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (1166666666667 / 500000000000)) := by
  have h := reflection_log_11154_neg
  have he : Real.log (1166666666667 / 500000000000) = -Real.log (500000000000 / 1166666666667) := by
    rw [show ((1166666666667 / 500000000000) : ℝ) = ((500000000000 / 1166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11155_neg : (337186267 / 1000000000) ≤ -Real.log (1000 / 1401) ∧
    -Real.log (1000 / 1401) ≤ (84296567 / 250000000) := by
  have h := checkLog_sound (w := (401 / 2401)) (n := 12)
    (lo := (337186267 / 1000000000)) (hi := (84296567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1401 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1401 / 1000) = 1/(1000 / 1401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11155 : Bounds (337186267 / 1000000000) (84296567 / 250000000) (Real.log (1401 / 1000)) := by
  have h := reflection_log_11155_neg
  have he : Real.log (1401 / 1000) = -Real.log (1000 / 1401) := by
    rw [show ((1401 / 1000) : ℝ) = ((1000 / 1401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11156_neg : (6406171 / 12500000) ≤ -Real.log (599 / 1000) ∧
    -Real.log (599 / 1000) ≤ (512493681 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 1599)) (n := 12)
    (lo := (6406171 / 12500000)) (hi := (512493681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 599) = 1/(599 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11156 : Bounds (-512493681 / 1000000000) (-6406171 / 12500000) (Real.log (599 / 1000)) := by
  have h := reflection_log_11156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11157_neg : (400919 / 1000000000) ≤ -Real.log (1000000 / 1000401) ∧
    -Real.log (1000000 / 1000401) ≤ (10023 / 25000000) := by
  have h := checkLog_sound (w := (401 / 2000401)) (n := 12)
    (lo := (400919 / 1000000000)) (hi := (10023 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000401 / 1000000) = 1/(1000000 / 1000401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11157 : Bounds (400919 / 1000000000) (10023 / 25000000) (Real.log (1000401 / 1000000)) := by
  have h := reflection_log_11157_neg
  have he : Real.log (1000401 / 1000000) = -Real.log (1000000 / 1000401) := by
    rw [show ((1000401 / 1000000) : ℝ) = ((1000000 / 1000401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11158_neg : (10027 / 25000000) ≤ -Real.log (999599 / 1000000) ∧
    -Real.log (999599 / 1000000) ≤ (401081 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 1999599)) (n := 12)
    (lo := (10027 / 25000000)) (hi := (401081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999599) = 1/(999599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11158 : Bounds (-401081 / 1000000000) (-10027 / 25000000) (Real.log (999599 / 1000000)) := by
  have h := reflection_log_11158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11159_neg : (18719881 / 100000000) ≤ -Real.log (1000000 / 1205867) ∧
    -Real.log (1000000 / 1205867) ≤ (187198811 / 1000000000) := by
  have h := checkLog_sound (w := (205867 / 2205867)) (n := 12)
    (lo := (18719881 / 100000000)) (hi := (187198811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205867 / 1000000) = 1/(1000000 / 1205867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11159 : Bounds (18719881 / 100000000) (187198811 / 1000000000) (Real.log (1205867 / 1000000)) := by
  have h := reflection_log_11159_neg
  have he : Real.log (1205867 / 1000000) = -Real.log (1000000 / 1205867) := by
    rw [show ((1205867 / 1000000) : ℝ) = ((1000000 / 1205867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11160_neg : (9220173 / 40000000) ≤ -Real.log (794133 / 1000000) ∧
    -Real.log (794133 / 1000000) ≤ (115252163 / 500000000) := by
  have h := checkLog_sound (w := (205867 / 1794133)) (n := 12)
    (lo := (9220173 / 40000000)) (hi := (115252163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794133) = 1/(794133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11160 : Bounds (-115252163 / 500000000) (-9220173 / 40000000) (Real.log (794133 / 1000000)) := by
  have h := reflection_log_11160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11161_neg : (37594777 / 200000000) ≤ -Real.log (500000 / 603401) ∧
    -Real.log (500000 / 603401) ≤ (93986943 / 500000000) := by
  have h := checkLog_sound (w := (103401 / 1103401)) (n := 12)
    (lo := (37594777 / 200000000)) (hi := (93986943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603401 / 500000) = 1/(500000 / 603401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11161 : Bounds (37594777 / 200000000) (93986943 / 500000000) (Real.log (603401 / 500000)) := by
  have h := reflection_log_11161_neg
  have he : Real.log (603401 / 500000) = -Real.log (500000 / 603401) := by
    rw [show ((603401 / 500000) : ℝ) = ((500000 / 603401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11162_neg : (231682403 / 1000000000) ≤ -Real.log (396599 / 500000) ∧
    -Real.log (396599 / 500000) ≤ (57920601 / 250000000) := by
  have h := checkLog_sound (w := (103401 / 896599)) (n := 12)
    (lo := (231682403 / 1000000000)) (hi := (57920601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396599) = 1/(396599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11162 : Bounds (-57920601 / 250000000) (-231682403 / 1000000000) (Real.log (396599 / 500000)) := by
  have h := reflection_log_11162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11163_neg : (21854259 / 500000000) ≤ -Real.log (239308233199 / 250000000000) ∧
    -Real.log (239308233199 / 250000000000) ≤ (43708519 / 1000000000) := by
  have h := checkLog_sound (w := (10691766801 / 489308233199)) (n := 12)
    (lo := (21854259 / 500000000)) (hi := (43708519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239308233199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239308233199) = 1/(239308233199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11163 : Bounds (-43708519 / 1000000000) (-21854259 / 500000000) (Real.log (239308233199 / 250000000000)) := by
  have h := reflection_log_11163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11164_neg : (8661103 / 200000000) ≤ -Real.log (957618778311 / 1000000000000) ∧
    -Real.log (957618778311 / 1000000000000) ≤ (10826379 / 250000000) := by
  have h := checkLog_sound (w := (42381221689 / 1957618778311)) (n := 12)
    (lo := (8661103 / 200000000)) (hi := (10826379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957618778311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957618778311) = 1/(957618778311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11164 : Bounds (-10826379 / 250000000) (-8661103 / 200000000) (Real.log (957618778311 / 1000000000000)) := by
  have h := reflection_log_11164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11165_neg : (83540627 / 200000000) ≤ -Real.log (10000000000 / 15184698281) ∧
    -Real.log (10000000000 / 15184698281) ≤ (13053223 / 31250000) := by
  have h := checkLog_sound (w := (5184698281 / 25184698281)) (n := 12)
    (lo := (83540627 / 200000000)) (hi := (13053223 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15184698281 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15184698281 / 10000000000) = 1/(10000000000 / 15184698281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11165 : Bounds (83540627 / 200000000) (13053223 / 31250000) (Real.log (15184698281 / 10000000000)) := by
  have h := reflection_log_11165_neg
  have he : Real.log (15184698281 / 10000000000) = -Real.log (10000000000 / 15184698281) := by
    rw [show ((15184698281 / 10000000000) : ℝ) = ((10000000000 / 15184698281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11166_neg : (419656289 / 1000000000) ≤ -Real.log (125000000000 / 190179816389) ∧
    -Real.log (125000000000 / 190179816389) ≤ (41965629 / 100000000) := by
  have h := checkLog_sound (w := (65179816389 / 315179816389)) (n := 12)
    (lo := (419656289 / 1000000000)) (hi := (41965629 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190179816389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190179816389 / 125000000000) = 1/(125000000000 / 190179816389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11166 : Bounds (419656289 / 1000000000) (41965629 / 100000000) (Real.log (190179816389 / 125000000000)) := by
  have h := reflection_log_11166_neg
  have he : Real.log (190179816389 / 125000000000) = -Real.log (125000000000 / 190179816389) := by
    rw [show ((190179816389 / 125000000000) : ℝ) = ((125000000000 / 190179816389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11167_neg : (847297859 / 1000000000) ≤ -Real.log (250000000000 / 583333333333) ∧
    -Real.log (250000000000 / 583333333333) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (83333333333 / 1083333333333)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583333333333 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(583333333333 / 500000000000) = 1/(250000000000 / 583333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11167 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (583333333333 / 250000000000)) := by
  have h := reflection_log_11167_neg
  have he : Real.log (583333333333 / 250000000000) = -Real.log (250000000000 / 583333333333) := by
    rw [show ((583333333333 / 250000000000) : ℝ) = ((250000000000 / 583333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11168_neg : (849679947 / 1000000000) ≤ -Real.log (125000000000 / 292362270451) ∧
    -Real.log (125000000000 / 292362270451) ≤ (849679949 / 1000000000) := by
  have h := checkLog_sound (w := (42362270451 / 542362270451)) (n := 12)
    (lo := (156532767 / 1000000000)) (hi := (4891649 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292362270451 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292362270451 / 250000000000) = 1/(125000000000 / 292362270451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11168 : Bounds (849679947 / 1000000000) (849679949 / 1000000000) (Real.log (292362270451 / 125000000000)) := by
  have h := reflection_log_11168_neg
  have he : Real.log (292362270451 / 125000000000) = -Real.log (125000000000 / 292362270451) := by
    rw [show ((292362270451 / 125000000000) : ℝ) = ((125000000000 / 292362270451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11169_neg : (84474947 / 250000000) ≤ -Real.log (500 / 701) ∧
    -Real.log (500 / 701) ≤ (337899789 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 1201)) (n := 12)
    (lo := (84474947 / 250000000)) (hi := (337899789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701 / 500) = 1/(500 / 701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11169 : Bounds (84474947 / 250000000) (337899789 / 1000000000) (Real.log (701 / 500)) := by
  have h := reflection_log_11169_neg
  have he : Real.log (701 / 500) = -Real.log (500 / 701) := by
    rw [show ((701 / 500) : ℝ) = ((500 / 701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11170_neg : (20566581 / 40000000) ≤ -Real.log (299 / 500) ∧
    -Real.log (299 / 500) ≤ (257082263 / 500000000) := by
  have h := checkLog_sound (w := (201 / 799)) (n := 12)
    (lo := (20566581 / 40000000)) (hi := (257082263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 299) = 1/(299 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11170 : Bounds (-257082263 / 500000000) (-20566581 / 40000000) (Real.log (299 / 500)) := by
  have h := reflection_log_11170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11171_neg : (401919 / 1000000000) ≤ -Real.log (500000 / 500201) ∧
    -Real.log (500000 / 500201) ≤ (157 / 390625) := by
  have h := checkLog_sound (w := (201 / 1000201)) (n := 12)
    (lo := (401919 / 1000000000)) (hi := (157 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500201 / 500000) = 1/(500000 / 500201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11171 : Bounds (401919 / 1000000000) (157 / 390625) (Real.log (500201 / 500000)) := by
  have h := reflection_log_11171_neg
  have he : Real.log (500201 / 500000) = -Real.log (500000 / 500201) := by
    rw [show ((500201 / 500000) : ℝ) = ((500000 / 500201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11172_neg : (2513 / 6250000) ≤ -Real.log (499799 / 500000) ∧
    -Real.log (499799 / 500000) ≤ (402081 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 999799)) (n := 12)
    (lo := (2513 / 6250000)) (hi := (402081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499799) = 1/(499799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11172 : Bounds (-402081 / 1000000000) (-2513 / 6250000) (Real.log (499799 / 500000)) := by
  have h := reflection_log_11172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11173_neg : (93825747 / 500000000) ≤ -Real.log (1000000 / 1206413) ∧
    -Real.log (1000000 / 1206413) ≤ (37530299 / 200000000) := by
  have h := checkLog_sound (w := (206413 / 2206413)) (n := 12)
    (lo := (93825747 / 500000000)) (hi := (37530299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206413 / 1000000) = 1/(1000000 / 1206413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11173 : Bounds (93825747 / 500000000) (37530299 / 200000000) (Real.log (1206413 / 1000000)) := by
  have h := reflection_log_11173_neg
  have he : Real.log (1206413 / 1000000) = -Real.log (1000000 / 1206413) := by
    rw [show ((1206413 / 1000000) : ℝ) = ((1000000 / 1206413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11174_neg : (28899013 / 125000000) ≤ -Real.log (793587 / 1000000) ∧
    -Real.log (793587 / 1000000) ≤ (46238421 / 200000000) := by
  have h := checkLog_sound (w := (206413 / 1793587)) (n := 12)
    (lo := (28899013 / 125000000)) (hi := (46238421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793587) = 1/(793587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11174 : Bounds (-46238421 / 200000000) (-28899013 / 125000000) (Real.log (793587 / 1000000)) := by
  have h := reflection_log_11174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11175_neg : (1507423 / 8000000) ≤ -Real.log (20000 / 24147) ∧
    -Real.log (20000 / 24147) ≤ (47106969 / 250000000) := by
  have h := checkLog_sound (w := (4147 / 44147)) (n := 12)
    (lo := (1507423 / 8000000)) (hi := (47106969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 20000) = 1/(20000 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11175 : Bounds (1507423 / 8000000) (47106969 / 250000000) (Real.log (24147 / 20000)) := by
  have h := reflection_log_11175_neg
  have he : Real.log (24147 / 20000) = -Real.log (20000 / 24147) := by
    rw [show ((24147 / 20000) : ℝ) = ((20000 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11176_neg : (58093379 / 250000000) ≤ -Real.log (15853 / 20000) ∧
    -Real.log (15853 / 20000) ≤ (232373517 / 1000000000) := by
  have h := checkLog_sound (w := (4147 / 35853)) (n := 12)
    (lo := (58093379 / 250000000)) (hi := (232373517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15853) = 1/(15853 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11176 : Bounds (-232373517 / 1000000000) (-58093379 / 250000000) (Real.log (15853 / 20000)) := by
  have h := reflection_log_11176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11177_neg : (43945641 / 1000000000) ≤ -Real.log (382802391 / 400000000) ∧
    -Real.log (382802391 / 400000000) ≤ (21972821 / 500000000) := by
  have h := checkLog_sound (w := (17197609 / 782802391)) (n := 12)
    (lo := (43945641 / 1000000000)) (hi := (21972821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 382802391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 382802391) = 1/(382802391 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11177 : Bounds (-21972821 / 500000000) (-43945641 / 1000000000) (Real.log (382802391 / 400000000)) := by
  have h := reflection_log_11177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11178_neg : (4354061 / 100000000) ≤ -Real.log (957393673431 / 1000000000000) ∧
    -Real.log (957393673431 / 1000000000000) ≤ (43540611 / 1000000000) := by
  have h := checkLog_sound (w := (42606326569 / 1957393673431)) (n := 12)
    (lo := (4354061 / 100000000)) (hi := (43540611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957393673431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957393673431) = 1/(957393673431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11178 : Bounds (-43540611 / 1000000000) (-4354061 / 100000000) (Real.log (957393673431 / 1000000000000)) := by
  have h := reflection_log_11178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11179_neg : (209421799 / 500000000) ≤ -Real.log (500000000000 / 760101286941) ∧
    -Real.log (500000000000 / 760101286941) ≤ (418843599 / 1000000000) := by
  have h := checkLog_sound (w := (260101286941 / 1260101286941)) (n := 12)
    (lo := (209421799 / 500000000)) (hi := (418843599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760101286941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760101286941 / 500000000000) = 1/(500000000000 / 760101286941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11179 : Bounds (209421799 / 500000000) (418843599 / 1000000000) (Real.log (760101286941 / 500000000000)) := by
  have h := reflection_log_11179_neg
  have he : Real.log (760101286941 / 500000000000) = -Real.log (500000000000 / 760101286941) := by
    rw [show ((760101286941 / 500000000000) : ℝ) = ((500000000000 / 760101286941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11180_neg : (420801391 / 1000000000) ≤ -Real.log (500000000000 / 761590866083) ∧
    -Real.log (500000000000 / 761590866083) ≤ (26300087 / 62500000) := by
  have h := checkLog_sound (w := (261590866083 / 1261590866083)) (n := 12)
    (lo := (420801391 / 1000000000)) (hi := (26300087 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761590866083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761590866083 / 500000000000) = 1/(500000000000 / 761590866083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11180 : Bounds (420801391 / 1000000000) (26300087 / 62500000) (Real.log (761590866083 / 500000000000)) := by
  have h := reflection_log_11180_neg
  have he : Real.log (761590866083 / 500000000000) = -Real.log (500000000000 / 761590866083) := by
    rw [show ((761590866083 / 500000000000) : ℝ) = ((500000000000 / 761590866083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11181_neg : (849679947 / 1000000000) ≤ -Real.log (500000000000 / 1169449081803) ∧
    -Real.log (500000000000 / 1169449081803) ≤ (849679949 / 1000000000) := by
  have h := checkLog_sound (w := (169449081803 / 2169449081803)) (n := 12)
    (lo := (156532767 / 1000000000)) (hi := (4891649 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169449081803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1169449081803 / 1000000000000) = 1/(500000000000 / 1169449081803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11181 : Bounds (849679947 / 1000000000) (849679949 / 1000000000) (Real.log (1169449081803 / 500000000000)) := by
  have h := reflection_log_11181_neg
  have he : Real.log (1169449081803 / 500000000000) = -Real.log (500000000000 / 1169449081803) := by
    rw [show ((1169449081803 / 500000000000) : ℝ) = ((500000000000 / 1169449081803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11182_neg : (852064313 / 1000000000) ≤ -Real.log (125000000000 / 293060200669) ∧
    -Real.log (125000000000 / 293060200669) ≤ (170412863 / 200000000) := by
  have h := checkLog_sound (w := (43060200669 / 543060200669)) (n := 12)
    (lo := (158917133 / 1000000000)) (hi := (79458567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293060200669 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293060200669 / 250000000000) = 1/(125000000000 / 293060200669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11182 : Bounds (852064313 / 1000000000) (170412863 / 200000000) (Real.log (293060200669 / 125000000000)) := by
  have h := reflection_log_11182_neg
  have he : Real.log (293060200669 / 125000000000) = -Real.log (125000000000 / 293060200669) := by
    rw [show ((293060200669 / 125000000000) : ℝ) = ((125000000000 / 293060200669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11183_neg : (338612801 / 1000000000) ≤ -Real.log (1000 / 1403) ∧
    -Real.log (1000 / 1403) ≤ (169306401 / 500000000) := by
  have h := checkLog_sound (w := (403 / 2403)) (n := 12)
    (lo := (338612801 / 1000000000)) (hi := (169306401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1000) = 1/(1000 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11183 : Bounds (338612801 / 1000000000) (169306401 / 500000000) (Real.log (1403 / 1000)) := by
  have h := reflection_log_11183_neg
  have he : Real.log (1403 / 1000) = -Real.log (1000 / 1403) := by
    rw [show ((1403 / 1000) : ℝ) = ((1000 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11184_neg : (103167633 / 200000000) ≤ -Real.log (597 / 1000) ∧
    -Real.log (597 / 1000) ≤ (257919083 / 500000000) := by
  have h := checkLog_sound (w := (403 / 1597)) (n := 12)
    (lo := (103167633 / 200000000)) (hi := (257919083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 597) = 1/(597 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11184 : Bounds (-257919083 / 500000000) (-103167633 / 200000000) (Real.log (597 / 1000)) := by
  have h := reflection_log_11184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11185_neg : (201459 / 500000000) ≤ -Real.log (1000000 / 1000403) ∧
    -Real.log (1000000 / 1000403) ≤ (402919 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 2000403)) (n := 12)
    (lo := (201459 / 500000000)) (hi := (402919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000403 / 1000000) = 1/(1000000 / 1000403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11185 : Bounds (201459 / 500000000) (402919 / 1000000000) (Real.log (1000403 / 1000000)) := by
  have h := reflection_log_11185_neg
  have he : Real.log (1000403 / 1000000) = -Real.log (1000000 / 1000403) := by
    rw [show ((1000403 / 1000000) : ℝ) = ((1000000 / 1000403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11186_neg : (403081 / 1000000000) ≤ -Real.log (999597 / 1000000) ∧
    -Real.log (999597 / 1000000) ≤ (201541 / 500000000) := by
  have h := checkLog_sound (w := (403 / 1999597)) (n := 12)
    (lo := (403081 / 1000000000)) (hi := (201541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999597) = 1/(999597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11186 : Bounds (-201541 / 500000000) (-403081 / 1000000000) (Real.log (999597 / 1000000)) := by
  have h := reflection_log_11186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11187_neg : (188104801 / 1000000000) ≤ -Real.log (12500 / 15087) ∧
    -Real.log (12500 / 15087) ≤ (94052401 / 500000000) := by
  have h := checkLog_sound (w := (2587 / 27587)) (n := 12)
    (lo := (188104801 / 1000000000)) (hi := (94052401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15087 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15087 / 12500) = 1/(12500 / 15087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11187 : Bounds (188104801 / 1000000000) (94052401 / 500000000) (Real.log (15087 / 12500)) := by
  have h := reflection_log_11187_neg
  have he : Real.log (15087 / 12500) = -Real.log (12500 / 15087) := by
    rw [show ((15087 / 12500) : ℝ) = ((12500 / 15087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11188_neg : (231881617 / 1000000000) ≤ -Real.log (9913 / 12500) ∧
    -Real.log (9913 / 12500) ≤ (115940809 / 500000000) := by
  have h := checkLog_sound (w := (2587 / 22413)) (n := 12)
    (lo := (231881617 / 1000000000)) (hi := (115940809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9913) = 1/(9913 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11188 : Bounds (-115940809 / 500000000) (-231881617 / 1000000000) (Real.log (9913 / 12500)) := by
  have h := reflection_log_11188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11189_neg : (94441243 / 500000000) ≤ -Real.log (1000000 / 1207899) ∧
    -Real.log (1000000 / 1207899) ≤ (188882487 / 1000000000) := by
  have h := checkLog_sound (w := (207899 / 2207899)) (n := 12)
    (lo := (94441243 / 500000000)) (hi := (188882487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207899 / 1000000) = 1/(1000000 / 1207899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11189 : Bounds (94441243 / 500000000) (188882487 / 1000000000) (Real.log (1207899 / 1000000)) := by
  have h := reflection_log_11189_neg
  have he : Real.log (1207899 / 1000000) = -Real.log (1000000 / 1207899) := by
    rw [show ((1207899 / 1000000) : ℝ) = ((1000000 / 1207899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11190_neg : (23306637 / 100000000) ≤ -Real.log (792101 / 1000000) ∧
    -Real.log (792101 / 1000000) ≤ (233066371 / 1000000000) := by
  have h := checkLog_sound (w := (207899 / 1792101)) (n := 12)
    (lo := (23306637 / 100000000)) (hi := (233066371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792101) = 1/(792101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11190 : Bounds (-233066371 / 1000000000) (-23306637 / 100000000) (Real.log (792101 / 1000000)) := by
  have h := reflection_log_11190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11191_neg : (44183883 / 1000000000) ≤ -Real.log (956778005799 / 1000000000000) ∧
    -Real.log (956778005799 / 1000000000000) ≤ (11045971 / 250000000) := by
  have h := checkLog_sound (w := (43221994201 / 1956778005799)) (n := 12)
    (lo := (44183883 / 1000000000)) (hi := (11045971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956778005799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956778005799) = 1/(956778005799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11191 : Bounds (-11045971 / 250000000) (-44183883 / 1000000000) (Real.log (956778005799 / 1000000000000)) := by
  have h := reflection_log_11191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11192_neg : (8755363 / 200000000) ≤ -Real.log (149557431 / 156250000) ∧
    -Real.log (149557431 / 156250000) ≤ (2736051 / 62500000) := by
  have h := checkLog_sound (w := (6692569 / 305807431)) (n := 12)
    (lo := (8755363 / 200000000)) (hi := (2736051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 149557431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 149557431) = 1/(149557431 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11192 : Bounds (-2736051 / 62500000) (-8755363 / 200000000) (Real.log (149557431 / 156250000)) := by
  have h := reflection_log_11192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11193_neg : (209993209 / 500000000) ≤ -Real.log (125000000000 / 190242610713) ∧
    -Real.log (125000000000 / 190242610713) ≤ (419986419 / 1000000000) := by
  have h := checkLog_sound (w := (65242610713 / 315242610713)) (n := 12)
    (lo := (209993209 / 500000000)) (hi := (419986419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190242610713 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190242610713 / 125000000000) = 1/(125000000000 / 190242610713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11193 : Bounds (209993209 / 500000000) (419986419 / 1000000000) (Real.log (190242610713 / 125000000000)) := by
  have h := reflection_log_11193_neg
  have he : Real.log (190242610713 / 125000000000) = -Real.log (125000000000 / 190242610713) := by
    rw [show ((190242610713 / 125000000000) : ℝ) = ((125000000000 / 190242610713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11194_neg : (52743607 / 125000000) ≤ -Real.log (20000000000 / 30498610657) ∧
    -Real.log (20000000000 / 30498610657) ≤ (421948857 / 1000000000) := by
  have h := checkLog_sound (w := (10498610657 / 50498610657)) (n := 12)
    (lo := (52743607 / 125000000)) (hi := (421948857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30498610657 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30498610657 / 20000000000) = 1/(20000000000 / 30498610657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11194 : Bounds (52743607 / 125000000) (421948857 / 1000000000) (Real.log (30498610657 / 20000000000)) := by
  have h := reflection_log_11194_neg
  have he : Real.log (30498610657 / 20000000000) = -Real.log (20000000000 / 30498610657) := by
    rw [show ((30498610657 / 20000000000) : ℝ) = ((20000000000 / 30498610657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11195_neg : (852064313 / 1000000000) ≤ -Real.log (20000000000 / 46889632107) ∧
    -Real.log (20000000000 / 46889632107) ≤ (170412863 / 200000000) := by
  have h := checkLog_sound (w := (6889632107 / 86889632107)) (n := 12)
    (lo := (158917133 / 1000000000)) (hi := (79458567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46889632107 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46889632107 / 40000000000) = 1/(20000000000 / 46889632107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11195 : Bounds (852064313 / 1000000000) (170412863 / 200000000) (Real.log (46889632107 / 20000000000)) := by
  have h := reflection_log_11195_neg
  have he : Real.log (46889632107 / 20000000000) = -Real.log (20000000000 / 46889632107) := by
    rw [show ((46889632107 / 20000000000) : ℝ) = ((20000000000 / 46889632107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11196_neg : (427225483 / 500000000) ≤ -Real.log (500000000000 / 1175041876047) ∧
    -Real.log (500000000000 / 1175041876047) ≤ (106806371 / 125000000) := by
  have h := checkLog_sound (w := (175041876047 / 2175041876047)) (n := 12)
    (lo := (80651893 / 500000000)) (hi := (161303787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175041876047 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1175041876047 / 1000000000000) = 1/(500000000000 / 1175041876047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11196 : Bounds (427225483 / 500000000) (106806371 / 125000000) (Real.log (1175041876047 / 500000000000)) := by
  have h := reflection_log_11196_neg
  have he : Real.log (1175041876047 / 500000000000) = -Real.log (500000000000 / 1175041876047) := by
    rw [show ((1175041876047 / 500000000000) : ℝ) = ((500000000000 / 1175041876047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11197_neg : (67865061 / 200000000) ≤ -Real.log (250 / 351) ∧
    -Real.log (250 / 351) ≤ (169662653 / 500000000) := by
  have h := checkLog_sound (w := (101 / 601)) (n := 12)
    (lo := (67865061 / 200000000)) (hi := (169662653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 250) = 1/(250 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11197 : Bounds (67865061 / 200000000) (169662653 / 500000000) (Real.log (351 / 250)) := by
  have h := reflection_log_11197_neg
  have he : Real.log (351 / 250) = -Real.log (250 / 351) := by
    rw [show ((351 / 250) : ℝ) = ((250 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11198_neg : (517514611 / 1000000000) ≤ -Real.log (149 / 250) ∧
    -Real.log (149 / 250) ≤ (129378653 / 250000000) := by
  have h := checkLog_sound (w := (101 / 399)) (n := 12)
    (lo := (517514611 / 1000000000)) (hi := (129378653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 149) = 1/(149 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11198 : Bounds (-129378653 / 250000000) (-517514611 / 1000000000) (Real.log (149 / 250)) := by
  have h := reflection_log_11198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11199_neg : (201959 / 500000000) ≤ -Real.log (250000 / 250101) ∧
    -Real.log (250000 / 250101) ≤ (403919 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 500101)) (n := 12)
    (lo := (201959 / 500000000)) (hi := (403919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250101 / 250000) = 1/(250000 / 250101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11199 : Bounds (201959 / 500000000) (403919 / 1000000000) (Real.log (250101 / 250000)) := by
  have h := reflection_log_11199_neg
  have he : Real.log (250101 / 250000) = -Real.log (250000 / 250101) := by
    rw [show ((250101 / 250000) : ℝ) = ((250000 / 250101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
