import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6080_neg : (93134177 / 1000000000) ≤ -Real.log (1000000 / 1097609) ∧
    -Real.log (1000000 / 1097609) ≤ (46567089 / 500000000) := by
  have h := checkLog_sound (w := (97609 / 2097609)) (n := 12)
    (lo := (93134177 / 1000000000)) (hi := (46567089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097609 / 1000000) = 1/(1000000 / 1097609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6080 : Bounds (93134177 / 1000000000) (46567089 / 500000000) (Real.log (1097609 / 1000000)) := by
  have h := reflection_log_6080_neg
  have he : Real.log (1097609 / 1000000) = -Real.log (1000000 / 1097609) := by
    rw [show ((1097609 / 1000000) : ℝ) = ((1000000 / 1097609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6081_neg : (102707371 / 1000000000) ≤ -Real.log (902391 / 1000000) ∧
    -Real.log (902391 / 1000000) ≤ (25676843 / 250000000) := by
  have h := checkLog_sound (w := (97609 / 1902391)) (n := 12)
    (lo := (102707371 / 1000000000)) (hi := (25676843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902391) = 1/(902391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6081 : Bounds (-25676843 / 250000000) (-102707371 / 1000000000) (Real.log (902391 / 1000000)) := by
  have h := reflection_log_6081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6082_neg : (4786597 / 500000000) ≤ -Real.log (990472483119 / 1000000000000) ∧
    -Real.log (990472483119 / 1000000000000) ≤ (1914639 / 200000000) := by
  have h := checkLog_sound (w := (9527516881 / 1990472483119)) (n := 12)
    (lo := (4786597 / 500000000)) (hi := (1914639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990472483119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990472483119) = 1/(990472483119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6082 : Bounds (-1914639 / 200000000) (-4786597 / 500000000) (Real.log (990472483119 / 1000000000000)) := by
  have h := reflection_log_6082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6083_neg : (9525163 / 1000000000) ≤ -Real.log (39620802271 / 40000000000) ∧
    -Real.log (39620802271 / 40000000000) ≤ (2381291 / 250000000) := by
  have h := checkLog_sound (w := (379197729 / 79620802271)) (n := 12)
    (lo := (9525163 / 1000000000)) (hi := (2381291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39620802271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39620802271) = 1/(39620802271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6083 : Bounds (-2381291 / 250000000) (-9525163 / 1000000000) (Real.log (39620802271 / 40000000000)) := by
  have h := reflection_log_6083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6084_neg : (195348867 / 1000000000) ≤ -Real.log (500000000000 / 607867521201) ∧
    -Real.log (500000000000 / 607867521201) ≤ (48837217 / 250000000) := by
  have h := checkLog_sound (w := (107867521201 / 1107867521201)) (n := 12)
    (lo := (195348867 / 1000000000)) (hi := (48837217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607867521201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607867521201 / 500000000000) = 1/(500000000000 / 607867521201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6084 : Bounds (195348867 / 1000000000) (48837217 / 250000000) (Real.log (607867521201 / 500000000000)) := by
  have h := reflection_log_6084_neg
  have he : Real.log (607867521201 / 500000000000) = -Real.log (500000000000 / 607867521201) := by
    rw [show ((607867521201 / 500000000000) : ℝ) = ((500000000000 / 607867521201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6085_neg : (195841549 / 1000000000) ≤ -Real.log (62500000000 / 76020885071) ∧
    -Real.log (62500000000 / 76020885071) ≤ (3916831 / 20000000) := by
  have h := checkLog_sound (w := (13520885071 / 138520885071)) (n := 12)
    (lo := (195841549 / 1000000000)) (hi := (3916831 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76020885071 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76020885071 / 62500000000) = 1/(62500000000 / 76020885071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6085 : Bounds (195841549 / 1000000000) (3916831 / 20000000) (Real.log (76020885071 / 62500000000)) := by
  have h := reflection_log_6085_neg
  have he : Real.log (76020885071 / 62500000000) = -Real.log (62500000000 / 76020885071) := by
    rw [show ((76020885071 / 62500000000) : ℝ) = ((62500000000 / 76020885071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6086_neg : (98037333 / 250000000) ≤ -Real.log (500000000000 / 740079365079) ∧
    -Real.log (500000000000 / 740079365079) ≤ (392149333 / 1000000000) := by
  have h := checkLog_sound (w := (240079365079 / 1240079365079)) (n := 12)
    (lo := (98037333 / 250000000)) (hi := (392149333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740079365079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740079365079 / 500000000000) = 1/(500000000000 / 740079365079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6086 : Bounds (98037333 / 250000000) (392149333 / 1000000000) (Real.log (740079365079 / 500000000000)) := by
  have h := reflection_log_6086_neg
  have he : Real.log (740079365079 / 500000000000) = -Real.log (500000000000 / 740079365079) := by
    rw [show ((740079365079 / 500000000000) : ℝ) = ((500000000000 / 740079365079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6087_neg : (98089281 / 250000000) ≤ -Real.log (100000000000 / 148046632767) ∧
    -Real.log (100000000000 / 148046632767) ≤ (3138857 / 8000000) := by
  have h := checkLog_sound (w := (48046632767 / 248046632767)) (n := 12)
    (lo := (98089281 / 250000000)) (hi := (3138857 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148046632767 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148046632767 / 100000000000) = 1/(100000000000 / 148046632767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6087 : Bounds (98089281 / 250000000) (3138857 / 8000000) (Real.log (148046632767 / 100000000000)) := by
  have h := reflection_log_6087_neg
  have he : Real.log (148046632767 / 100000000000) = -Real.log (100000000000 / 148046632767) := by
    rw [show ((148046632767 / 100000000000) : ℝ) = ((100000000000 / 148046632767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6088_neg : (22142687 / 125000000) ≤ -Real.log (5000 / 5969) ∧
    -Real.log (5000 / 5969) ≤ (177141497 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 10969)) (n := 12)
    (lo := (22142687 / 125000000)) (hi := (177141497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5969 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5969 / 5000) = 1/(5000 / 5969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6088 : Bounds (22142687 / 125000000) (177141497 / 1000000000) (Real.log (5969 / 5000)) := by
  have h := reflection_log_6088_neg
  have he : Real.log (5969 / 5000) = -Real.log (5000 / 5969) := by
    rw [show ((5969 / 5000) : ℝ) = ((5000 / 5969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6089_neg : (53855857 / 250000000) ≤ -Real.log (4031 / 5000) ∧
    -Real.log (4031 / 5000) ≤ (215423429 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 9031)) (n := 12)
    (lo := (53855857 / 250000000)) (hi := (215423429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4031) = 1/(4031 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6089 : Bounds (-215423429 / 1000000000) (-53855857 / 250000000) (Real.log (4031 / 5000)) := by
  have h := reflection_log_6089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6090_neg : (193781 / 1000000000) ≤ -Real.log (5000000 / 5000969) ∧
    -Real.log (5000000 / 5000969) ≤ (96891 / 500000000) := by
  have h := checkLog_sound (w := (969 / 10000969)) (n := 12)
    (lo := (193781 / 1000000000)) (hi := (96891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000969 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000969 / 5000000) = 1/(5000000 / 5000969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6090 : Bounds (193781 / 1000000000) (96891 / 500000000) (Real.log (5000969 / 5000000)) := by
  have h := reflection_log_6090_neg
  have he : Real.log (5000969 / 5000000) = -Real.log (5000000 / 5000969) := by
    rw [show ((5000969 / 5000000) : ℝ) = ((5000000 / 5000969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6091_neg : (96909 / 500000000) ≤ -Real.log (4999031 / 5000000) ∧
    -Real.log (4999031 / 5000000) ≤ (193819 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 9999031)) (n := 12)
    (lo := (96909 / 500000000)) (hi := (193819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999031) = 1/(4999031 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6091 : Bounds (-193819 / 1000000000) (-96909 / 500000000) (Real.log (4999031 / 5000000)) := by
  have h := reflection_log_6091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6092_neg : (3718333 / 40000000) ≤ -Real.log (125000 / 137177) ∧
    -Real.log (125000 / 137177) ≤ (46479163 / 500000000) := by
  have h := checkLog_sound (w := (12177 / 262177)) (n := 12)
    (lo := (3718333 / 40000000)) (hi := (46479163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137177 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137177 / 125000) = 1/(125000 / 137177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6092 : Bounds (3718333 / 40000000) (46479163 / 500000000) (Real.log (137177 / 125000)) := by
  have h := reflection_log_6092_neg
  have he : Real.log (137177 / 125000) = -Real.log (125000 / 137177) := by
    rw [show ((137177 / 125000) : ℝ) = ((125000 / 137177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6093_neg : (51246759 / 500000000) ≤ -Real.log (112823 / 125000) ∧
    -Real.log (112823 / 125000) ≤ (102493519 / 1000000000) := by
  have h := checkLog_sound (w := (12177 / 237823)) (n := 12)
    (lo := (51246759 / 500000000)) (hi := (102493519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112823) = 1/(112823 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6093 : Bounds (-102493519 / 1000000000) (-51246759 / 500000000) (Real.log (112823 / 125000)) := by
  have h := reflection_log_6093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6094_neg : (93180641 / 1000000000) ≤ -Real.log (50000 / 54883) ∧
    -Real.log (50000 / 54883) ≤ (46590321 / 500000000) := by
  have h := checkLog_sound (w := (4883 / 104883)) (n := 12)
    (lo := (93180641 / 1000000000)) (hi := (46590321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54883 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54883 / 50000) = 1/(50000 / 54883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6094 : Bounds (93180641 / 1000000000) (46590321 / 500000000) (Real.log (54883 / 50000)) := by
  have h := reflection_log_6094_neg
  have he : Real.log (54883 / 50000) = -Real.log (50000 / 54883) := by
    rw [show ((54883 / 50000) : ℝ) = ((50000 / 54883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6095_neg : (102763889 / 1000000000) ≤ -Real.log (45117 / 50000) ∧
    -Real.log (45117 / 50000) ≤ (10276389 / 100000000) := by
  have h := checkLog_sound (w := (4883 / 95117)) (n := 12)
    (lo := (102763889 / 1000000000)) (hi := (10276389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45117) = 1/(45117 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6095 : Bounds (-10276389 / 100000000) (-102763889 / 1000000000) (Real.log (45117 / 50000)) := by
  have h := reflection_log_6095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6096_neg : (598953 / 62500000) ≤ -Real.log (2476156311 / 2500000000) ∧
    -Real.log (2476156311 / 2500000000) ≤ (9583249 / 1000000000) := by
  have h := checkLog_sound (w := (23843689 / 4976156311)) (n := 12)
    (lo := (598953 / 62500000)) (hi := (9583249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2476156311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2476156311) = 1/(2476156311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6096 : Bounds (-9583249 / 1000000000) (-598953 / 62500000) (Real.log (2476156311 / 2500000000)) := by
  have h := reflection_log_6096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6097_neg : (1191899 / 125000000) ≤ -Real.log (15476720671 / 15625000000) ∧
    -Real.log (15476720671 / 15625000000) ≤ (9535193 / 1000000000) := by
  have h := checkLog_sound (w := (148279329 / 31101720671)) (n := 12)
    (lo := (1191899 / 125000000)) (hi := (9535193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15476720671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15476720671) = 1/(15476720671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6097 : Bounds (-9535193 / 1000000000) (-1191899 / 125000000) (Real.log (15476720671 / 15625000000)) := by
  have h := reflection_log_6097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6098_neg : (195451843 / 1000000000) ≤ -Real.log (500000000000 / 607930120631) ∧
    -Real.log (500000000000 / 607930120631) ≤ (48862961 / 250000000) := by
  have h := checkLog_sound (w := (107930120631 / 1107930120631)) (n := 12)
    (lo := (195451843 / 1000000000)) (hi := (48862961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607930120631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607930120631 / 500000000000) = 1/(500000000000 / 607930120631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6098 : Bounds (195451843 / 1000000000) (48862961 / 250000000) (Real.log (607930120631 / 500000000000)) := by
  have h := reflection_log_6098_neg
  have he : Real.log (607930120631 / 500000000000) = -Real.log (500000000000 / 607930120631) := by
    rw [show ((607930120631 / 500000000000) : ℝ) = ((500000000000 / 607930120631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6099_neg : (195944531 / 1000000000) ≤ -Real.log (7812500000 / 9503589279) ∧
    -Real.log (7812500000 / 9503589279) ≤ (48986133 / 250000000) := by
  have h := checkLog_sound (w := (1691089279 / 17316089279)) (n := 12)
    (lo := (195944531 / 1000000000)) (hi := (48986133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9503589279 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9503589279 / 7812500000) = 1/(7812500000 / 9503589279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6099 : Bounds (195944531 / 1000000000) (48986133 / 250000000) (Real.log (9503589279 / 7812500000)) := by
  have h := reflection_log_6099_neg
  have he : Real.log (9503589279 / 7812500000) = -Real.log (7812500000 / 9503589279) := by
    rw [show ((9503589279 / 7812500000) : ℝ) = ((7812500000 / 9503589279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6100_neg : (98089281 / 250000000) ≤ -Real.log (250000000000 / 370116581917) ∧
    -Real.log (250000000000 / 370116581917) ≤ (3138857 / 8000000) := by
  have h := checkLog_sound (w := (120116581917 / 620116581917)) (n := 12)
    (lo := (98089281 / 250000000)) (hi := (3138857 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370116581917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370116581917 / 250000000000) = 1/(250000000000 / 370116581917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6100 : Bounds (98089281 / 250000000) (3138857 / 8000000) (Real.log (370116581917 / 250000000000)) := by
  have h := reflection_log_6100_neg
  have he : Real.log (370116581917 / 250000000000) = -Real.log (250000000000 / 370116581917) := by
    rw [show ((370116581917 / 250000000000) : ℝ) = ((250000000000 / 370116581917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6101_neg : (15702597 / 40000000) ≤ -Real.log (100000000000 / 148077400149) ∧
    -Real.log (100000000000 / 148077400149) ≤ (196282463 / 500000000) := by
  have h := checkLog_sound (w := (48077400149 / 248077400149)) (n := 12)
    (lo := (15702597 / 40000000)) (hi := (196282463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148077400149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148077400149 / 100000000000) = 1/(100000000000 / 148077400149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6101 : Bounds (15702597 / 40000000) (196282463 / 500000000) (Real.log (148077400149 / 100000000000)) := by
  have h := reflection_log_6101_neg
  have he : Real.log (148077400149 / 100000000000) = -Real.log (100000000000 / 148077400149) := by
    rw [show ((148077400149 / 100000000000) : ℝ) = ((100000000000 / 148077400149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6102_neg : (177225259 / 1000000000) ≤ -Real.log (10000 / 11939) ∧
    -Real.log (10000 / 11939) ≤ (8861263 / 50000000) := by
  have h := checkLog_sound (w := (1939 / 21939)) (n := 12)
    (lo := (177225259 / 1000000000)) (hi := (8861263 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11939 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11939 / 10000) = 1/(10000 / 11939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6102 : Bounds (177225259 / 1000000000) (8861263 / 50000000) (Real.log (11939 / 10000)) := by
  have h := reflection_log_6102_neg
  have he : Real.log (11939 / 10000) = -Real.log (10000 / 11939) := by
    rw [show ((11939 / 10000) : ℝ) = ((10000 / 11939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6103_neg : (107773737 / 500000000) ≤ -Real.log (8061 / 10000) ∧
    -Real.log (8061 / 10000) ≤ (8621899 / 40000000) := by
  have h := checkLog_sound (w := (1939 / 18061)) (n := 12)
    (lo := (107773737 / 500000000)) (hi := (8621899 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8061) = 1/(8061 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6103 : Bounds (-8621899 / 40000000) (-107773737 / 500000000) (Real.log (8061 / 10000)) := by
  have h := reflection_log_6103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6104_neg : (193881 / 1000000000) ≤ -Real.log (10000000 / 10001939) ∧
    -Real.log (10000000 / 10001939) ≤ (96941 / 500000000) := by
  have h := checkLog_sound (w := (1939 / 20001939)) (n := 12)
    (lo := (193881 / 1000000000)) (hi := (96941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001939 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001939 / 10000000) = 1/(10000000 / 10001939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6104 : Bounds (193881 / 1000000000) (96941 / 500000000) (Real.log (10001939 / 10000000)) := by
  have h := reflection_log_6104_neg
  have he : Real.log (10001939 / 10000000) = -Real.log (10000000 / 10001939) := by
    rw [show ((10001939 / 10000000) : ℝ) = ((10000000 / 10001939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6105_neg : (96959 / 500000000) ≤ -Real.log (9998061 / 10000000) ∧
    -Real.log (9998061 / 10000000) ≤ (193919 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 19998061)) (n := 12)
    (lo := (96959 / 500000000)) (hi := (193919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998061) = 1/(9998061 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6105 : Bounds (-193919 / 1000000000) (-96959 / 500000000) (Real.log (9998061 / 10000000)) := by
  have h := reflection_log_6105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6106_neg : (93004797 / 1000000000) ≤ -Real.log (1000000 / 1097467) ∧
    -Real.log (1000000 / 1097467) ≤ (46502399 / 500000000) := by
  have h := checkLog_sound (w := (97467 / 2097467)) (n := 12)
    (lo := (93004797 / 1000000000)) (hi := (46502399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097467 / 1000000) = 1/(1000000 / 1097467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6106 : Bounds (93004797 / 1000000000) (46502399 / 500000000) (Real.log (1097467 / 1000000)) := by
  have h := reflection_log_6106_neg
  have he : Real.log (1097467 / 1000000) = -Real.log (1000000 / 1097467) := by
    rw [show ((1097467 / 1000000) : ℝ) = ((1000000 / 1097467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6107_neg : (12818753 / 125000000) ≤ -Real.log (902533 / 1000000) ∧
    -Real.log (902533 / 1000000) ≤ (4102001 / 40000000) := by
  have h := checkLog_sound (w := (97467 / 1902533)) (n := 12)
    (lo := (12818753 / 125000000)) (hi := (4102001 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902533) = 1/(902533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6107 : Bounds (-4102001 / 40000000) (-12818753 / 125000000) (Real.log (902533 / 1000000)) := by
  have h := reflection_log_6107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6108_neg : (46613551 / 500000000) ≤ -Real.log (1000000 / 1097711) ∧
    -Real.log (1000000 / 1097711) ≤ (93227103 / 1000000000) := by
  have h := checkLog_sound (w := (97711 / 2097711)) (n := 12)
    (lo := (46613551 / 500000000)) (hi := (93227103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097711 / 1000000) = 1/(1000000 / 1097711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6108 : Bounds (46613551 / 500000000) (93227103 / 1000000000) (Real.log (1097711 / 1000000)) := by
  have h := reflection_log_6108_neg
  have he : Real.log (1097711 / 1000000) = -Real.log (1000000 / 1097711) := by
    rw [show ((1097711 / 1000000) : ℝ) = ((1000000 / 1097711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6109_neg : (102820411 / 1000000000) ≤ -Real.log (902289 / 1000000) ∧
    -Real.log (902289 / 1000000) ≤ (25705103 / 250000000) := by
  have h := checkLog_sound (w := (97711 / 1902289)) (n := 12)
    (lo := (102820411 / 1000000000)) (hi := (25705103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902289) = 1/(902289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6109 : Bounds (-25705103 / 250000000) (-102820411 / 1000000000) (Real.log (902289 / 1000000)) := by
  have h := reflection_log_6109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6110_neg : (2398327 / 250000000) ≤ -Real.log (990452560479 / 1000000000000) ∧
    -Real.log (990452560479 / 1000000000000) ≤ (9593309 / 1000000000) := by
  have h := checkLog_sound (w := (9547439521 / 1990452560479)) (n := 12)
    (lo := (2398327 / 250000000)) (hi := (9593309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990452560479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990452560479) = 1/(990452560479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6110 : Bounds (-9593309 / 1000000000) (-2398327 / 250000000) (Real.log (990452560479 / 1000000000000)) := by
  have h := reflection_log_6110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6111_neg : (9545227 / 1000000000) ≤ -Real.log (990500183911 / 1000000000000) ∧
    -Real.log (990500183911 / 1000000000000) ≤ (2386307 / 250000000) := by
  have h := checkLog_sound (w := (9499816089 / 1990500183911)) (n := 12)
    (lo := (9545227 / 1000000000)) (hi := (2386307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990500183911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990500183911) = 1/(990500183911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6111 : Bounds (-2386307 / 250000000) (-9545227 / 1000000000) (Real.log (990500183911 / 1000000000000)) := by
  have h := reflection_log_6111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6112_neg : (195554821 / 1000000000) ≤ -Real.log (100000000000 / 121598545427) ∧
    -Real.log (100000000000 / 121598545427) ≤ (97777411 / 500000000) := by
  have h := checkLog_sound (w := (21598545427 / 221598545427)) (n := 12)
    (lo := (195554821 / 1000000000)) (hi := (97777411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121598545427 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121598545427 / 100000000000) = 1/(100000000000 / 121598545427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6112 : Bounds (195554821 / 1000000000) (97777411 / 500000000) (Real.log (121598545427 / 100000000000)) := by
  have h := reflection_log_6112_neg
  have he : Real.log (121598545427 / 100000000000) = -Real.log (100000000000 / 121598545427) := by
    rw [show ((121598545427 / 100000000000) : ℝ) = ((100000000000 / 121598545427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6113_neg : (196047513 / 1000000000) ≤ -Real.log (31250000000 / 38018272139) ∧
    -Real.log (31250000000 / 38018272139) ≤ (98023757 / 500000000) := by
  have h := checkLog_sound (w := (6768272139 / 69268272139)) (n := 12)
    (lo := (196047513 / 1000000000)) (hi := (98023757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38018272139 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38018272139 / 31250000000) = 1/(31250000000 / 38018272139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6113 : Bounds (196047513 / 1000000000) (98023757 / 500000000) (Real.log (38018272139 / 31250000000)) := by
  have h := reflection_log_6113_neg
  have he : Real.log (38018272139 / 31250000000) = -Real.log (31250000000 / 38018272139) := by
    rw [show ((38018272139 / 31250000000) : ℝ) = ((31250000000 / 38018272139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6114_neg : (15702597 / 40000000) ≤ -Real.log (62500000000 / 92548375093) ∧
    -Real.log (62500000000 / 92548375093) ≤ (196282463 / 500000000) := by
  have h := checkLog_sound (w := (30048375093 / 155048375093)) (n := 12)
    (lo := (15702597 / 40000000)) (hi := (196282463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92548375093 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92548375093 / 62500000000) = 1/(62500000000 / 92548375093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6114 : Bounds (15702597 / 40000000) (196282463 / 500000000) (Real.log (92548375093 / 62500000000)) := by
  have h := reflection_log_6114_neg
  have he : Real.log (92548375093 / 62500000000) = -Real.log (62500000000 / 92548375093) := by
    rw [show ((92548375093 / 62500000000) : ℝ) = ((62500000000 / 92548375093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6115_neg : (196386367 / 500000000) ≤ -Real.log (250000000000 / 370270437911) ∧
    -Real.log (250000000000 / 370270437911) ≤ (78554547 / 200000000) := by
  have h := checkLog_sound (w := (120270437911 / 620270437911)) (n := 12)
    (lo := (196386367 / 500000000)) (hi := (78554547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370270437911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370270437911 / 250000000000) = 1/(250000000000 / 370270437911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6115 : Bounds (196386367 / 500000000) (78554547 / 200000000) (Real.log (370270437911 / 250000000000)) := by
  have h := reflection_log_6115_neg
  have he : Real.log (370270437911 / 250000000000) = -Real.log (250000000000 / 370270437911) := by
    rw [show ((370270437911 / 250000000000) : ℝ) = ((250000000000 / 370270437911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6116_neg : (88654507 / 500000000) ≤ -Real.log (500 / 597) ∧
    -Real.log (500 / 597) ≤ (35461803 / 200000000) := by
  have h := checkLog_sound (w := (97 / 1097)) (n := 12)
    (lo := (88654507 / 500000000)) (hi := (35461803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597 / 500) = 1/(500 / 597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6116 : Bounds (88654507 / 500000000) (35461803 / 200000000) (Real.log (597 / 500)) := by
  have h := reflection_log_6116_neg
  have he : Real.log (597 / 500) = -Real.log (500 / 597) := by
    rw [show ((597 / 500) : ℝ) = ((500 / 597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6117_neg : (13479471 / 62500000) ≤ -Real.log (403 / 500) ∧
    -Real.log (403 / 500) ≤ (215671537 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 903)) (n := 12)
    (lo := (13479471 / 62500000)) (hi := (215671537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 403) = 1/(403 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6117 : Bounds (-215671537 / 1000000000) (-13479471 / 62500000) (Real.log (403 / 500)) := by
  have h := reflection_log_6117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6118_neg : (193981 / 1000000000) ≤ -Real.log (500000 / 500097) ∧
    -Real.log (500000 / 500097) ≤ (96991 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1000097)) (n := 12)
    (lo := (193981 / 1000000000)) (hi := (96991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500097 / 500000) = 1/(500000 / 500097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6118 : Bounds (193981 / 1000000000) (96991 / 500000000) (Real.log (500097 / 500000)) := by
  have h := reflection_log_6118_neg
  have he : Real.log (500097 / 500000) = -Real.log (500000 / 500097) := by
    rw [show ((500097 / 500000) : ℝ) = ((500000 / 500097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6119_neg : (97009 / 500000000) ≤ -Real.log (499903 / 500000) ∧
    -Real.log (499903 / 500000) ≤ (194019 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 999903)) (n := 12)
    (lo := (97009 / 500000000)) (hi := (194019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499903) = 1/(499903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6119 : Bounds (-194019 / 1000000000) (-97009 / 500000000) (Real.log (499903 / 500000)) := by
  have h := reflection_log_6119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6120_neg : (46525633 / 500000000) ≤ -Real.log (500000 / 548759) ∧
    -Real.log (500000 / 548759) ≤ (93051267 / 1000000000) := by
  have h := checkLog_sound (w := (48759 / 1048759)) (n := 12)
    (lo := (46525633 / 500000000)) (hi := (93051267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548759 / 500000) = 1/(500000 / 548759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6120 : Bounds (46525633 / 500000000) (93051267 / 1000000000) (Real.log (548759 / 500000)) := by
  have h := reflection_log_6120_neg
  have he : Real.log (548759 / 500000) = -Real.log (500000 / 548759) := by
    rw [show ((548759 / 500000) : ℝ) = ((500000 / 548759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6121_neg : (102606533 / 1000000000) ≤ -Real.log (451241 / 500000) ∧
    -Real.log (451241 / 500000) ≤ (51303267 / 500000000) := by
  have h := checkLog_sound (w := (48759 / 951241)) (n := 12)
    (lo := (102606533 / 1000000000)) (hi := (51303267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451241) = 1/(451241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6121 : Bounds (-51303267 / 500000000) (-102606533 / 1000000000) (Real.log (451241 / 500000)) := by
  have h := reflection_log_6121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6122_neg : (11659309 / 125000000) ≤ -Real.log (1000000 / 1097763) ∧
    -Real.log (1000000 / 1097763) ≤ (93274473 / 1000000000) := by
  have h := checkLog_sound (w := (97763 / 2097763)) (n := 12)
    (lo := (11659309 / 125000000)) (hi := (93274473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097763 / 1000000) = 1/(1000000 / 1097763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6122 : Bounds (11659309 / 125000000) (93274473 / 1000000000) (Real.log (1097763 / 1000000)) := by
  have h := reflection_log_6122_neg
  have he : Real.log (1097763 / 1000000) = -Real.log (1000000 / 1097763) := by
    rw [show ((1097763 / 1000000) : ℝ) = ((1000000 / 1097763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6123_neg : (102878043 / 1000000000) ≤ -Real.log (902237 / 1000000) ∧
    -Real.log (902237 / 1000000) ≤ (25719511 / 250000000) := by
  have h := checkLog_sound (w := (97763 / 1902237)) (n := 12)
    (lo := (102878043 / 1000000000)) (hi := (25719511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902237) = 1/(902237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6123 : Bounds (-25719511 / 250000000) (-102878043 / 1000000000) (Real.log (902237 / 1000000)) := by
  have h := reflection_log_6123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6124_neg : (9603571 / 1000000000) ≤ -Real.log (990442395831 / 1000000000000) ∧
    -Real.log (990442395831 / 1000000000000) ≤ (2400893 / 250000000) := by
  have h := checkLog_sound (w := (9557604169 / 1990442395831)) (n := 12)
    (lo := (9603571 / 1000000000)) (hi := (2400893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990442395831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990442395831) = 1/(990442395831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6124 : Bounds (-2400893 / 250000000) (-9603571 / 1000000000) (Real.log (990442395831 / 1000000000000)) := by
  have h := reflection_log_6124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6125_neg : (4777633 / 500000000) ≤ -Real.log (247622559919 / 250000000000) ∧
    -Real.log (247622559919 / 250000000000) ≤ (9555267 / 1000000000) := by
  have h := checkLog_sound (w := (2377440081 / 497622559919)) (n := 12)
    (lo := (4777633 / 500000000)) (hi := (9555267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247622559919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247622559919) = 1/(247622559919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6125 : Bounds (-9555267 / 1000000000) (-4777633 / 500000000) (Real.log (247622559919 / 250000000000)) := by
  have h := reflection_log_6125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6126_neg : (978289 / 5000000) ≤ -Real.log (100000000000 / 121611068143) ∧
    -Real.log (100000000000 / 121611068143) ≤ (195657801 / 1000000000) := by
  have h := checkLog_sound (w := (21611068143 / 221611068143)) (n := 12)
    (lo := (978289 / 5000000)) (hi := (195657801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121611068143 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121611068143 / 100000000000) = 1/(100000000000 / 121611068143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6126 : Bounds (978289 / 5000000) (195657801 / 1000000000) (Real.log (121611068143 / 100000000000)) := by
  have h := reflection_log_6126_neg
  have he : Real.log (121611068143 / 100000000000) = -Real.log (100000000000 / 121611068143) := by
    rw [show ((121611068143 / 100000000000) : ℝ) = ((100000000000 / 121611068143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6127_neg : (49038129 / 250000000) ≤ -Real.log (250000000000 / 304178115063) ∧
    -Real.log (250000000000 / 304178115063) ≤ (196152517 / 1000000000) := by
  have h := checkLog_sound (w := (54178115063 / 554178115063)) (n := 12)
    (lo := (49038129 / 250000000)) (hi := (196152517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304178115063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304178115063 / 250000000000) = 1/(250000000000 / 304178115063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6127 : Bounds (49038129 / 250000000) (196152517 / 1000000000) (Real.log (304178115063 / 250000000000)) := by
  have h := reflection_log_6127_neg
  have he : Real.log (304178115063 / 250000000000) = -Real.log (250000000000 / 304178115063) := by
    rw [show ((304178115063 / 250000000000) : ℝ) = ((250000000000 / 304178115063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6128_neg : (196386367 / 500000000) ≤ -Real.log (500000000000 / 740540875821) ∧
    -Real.log (500000000000 / 740540875821) ≤ (78554547 / 200000000) := by
  have h := checkLog_sound (w := (240540875821 / 1240540875821)) (n := 12)
    (lo := (196386367 / 500000000)) (hi := (78554547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740540875821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740540875821 / 500000000000) = 1/(500000000000 / 740540875821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6128 : Bounds (196386367 / 500000000) (78554547 / 200000000) (Real.log (740540875821 / 500000000000)) := by
  have h := reflection_log_6128_neg
  have he : Real.log (740540875821 / 500000000000) = -Real.log (500000000000 / 740540875821) := by
    rw [show ((740540875821 / 500000000000) : ℝ) = ((500000000000 / 740540875821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6129_neg : (392980551 / 1000000000) ≤ -Real.log (250000000000 / 370347394541) ∧
    -Real.log (250000000000 / 370347394541) ≤ (49122569 / 125000000) := by
  have h := checkLog_sound (w := (120347394541 / 620347394541)) (n := 12)
    (lo := (392980551 / 1000000000)) (hi := (49122569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370347394541 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370347394541 / 250000000000) = 1/(250000000000 / 370347394541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6129 : Bounds (392980551 / 1000000000) (49122569 / 125000000) (Real.log (370347394541 / 250000000000)) := by
  have h := reflection_log_6129_neg
  have he : Real.log (370347394541 / 250000000000) = -Real.log (250000000000 / 370347394541) := by
    rw [show ((370347394541 / 250000000000) : ℝ) = ((250000000000 / 370347394541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6130_neg : (177392763 / 1000000000) ≤ -Real.log (10000 / 11941) ∧
    -Real.log (10000 / 11941) ≤ (44348191 / 250000000) := by
  have h := checkLog_sound (w := (1941 / 21941)) (n := 12)
    (lo := (177392763 / 1000000000)) (hi := (44348191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11941 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11941 / 10000) = 1/(10000 / 11941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6130 : Bounds (177392763 / 1000000000) (44348191 / 250000000) (Real.log (11941 / 10000)) := by
  have h := reflection_log_6130_neg
  have he : Real.log (11941 / 10000) = -Real.log (10000 / 11941) := by
    rw [show ((11941 / 10000) : ℝ) = ((10000 / 11941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6131_neg : (215795613 / 1000000000) ≤ -Real.log (8059 / 10000) ∧
    -Real.log (8059 / 10000) ≤ (107897807 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 18059)) (n := 12)
    (lo := (215795613 / 1000000000)) (hi := (107897807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8059) = 1/(8059 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6131 : Bounds (-107897807 / 500000000) (-215795613 / 1000000000) (Real.log (8059 / 10000)) := by
  have h := reflection_log_6131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6132_neg : (194081 / 1000000000) ≤ -Real.log (10000000 / 10001941) ∧
    -Real.log (10000000 / 10001941) ≤ (97041 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 20001941)) (n := 12)
    (lo := (194081 / 1000000000)) (hi := (97041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001941 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001941 / 10000000) = 1/(10000000 / 10001941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6132 : Bounds (194081 / 1000000000) (97041 / 500000000) (Real.log (10001941 / 10000000)) := by
  have h := reflection_log_6132_neg
  have he : Real.log (10001941 / 10000000) = -Real.log (10000000 / 10001941) := by
    rw [show ((10001941 / 10000000) : ℝ) = ((10000000 / 10001941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6133_neg : (97059 / 500000000) ≤ -Real.log (9998059 / 10000000) ∧
    -Real.log (9998059 / 10000000) ≤ (194119 / 1000000000) := by
  have h := checkLog_sound (w := (1941 / 19998059)) (n := 12)
    (lo := (97059 / 500000000)) (hi := (194119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998059) = 1/(9998059 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6133 : Bounds (-194119 / 1000000000) (-97059 / 500000000) (Real.log (9998059 / 10000000)) := by
  have h := reflection_log_6133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6134_neg : (46548867 / 500000000) ≤ -Real.log (1000000 / 1097569) ∧
    -Real.log (1000000 / 1097569) ≤ (18619547 / 200000000) := by
  have h := checkLog_sound (w := (97569 / 2097569)) (n := 12)
    (lo := (46548867 / 500000000)) (hi := (18619547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097569 / 1000000) = 1/(1000000 / 1097569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6134 : Bounds (46548867 / 500000000) (18619547 / 200000000) (Real.log (1097569 / 1000000)) := by
  have h := reflection_log_6134_neg
  have he : Real.log (1097569 / 1000000) = -Real.log (1000000 / 1097569) := by
    rw [show ((1097569 / 1000000) : ℝ) = ((1000000 / 1097569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6135_neg : (20532609 / 200000000) ≤ -Real.log (902431 / 1000000) ∧
    -Real.log (902431 / 1000000) ≤ (51331523 / 500000000) := by
  have h := checkLog_sound (w := (97569 / 1902431)) (n := 12)
    (lo := (20532609 / 200000000)) (hi := (51331523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902431) = 1/(902431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6135 : Bounds (-51331523 / 500000000) (-20532609 / 200000000) (Real.log (902431 / 1000000)) := by
  have h := reflection_log_6135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6136_neg : (93320929 / 1000000000) ≤ -Real.log (500000 / 548907) ∧
    -Real.log (500000 / 548907) ≤ (9332093 / 100000000) := by
  have h := checkLog_sound (w := (48907 / 1048907)) (n := 12)
    (lo := (93320929 / 1000000000)) (hi := (9332093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548907 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548907 / 500000) = 1/(500000 / 548907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6136 : Bounds (93320929 / 1000000000) (9332093 / 100000000) (Real.log (548907 / 500000)) := by
  have h := reflection_log_6136_neg
  have he : Real.log (548907 / 500000) = -Real.log (500000 / 548907) := by
    rw [show ((548907 / 500000) : ℝ) = ((500000 / 548907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6137_neg : (102934571 / 1000000000) ≤ -Real.log (451093 / 500000) ∧
    -Real.log (451093 / 500000) ≤ (25733643 / 250000000) := by
  have h := checkLog_sound (w := (48907 / 951093)) (n := 12)
    (lo := (102934571 / 1000000000)) (hi := (25733643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451093) = 1/(451093 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6137 : Bounds (-25733643 / 250000000) (-102934571 / 1000000000) (Real.log (451093 / 500000)) := by
  have h := reflection_log_6137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6138_neg : (9613641 / 1000000000) ≤ -Real.log (247608105351 / 250000000000) ∧
    -Real.log (247608105351 / 250000000000) ≤ (4806821 / 500000000) := by
  have h := checkLog_sound (w := (2391894649 / 497608105351)) (n := 12)
    (lo := (9613641 / 1000000000)) (hi := (4806821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247608105351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247608105351) = 1/(247608105351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6138 : Bounds (-4806821 / 500000000) (-9613641 / 1000000000) (Real.log (247608105351 / 250000000000)) := by
  have h := reflection_log_6138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6139_neg : (9565311 / 1000000000) ≤ -Real.log (990480290239 / 1000000000000) ∧
    -Real.log (990480290239 / 1000000000000) ≤ (74729 / 7812500) := by
  have h := checkLog_sound (w := (9519709761 / 1990480290239)) (n := 12)
    (lo := (9565311 / 1000000000)) (hi := (74729 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990480290239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990480290239) = 1/(990480290239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6139 : Bounds (-74729 / 7812500) (-9565311 / 1000000000) (Real.log (990480290239 / 1000000000000)) := by
  have h := reflection_log_6139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6140_neg : (9788039 / 50000000) ≤ -Real.log (500000000000 / 608117961373) ∧
    -Real.log (500000000000 / 608117961373) ≤ (195760781 / 1000000000) := by
  have h := checkLog_sound (w := (108117961373 / 1108117961373)) (n := 12)
    (lo := (9788039 / 50000000)) (hi := (195760781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608117961373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608117961373 / 500000000000) = 1/(500000000000 / 608117961373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6140 : Bounds (9788039 / 50000000) (195760781 / 1000000000) (Real.log (608117961373 / 500000000000)) := by
  have h := reflection_log_6140_neg
  have he : Real.log (608117961373 / 500000000000) = -Real.log (500000000000 / 608117961373) := by
    rw [show ((608117961373 / 500000000000) : ℝ) = ((500000000000 / 608117961373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6141_neg : (196255501 / 1000000000) ≤ -Real.log (250000000000 / 304209442399) ∧
    -Real.log (250000000000 / 304209442399) ≤ (98127751 / 500000000) := by
  have h := checkLog_sound (w := (54209442399 / 554209442399)) (n := 12)
    (lo := (196255501 / 1000000000)) (hi := (98127751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304209442399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304209442399 / 250000000000) = 1/(250000000000 / 304209442399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6141 : Bounds (196255501 / 1000000000) (98127751 / 500000000) (Real.log (304209442399 / 250000000000)) := by
  have h := reflection_log_6141_neg
  have he : Real.log (304209442399 / 250000000000) = -Real.log (250000000000 / 304209442399) := by
    rw [show ((304209442399 / 250000000000) : ℝ) = ((250000000000 / 304209442399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6142_neg : (392980551 / 1000000000) ≤ -Real.log (500000000000 / 740694789081) ∧
    -Real.log (500000000000 / 740694789081) ≤ (49122569 / 125000000) := by
  have h := checkLog_sound (w := (240694789081 / 1240694789081)) (n := 12)
    (lo := (392980551 / 1000000000)) (hi := (49122569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740694789081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740694789081 / 500000000000) = 1/(500000000000 / 740694789081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6142 : Bounds (392980551 / 1000000000) (49122569 / 125000000) (Real.log (740694789081 / 500000000000)) := by
  have h := reflection_log_6142_neg
  have he : Real.log (740694789081 / 500000000000) = -Real.log (500000000000 / 740694789081) := by
    rw [show ((740694789081 / 500000000000) : ℝ) = ((500000000000 / 740694789081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6143_neg : (393188377 / 1000000000) ≤ -Real.log (500000000000 / 740848740539) ∧
    -Real.log (500000000000 / 740848740539) ≤ (196594189 / 500000000) := by
  have h := checkLog_sound (w := (240848740539 / 1240848740539)) (n := 12)
    (lo := (393188377 / 1000000000)) (hi := (196594189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740848740539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740848740539 / 500000000000) = 1/(500000000000 / 740848740539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6143 : Bounds (393188377 / 1000000000) (196594189 / 500000000) (Real.log (740848740539 / 500000000000)) := by
  have h := reflection_log_6143_neg
  have he : Real.log (740848740539 / 500000000000) = -Real.log (500000000000 / 740848740539) := by
    rw [show ((740848740539 / 500000000000) : ℝ) = ((500000000000 / 740848740539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
