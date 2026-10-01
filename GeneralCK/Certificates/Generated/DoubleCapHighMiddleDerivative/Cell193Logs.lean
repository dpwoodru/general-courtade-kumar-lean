import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell193
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

theorem reflection_log_1_neg : (310180969 / 1000000000) ≤ -Real.log (2560 / 3491) ∧
    -Real.log (2560 / 3491) ≤ (31018097 / 100000000) := by
  have h := checkLog_sound (w := (931 / 6051)) (n := 12)
    (lo := (310180969 / 1000000000)) (hi := (31018097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3491 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3491 / 2560) = 1/(2560 / 3491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (310180969 / 1000000000) (31018097 / 100000000) (Real.log (3491 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3491 / 2560) = -Real.log (2560 / 3491) := by
    rw [show ((3491 / 2560) : ℝ) = ((2560 / 3491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (14126279 / 31250000) ≤ -Real.log (1629 / 2560) ∧
    -Real.log (1629 / 2560) ≤ (452040929 / 1000000000) := by
  have h := checkLog_sound (w := (931 / 4189)) (n := 12)
    (lo := (14126279 / 31250000)) (hi := (452040929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1629) = 1/(1629 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-452040929 / 1000000000) (-14126279 / 31250000) (Real.log (1629 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (387189 / 1250000) ≤ -Real.log (5120 / 6979) ∧
    -Real.log (5120 / 6979) ≤ (309751201 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 12099)) (n := 12)
    (lo := (387189 / 1250000)) (hi := (309751201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6979 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6979 / 5120) = 1/(5120 / 6979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (387189 / 1250000) (309751201 / 1000000000) (Real.log (6979 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6979 / 5120) = -Real.log (5120 / 6979) := by
    rw [show ((6979 / 5120) : ℝ) = ((5120 / 6979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (225560271 / 500000000) ≤ -Real.log (3261 / 5120) ∧
    -Real.log (3261 / 5120) ≤ (451120543 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 8381)) (n := 12)
    (lo := (225560271 / 500000000)) (hi := (451120543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3261) = 1/(3261 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-451120543 / 1000000000) (-225560271 / 500000000) (Real.log (3261 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45941671 / 200000000) ≤ -Real.log (1000000 / 1258233) ∧
    -Real.log (1000000 / 1258233) ≤ (57427089 / 250000000) := by
  have h := checkLog_sound (w := (258233 / 2258233)) (n := 12)
    (lo := (45941671 / 200000000)) (hi := (57427089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258233 / 1000000) = 1/(1000000 / 1258233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45941671 / 200000000) (57427089 / 250000000) (Real.log (1258233 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1258233 / 1000000) = -Real.log (1000000 / 1258233) := by
    rw [show ((1258233 / 1000000) : ℝ) = ((1000000 / 1258233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298720101 / 1000000000) ≤ -Real.log (741767 / 1000000) ∧
    -Real.log (741767 / 1000000) ≤ (149360051 / 500000000) := by
  have h := checkLog_sound (w := (258233 / 1741767)) (n := 12)
    (lo := (298720101 / 1000000000)) (hi := (149360051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741767) = 1/(741767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149360051 / 500000000) (-298720101 / 1000000000) (Real.log (741767 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46008897 / 200000000) ≤ -Real.log (31250 / 39333) ∧
    -Real.log (31250 / 39333) ≤ (115022243 / 500000000) := by
  have h := checkLog_sound (w := (8083 / 70583)) (n := 12)
    (lo := (46008897 / 200000000)) (hi := (115022243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39333 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39333 / 31250) = 1/(31250 / 39333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46008897 / 200000000) (115022243 / 500000000) (Real.log (39333 / 31250)) := by
  have h := reflection_log_7_neg
  have he : Real.log (39333 / 31250) = -Real.log (31250 / 39333) := by
    rw [show ((39333 / 31250) : ℝ) = ((31250 / 39333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (299290523 / 1000000000) ≤ -Real.log (23167 / 31250) ∧
    -Real.log (23167 / 31250) ≤ (74822631 / 250000000) := by
  have h := checkLog_sound (w := (8083 / 54417)) (n := 12)
    (lo := (299290523 / 1000000000)) (hi := (74822631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23167) = 1/(23167 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-74822631 / 250000000) (-299290523 / 1000000000) (Real.log (23167 / 31250)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170615811 / 1000000000) ≤ -Real.log (200000 / 237207) ∧
    -Real.log (200000 / 237207) ≤ (42653953 / 250000000) := by
  have h := checkLog_sound (w := (37207 / 437207)) (n := 12)
    (lo := (170615811 / 1000000000)) (hi := (42653953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237207 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237207 / 200000) = 1/(200000 / 237207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170615811 / 1000000000) (42653953 / 250000000) (Real.log (237207 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (237207 / 200000) = -Real.log (200000 / 237207) := by
    rw [show ((237207 / 200000) : ℝ) = ((200000 / 237207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (205837911 / 1000000000) ≤ -Real.log (162793 / 200000) ∧
    -Real.log (162793 / 200000) ≤ (25729739 / 125000000) := by
  have h := checkLog_sound (w := (37207 / 362793)) (n := 12)
    (lo := (205837911 / 1000000000)) (hi := (25729739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162793) = 1/(162793 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25729739 / 125000000) (-205837911 / 1000000000) (Real.log (162793 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170882209 / 1000000000) ≤ -Real.log (1000000 / 1186351) ∧
    -Real.log (1000000 / 1186351) ≤ (17088221 / 100000000) := by
  have h := checkLog_sound (w := (186351 / 2186351)) (n := 12)
    (lo := (170882209 / 1000000000)) (hi := (17088221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186351 / 1000000) = 1/(1000000 / 1186351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170882209 / 1000000000) (17088221 / 100000000) (Real.log (1186351 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1186351 / 1000000) = -Real.log (1000000 / 1186351) := by
    rw [show ((1186351 / 1000000) : ℝ) = ((1000000 / 1186351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (206226209 / 1000000000) ≤ -Real.log (813649 / 1000000) ∧
    -Real.log (813649 / 1000000) ≤ (20622621 / 100000000) := by
  have h := checkLog_sound (w := (186351 / 1813649)) (n := 12)
    (lo := (206226209 / 1000000000)) (hi := (20622621 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813649) = 1/(813649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20622621 / 100000000) (-206226209 / 1000000000) (Real.log (813649 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (380435871 / 500000000) ≤ -Real.log (31250000000 / 66879408157) ∧
    -Real.log (31250000000 / 66879408157) ≤ (11888621 / 15625000) := by
  have h := checkLog_sound (w := (4379408157 / 129379408157)) (n := 12)
    (lo := (33862281 / 500000000)) (hi := (67724563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66879408157 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66879408157 / 62500000000) = 1/(31250000000 / 66879408157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (380435871 / 500000000) (11888621 / 15625000) (Real.log (66879408157 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66879408157 / 31250000000) = -Real.log (31250000000 / 66879408157) := by
    rw [show ((66879408157 / 31250000000) : ℝ) = ((31250000000 / 66879408157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (762221897 / 1000000000) ≤ -Real.log (500000000000 / 1071516267649) ∧
    -Real.log (500000000000 / 1071516267649) ≤ (762221899 / 1000000000) := by
  have h := checkLog_sound (w := (71516267649 / 2071516267649)) (n := 12)
    (lo := (69074717 / 1000000000)) (hi := (34537359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1071516267649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1071516267649 / 1000000000000) = 1/(500000000000 / 1071516267649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (762221897 / 1000000000) (762221899 / 1000000000) (Real.log (1071516267649 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1071516267649 / 500000000000) = -Real.log (500000000000 / 1071516267649) := by
    rw [show ((1071516267649 / 500000000000) : ℝ) = ((500000000000 / 1071516267649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (528428457 / 1000000000) ≤ -Real.log (500000000000 / 848132230201) ∧
    -Real.log (500000000000 / 848132230201) ≤ (264214229 / 500000000) := by
  have h := checkLog_sound (w := (348132230201 / 1348132230201)) (n := 12)
    (lo := (528428457 / 1000000000)) (hi := (264214229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848132230201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848132230201 / 500000000000) = 1/(500000000000 / 848132230201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (528428457 / 1000000000) (264214229 / 500000000) (Real.log (848132230201 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (848132230201 / 500000000000) = -Real.log (500000000000 / 848132230201) := by
    rw [show ((848132230201 / 500000000000) : ℝ) = ((500000000000 / 848132230201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16541719 / 31250000) ≤ -Real.log (7812500000 / 13264085229) ∧
    -Real.log (7812500000 / 13264085229) ≤ (529335009 / 1000000000) := by
  have h := checkLog_sound (w := (5451585229 / 21076585229)) (n := 12)
    (lo := (16541719 / 31250000)) (hi := (529335009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13264085229 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13264085229 / 7812500000) = 1/(7812500000 / 13264085229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (16541719 / 31250000) (529335009 / 1000000000) (Real.log (13264085229 / 7812500000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (13264085229 / 7812500000) = -Real.log (7812500000 / 13264085229) := by
    rw [show ((13264085229 / 7812500000) : ℝ) = ((7812500000 / 13264085229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (188226861 / 500000000) ≤ -Real.log (250000000000 / 364277026653) ∧
    -Real.log (250000000000 / 364277026653) ≤ (376453723 / 1000000000) := by
  have h := checkLog_sound (w := (114277026653 / 614277026653)) (n := 12)
    (lo := (188226861 / 500000000)) (hi := (376453723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364277026653 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364277026653 / 250000000000) = 1/(250000000000 / 364277026653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188226861 / 500000000) (376453723 / 1000000000) (Real.log (364277026653 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (364277026653 / 250000000000) = -Real.log (250000000000 / 364277026653) := by
    rw [show ((364277026653 / 250000000000) : ℝ) = ((250000000000 / 364277026653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (377108419 / 1000000000) ≤ -Real.log (500000000000 / 729031191583) ∧
    -Real.log (500000000000 / 729031191583) ≤ (18855421 / 50000000) := by
  have h := checkLog_sound (w := (229031191583 / 1229031191583)) (n := 12)
    (lo := (377108419 / 1000000000)) (hi := (18855421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729031191583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729031191583 / 500000000000) = 1/(500000000000 / 729031191583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (377108419 / 1000000000) (18855421 / 50000000) (Real.log (729031191583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (729031191583 / 500000000000) = -Real.log (500000000000 / 729031191583) := by
    rw [show ((729031191583 / 500000000000) : ℝ) = ((500000000000 / 729031191583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2209 / 62500) ≤ -Real.log (965273304799 / 1000000000000) ∧
    -Real.log (965273304799 / 1000000000000) ≤ (35344001 / 1000000000) := by
  have h := checkLog_sound (w := (34726695201 / 1965273304799)) (n := 12)
    (lo := (2209 / 62500)) (hi := (35344001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965273304799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965273304799) = 1/(965273304799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-35344001 / 1000000000) (-2209 / 62500) (Real.log (965273304799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (352221 / 10000000) ≤ -Real.log (38615639151 / 40000000000) ∧
    -Real.log (38615639151 / 40000000000) ≤ (35222101 / 1000000000) := by
  have h := checkLog_sound (w := (1384360849 / 78615639151)) (n := 12)
    (lo := (352221 / 10000000)) (hi := (35222101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38615639151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38615639151) = 1/(38615639151 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35222101 / 1000000000) (-352221 / 10000000) (Real.log (38615639151 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell193
