import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell222
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

theorem reflection_log_1_neg : (80641147 / 250000000) ≤ -Real.log (5120 / 7069) ∧
    -Real.log (5120 / 7069) ≤ (322564589 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 12189)) (n := 12)
    (lo := (80641147 / 250000000)) (hi := (322564589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7069 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7069 / 5120) = 1/(5120 / 7069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80641147 / 250000000) (322564589 / 1000000000) (Real.log (7069 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7069 / 5120) = -Real.log (5120 / 7069) := by
    rw [show ((7069 / 5120) : ℝ) = ((5120 / 7069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (479107443 / 1000000000) ≤ -Real.log (3171 / 5120) ∧
    -Real.log (3171 / 5120) ≤ (119776861 / 250000000) := by
  have h := checkLog_sound (w := (1949 / 8291)) (n := 12)
    (lo := (479107443 / 1000000000)) (hi := (119776861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3171) = 1/(3171 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-119776861 / 250000000) (-479107443 / 1000000000) (Real.log (3171 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (322140109 / 1000000000) ≤ -Real.log (2560 / 3533) ∧
    -Real.log (2560 / 3533) ≤ (32214011 / 100000000) := by
  have h := checkLog_sound (w := (973 / 6093)) (n := 12)
    (lo := (322140109 / 1000000000)) (hi := (32214011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3533 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3533 / 2560) = 1/(2560 / 3533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (322140109 / 1000000000) (32214011 / 100000000) (Real.log (3533 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3533 / 2560) = -Real.log (2560 / 3533) := by
    rw [show ((3533 / 2560) : ℝ) = ((2560 / 3533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (59770227 / 125000000) ≤ -Real.log (1587 / 2560) ∧
    -Real.log (1587 / 2560) ≤ (478161817 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 4147)) (n := 12)
    (lo := (59770227 / 125000000)) (hi := (478161817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1587) = 1/(1587 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-478161817 / 1000000000) (-59770227 / 125000000) (Real.log (1587 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239393207 / 1000000000) ≤ -Real.log (500000 / 635239) ∧
    -Real.log (500000 / 635239) ≤ (29924151 / 125000000) := by
  have h := checkLog_sound (w := (135239 / 1135239)) (n := 12)
    (lo := (239393207 / 1000000000)) (hi := (29924151 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635239 / 500000) = 1/(500000 / 635239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239393207 / 1000000000) (29924151 / 125000000) (Real.log (635239 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (635239 / 500000) = -Real.log (500000 / 635239) := by
    rw [show ((635239 / 500000) : ℝ) = ((500000 / 635239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (315365753 / 1000000000) ≤ -Real.log (364761 / 500000) ∧
    -Real.log (364761 / 500000) ≤ (157682877 / 500000000) := by
  have h := checkLog_sound (w := (135239 / 864761)) (n := 12)
    (lo := (315365753 / 1000000000)) (hi := (157682877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364761) = 1/(364761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-157682877 / 500000000) (-315365753 / 1000000000) (Real.log (364761 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59931721 / 250000000) ≤ -Real.log (500000 / 635451) ∧
    -Real.log (500000 / 635451) ≤ (47945377 / 200000000) := by
  have h := checkLog_sound (w := (135451 / 1135451)) (n := 12)
    (lo := (59931721 / 250000000)) (hi := (47945377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635451 / 500000) = 1/(500000 / 635451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59931721 / 250000000) (47945377 / 200000000) (Real.log (635451 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (635451 / 500000) = -Real.log (500000 / 635451) := by
    rw [show ((635451 / 500000) : ℝ) = ((500000 / 635451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2527577 / 8000000) ≤ -Real.log (364549 / 500000) ∧
    -Real.log (364549 / 500000) ≤ (157973563 / 500000000) := by
  have h := checkLog_sound (w := (135451 / 864549)) (n := 12)
    (lo := (2527577 / 8000000)) (hi := (157973563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364549) = 1/(364549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-157973563 / 500000000) (-2527577 / 8000000) (Real.log (364549 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7132943 / 40000000) ≤ -Real.log (250000 / 298803) ∧
    -Real.log (250000 / 298803) ≤ (22290447 / 125000000) := by
  have h := checkLog_sound (w := (48803 / 548803)) (n := 12)
    (lo := (7132943 / 40000000)) (hi := (22290447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298803 / 250000) = 1/(250000 / 298803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7132943 / 40000000) (22290447 / 125000000) (Real.log (298803 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (298803 / 250000) = -Real.log (250000 / 298803) := by
    rw [show ((298803 / 250000) : ℝ) = ((250000 / 298803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21717639 / 100000000) ≤ -Real.log (201197 / 250000) ∧
    -Real.log (201197 / 250000) ≤ (217176391 / 1000000000) := by
  have h := checkLog_sound (w := (48803 / 451197)) (n := 12)
    (lo := (21717639 / 100000000)) (hi := (217176391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201197) = 1/(201197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-217176391 / 1000000000) (-21717639 / 100000000) (Real.log (201197 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89295219 / 500000000) ≤ -Real.log (1000000 / 1195531) ∧
    -Real.log (1000000 / 1195531) ≤ (178590439 / 1000000000) := by
  have h := checkLog_sound (w := (195531 / 2195531)) (n := 12)
    (lo := (89295219 / 500000000)) (hi := (178590439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195531 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195531 / 1000000) = 1/(1000000 / 1195531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89295219 / 500000000) (178590439 / 1000000000) (Real.log (1195531 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195531 / 1000000) = -Real.log (1000000 / 1195531) := by
    rw [show ((1195531 / 1000000) : ℝ) = ((1000000 / 1195531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (108786423 / 500000000) ≤ -Real.log (804469 / 1000000) ∧
    -Real.log (804469 / 1000000) ≤ (217572847 / 1000000000) := by
  have h := checkLog_sound (w := (195531 / 1804469)) (n := 12)
    (lo := (108786423 / 500000000)) (hi := (217572847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804469) = 1/(804469 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217572847 / 1000000000) (-108786423 / 500000000) (Real.log (804469 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (400150963 / 500000000) ≤ -Real.log (500000000000 / 1113106490233) ∧
    -Real.log (500000000000 / 1113106490233) ≤ (100037741 / 125000000) := by
  have h := checkLog_sound (w := (113106490233 / 2113106490233)) (n := 12)
    (lo := (53577373 / 500000000)) (hi := (107154747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113106490233 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1113106490233 / 1000000000000) = 1/(500000000000 / 1113106490233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (400150963 / 500000000) (100037741 / 125000000) (Real.log (1113106490233 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1113106490233 / 500000000000) = -Real.log (500000000000 / 1113106490233) := by
    rw [show ((1113106490233 / 500000000000) : ℝ) = ((500000000000 / 1113106490233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (801672031 / 1000000000) ≤ -Real.log (500000000000 / 1114632608011) ∧
    -Real.log (500000000000 / 1114632608011) ≤ (801672033 / 1000000000) := by
  have h := checkLog_sound (w := (114632608011 / 2114632608011)) (n := 12)
    (lo := (108524851 / 1000000000)) (hi := (27131213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1114632608011 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1114632608011 / 1000000000000) = 1/(500000000000 / 1114632608011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (801672031 / 1000000000) (801672033 / 1000000000) (Real.log (1114632608011 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1114632608011 / 500000000000) = -Real.log (500000000000 / 1114632608011) := by
    rw [show ((1114632608011 / 500000000000) : ℝ) = ((500000000000 / 1114632608011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (554758961 / 1000000000) ≤ -Real.log (100000000000 / 174152116043) ∧
    -Real.log (100000000000 / 174152116043) ≤ (277379481 / 500000000) := by
  have h := checkLog_sound (w := (74152116043 / 274152116043)) (n := 12)
    (lo := (554758961 / 1000000000)) (hi := (277379481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174152116043 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174152116043 / 100000000000) = 1/(100000000000 / 174152116043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (554758961 / 1000000000) (277379481 / 500000000) (Real.log (174152116043 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (174152116043 / 100000000000) = -Real.log (100000000000 / 174152116043) := by
    rw [show ((174152116043 / 100000000000) : ℝ) = ((100000000000 / 174152116043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (555674009 / 1000000000) ≤ -Real.log (25000000000 / 43577886649) ∧
    -Real.log (25000000000 / 43577886649) ≤ (55567401 / 100000000) := by
  have h := checkLog_sound (w := (18577886649 / 68577886649)) (n := 12)
    (lo := (555674009 / 1000000000)) (hi := (55567401 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43577886649 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43577886649 / 25000000000) = 1/(25000000000 / 43577886649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (555674009 / 1000000000) (55567401 / 100000000) (Real.log (43577886649 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (43577886649 / 25000000000) = -Real.log (25000000000 / 43577886649) := by
    rw [show ((43577886649 / 25000000000) : ℝ) = ((25000000000 / 43577886649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79099993 / 200000000) ≤ -Real.log (100000000000 / 148512651779) ∧
    -Real.log (100000000000 / 148512651779) ≤ (197749983 / 500000000) := by
  have h := checkLog_sound (w := (48512651779 / 248512651779)) (n := 12)
    (lo := (79099993 / 200000000)) (hi := (197749983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148512651779 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148512651779 / 100000000000) = 1/(100000000000 / 148512651779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79099993 / 200000000) (197749983 / 500000000) (Real.log (148512651779 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (148512651779 / 100000000000) = -Real.log (100000000000 / 148512651779) := by
    rw [show ((148512651779 / 100000000000) : ℝ) = ((100000000000 / 148512651779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (99040821 / 250000000) ≤ -Real.log (25000000000 / 37152798927) ∧
    -Real.log (25000000000 / 37152798927) ≤ (79232657 / 200000000) := by
  have h := checkLog_sound (w := (12152798927 / 62152798927)) (n := 12)
    (lo := (99040821 / 250000000)) (hi := (79232657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37152798927 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37152798927 / 25000000000) = 1/(25000000000 / 37152798927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (99040821 / 250000000) (79232657 / 200000000) (Real.log (37152798927 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37152798927 / 25000000000) = -Real.log (25000000000 / 37152798927) := by
    rw [show ((37152798927 / 25000000000) : ℝ) = ((25000000000 / 37152798927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4872801 / 125000000) ≤ -Real.log (961767628039 / 1000000000000) ∧
    -Real.log (961767628039 / 1000000000000) ≤ (38982409 / 1000000000) := by
  have h := checkLog_sound (w := (38232371961 / 1961767628039)) (n := 12)
    (lo := (4872801 / 125000000)) (hi := (38982409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961767628039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961767628039) = 1/(961767628039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38982409 / 1000000000) (-4872801 / 125000000) (Real.log (961767628039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19426407 / 500000000) ≤ -Real.log (60118267191 / 62500000000) ∧
    -Real.log (60118267191 / 62500000000) ≤ (7770563 / 200000000) := by
  have h := checkLog_sound (w := (2381732809 / 122618267191)) (n := 12)
    (lo := (19426407 / 500000000)) (hi := (7770563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60118267191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60118267191) = 1/(60118267191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7770563 / 200000000) (-19426407 / 500000000) (Real.log (60118267191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell222
