import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell064
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

theorem reflection_log_1_neg : (253157347 / 1000000000) ≤ -Real.log (1024 / 1319) ∧
    -Real.log (1024 / 1319) ≤ (63289337 / 250000000) := by
  have h := checkLog_sound (w := (295 / 2343)) (n := 12)
    (lo := (253157347 / 1000000000)) (hi := (63289337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1024) = 1/(1024 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253157347 / 1000000000) (63289337 / 250000000) (Real.log (1319 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1319 / 1024) = -Real.log (1024 / 1319) := by
    rw [show ((1319 / 1024) : ℝ) = ((1024 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (339798073 / 1000000000) ≤ -Real.log (729 / 1024) ∧
    -Real.log (729 / 1024) ≤ (169899037 / 500000000) := by
  have h := checkLog_sound (w := (295 / 1753)) (n := 12)
    (lo := (339798073 / 1000000000)) (hi := (169899037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 729) = 1/(729 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169899037 / 500000000) (-339798073 / 1000000000) (Real.log (729 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252702353 / 1000000000) ≤ -Real.log (80 / 103) ∧
    -Real.log (80 / 103) ≤ (126351177 / 500000000) := by
  have h := checkLog_sound (w := (23 / 183)) (n := 12)
    (lo := (252702353 / 1000000000)) (hi := (126351177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103 / 80) = 1/(80 / 103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252702353 / 1000000000) (126351177 / 500000000) (Real.log (103 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (103 / 80) = -Real.log (80 / 103) := by
    rw [show ((103 / 80) : ℝ) = ((80 / 103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (169487683 / 500000000) ≤ -Real.log (57 / 80) ∧
    -Real.log (57 / 80) ≤ (338975367 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 57) = 1/(57 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-338975367 / 1000000000) (-169487683 / 500000000) (Real.log (57 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23208037 / 125000000) ≤ -Real.log (500000 / 602009) ∧
    -Real.log (500000 / 602009) ≤ (185664297 / 1000000000) := by
  have h := checkLog_sound (w := (102009 / 1102009)) (n := 12)
    (lo := (23208037 / 125000000)) (hi := (185664297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602009 / 500000) = 1/(500000 / 602009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23208037 / 125000000) (185664297 / 1000000000) (Real.log (602009 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (602009 / 500000) = -Real.log (500000 / 602009) := by
    rw [show ((602009 / 500000) : ℝ) = ((500000 / 602009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114089353 / 500000000) ≤ -Real.log (397991 / 500000) ∧
    -Real.log (397991 / 500000) ≤ (228178707 / 1000000000) := by
  have h := checkLog_sound (w := (102009 / 897991)) (n := 12)
    (lo := (114089353 / 500000000)) (hi := (228178707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397991) = 1/(397991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-228178707 / 1000000000) (-114089353 / 500000000) (Real.log (397991 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46503267 / 250000000) ≤ -Real.log (500000 / 602219) ∧
    -Real.log (500000 / 602219) ≤ (186013069 / 1000000000) := by
  have h := checkLog_sound (w := (102219 / 1102219)) (n := 12)
    (lo := (46503267 / 250000000)) (hi := (186013069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602219 / 500000) = 1/(500000 / 602219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46503267 / 250000000) (186013069 / 1000000000) (Real.log (602219 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (602219 / 500000) = -Real.log (500000 / 602219) := by
    rw [show ((602219 / 500000) : ℝ) = ((500000 / 602219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45741299 / 200000000) ≤ -Real.log (397781 / 500000) ∧
    -Real.log (397781 / 500000) ≤ (3573539 / 15625000) := by
  have h := checkLog_sound (w := (102219 / 897781)) (n := 12)
    (lo := (45741299 / 200000000)) (hi := (3573539 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397781) = 1/(397781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3573539 / 15625000) (-45741299 / 200000000) (Real.log (397781 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4257203 / 31250000) ≤ -Real.log (500000 / 572973) ∧
    -Real.log (500000 / 572973) ≤ (136230497 / 1000000000) := by
  have h := checkLog_sound (w := (72973 / 1072973)) (n := 12)
    (lo := (4257203 / 31250000)) (hi := (136230497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572973 / 500000) = 1/(500000 / 572973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4257203 / 31250000) (136230497 / 1000000000) (Real.log (572973 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (572973 / 500000) = -Real.log (500000 / 572973) := by
    rw [show ((572973 / 500000) : ℝ) = ((500000 / 572973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31552171 / 200000000) ≤ -Real.log (427027 / 500000) ∧
    -Real.log (427027 / 500000) ≤ (19720107 / 125000000) := by
  have h := checkLog_sound (w := (72973 / 927027)) (n := 12)
    (lo := (31552171 / 200000000)) (hi := (19720107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427027) = 1/(427027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19720107 / 125000000) (-31552171 / 200000000) (Real.log (427027 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136498361 / 1000000000) ≤ -Real.log (1000000 / 1146253) ∧
    -Real.log (1000000 / 1146253) ≤ (68249181 / 500000000) := by
  have h := checkLog_sound (w := (146253 / 2146253)) (n := 12)
    (lo := (136498361 / 1000000000)) (hi := (68249181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146253 / 1000000) = 1/(1000000 / 1146253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136498361 / 1000000000) (68249181 / 500000000) (Real.log (1146253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1146253 / 1000000) = -Real.log (1000000 / 1146253) := by
    rw [show ((1146253 / 1000000) : ℝ) = ((1000000 / 1146253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79060191 / 500000000) ≤ -Real.log (853747 / 1000000) ∧
    -Real.log (853747 / 1000000) ≤ (158120383 / 1000000000) := by
  have h := checkLog_sound (w := (146253 / 1853747)) (n := 12)
    (lo := (79060191 / 500000000)) (hi := (158120383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853747) = 1/(853747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-158120383 / 1000000000) (-79060191 / 500000000) (Real.log (853747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14791943 / 25000000) ≤ -Real.log (500000000000 / 903508771929) ∧
    -Real.log (500000000000 / 903508771929) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (403508771929 / 1403508771929)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903508771929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903508771929 / 500000000000) = 1/(500000000000 / 903508771929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (903508771929 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (903508771929 / 500000000000) = -Real.log (500000000000 / 903508771929) := by
    rw [show ((903508771929 / 500000000000) : ℝ) = ((500000000000 / 903508771929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29647771 / 50000000) ≤ -Real.log (500000000000 / 904663923183) ∧
    -Real.log (500000000000 / 904663923183) ≤ (592955421 / 1000000000) := by
  have h := checkLog_sound (w := (404663923183 / 1404663923183)) (n := 12)
    (lo := (29647771 / 50000000)) (hi := (592955421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904663923183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904663923183 / 500000000000) = 1/(500000000000 / 904663923183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (29647771 / 50000000) (592955421 / 1000000000) (Real.log (904663923183 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (904663923183 / 500000000000) = -Real.log (500000000000 / 904663923183) := by
    rw [show ((904663923183 / 500000000000) : ℝ) = ((500000000000 / 904663923183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (413843003 / 1000000000) ≤ -Real.log (500000000000 / 756309816051) ∧
    -Real.log (500000000000 / 756309816051) ≤ (103460751 / 250000000) := by
  have h := checkLog_sound (w := (256309816051 / 1256309816051)) (n := 12)
    (lo := (413843003 / 1000000000)) (hi := (103460751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756309816051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756309816051 / 500000000000) = 1/(500000000000 / 756309816051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (413843003 / 1000000000) (103460751 / 250000000) (Real.log (756309816051 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (756309816051 / 500000000000) = -Real.log (500000000000 / 756309816051) := by
    rw [show ((756309816051 / 500000000000) : ℝ) = ((500000000000 / 756309816051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (414719563 / 1000000000) ≤ -Real.log (12500000000 / 18924326451) ∧
    -Real.log (12500000000 / 18924326451) ≤ (103679891 / 250000000) := by
  have h := checkLog_sound (w := (6424326451 / 31424326451)) (n := 12)
    (lo := (414719563 / 1000000000)) (hi := (103679891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18924326451 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18924326451 / 12500000000) = 1/(12500000000 / 18924326451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (414719563 / 1000000000) (103679891 / 250000000) (Real.log (18924326451 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (18924326451 / 12500000000) = -Real.log (12500000000 / 18924326451) := by
    rw [show ((18924326451 / 12500000000) : ℝ) = ((12500000000 / 18924326451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (36748919 / 125000000) ≤ -Real.log (62500000000 / 83860768757) ∧
    -Real.log (62500000000 / 83860768757) ≤ (293991353 / 1000000000) := by
  have h := checkLog_sound (w := (21360768757 / 146360768757)) (n := 12)
    (lo := (36748919 / 125000000)) (hi := (293991353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83860768757 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83860768757 / 62500000000) = 1/(62500000000 / 83860768757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36748919 / 125000000) (293991353 / 1000000000) (Real.log (83860768757 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (83860768757 / 62500000000) = -Real.log (62500000000 / 83860768757) := by
    rw [show ((83860768757 / 62500000000) : ℝ) = ((62500000000 / 83860768757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (294618743 / 1000000000) ≤ -Real.log (250000000000 / 335653595269) ∧
    -Real.log (250000000000 / 335653595269) ≤ (36827343 / 125000000) := by
  have h := checkLog_sound (w := (85653595269 / 585653595269)) (n := 12)
    (lo := (294618743 / 1000000000)) (hi := (36827343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335653595269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335653595269 / 250000000000) = 1/(250000000000 / 335653595269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (294618743 / 1000000000) (36827343 / 125000000) (Real.log (335653595269 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335653595269 / 250000000000) = -Real.log (250000000000 / 335653595269) := by
    rw [show ((335653595269 / 250000000000) : ℝ) = ((250000000000 / 335653595269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1081101 / 50000000) ≤ -Real.log (978610059991 / 1000000000000) ∧
    -Real.log (978610059991 / 1000000000000) ≤ (21622021 / 1000000000) := by
  have h := checkLog_sound (w := (21389940009 / 1978610059991)) (n := 12)
    (lo := (1081101 / 50000000)) (hi := (21622021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978610059991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978610059991) = 1/(978610059991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21622021 / 1000000000) (-1081101 / 50000000) (Real.log (978610059991 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10765179 / 500000000) ≤ -Real.log (244674941271 / 250000000000) ∧
    -Real.log (244674941271 / 250000000000) ≤ (21530359 / 1000000000) := by
  have h := checkLog_sound (w := (5325058729 / 494674941271)) (n := 12)
    (lo := (10765179 / 500000000)) (hi := (21530359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244674941271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244674941271) = 1/(244674941271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21530359 / 1000000000) (-10765179 / 500000000) (Real.log (244674941271 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell064
