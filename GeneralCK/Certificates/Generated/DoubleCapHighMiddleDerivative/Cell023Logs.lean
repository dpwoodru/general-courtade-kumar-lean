import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell023
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

theorem reflection_log_1_neg : (11716537 / 50000000) ≤ -Real.log (640 / 809) ∧
    -Real.log (640 / 809) ≤ (234330741 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1449)) (n := 12)
    (lo := (11716537 / 50000000)) (hi := (234330741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809 / 640) = 1/(640 / 809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11716537 / 50000000) (234330741 / 1000000000) (Real.log (809 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (809 / 640) = -Real.log (640 / 809) := by
    rw [show ((809 / 640) : ℝ) = ((640 / 809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (153305041 / 500000000) ≤ -Real.log (471 / 640) ∧
    -Real.log (471 / 640) ≤ (306610083 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 1111)) (n := 12)
    (lo := (153305041 / 500000000)) (hi := (306610083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 471) = 1/(471 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-306610083 / 1000000000) (-153305041 / 500000000) (Real.log (471 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116933549 / 500000000) ≤ -Real.log (5120 / 6469) ∧
    -Real.log (5120 / 6469) ≤ (233867099 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 11589)) (n := 12)
    (lo := (116933549 / 500000000)) (hi := (233867099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6469 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6469 / 5120) = 1/(5120 / 6469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116933549 / 500000000) (233867099 / 1000000000) (Real.log (6469 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6469 / 5120) = -Real.log (5120 / 6469) := by
    rw [show ((6469 / 5120) : ℝ) = ((5120 / 6469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15290711 / 50000000) ≤ -Real.log (3771 / 5120) ∧
    -Real.log (3771 / 5120) ≤ (305814221 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 8891)) (n := 12)
    (lo := (15290711 / 50000000)) (hi := (305814221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3771) = 1/(3771 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-305814221 / 1000000000) (-15290711 / 50000000) (Real.log (3771 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42827791 / 250000000) ≤ -Real.log (50000 / 59343) ∧
    -Real.log (50000 / 59343) ≤ (34262233 / 200000000) := by
  have h := checkLog_sound (w := (9343 / 109343)) (n := 12)
    (lo := (42827791 / 250000000)) (hi := (34262233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59343 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59343 / 50000) = 1/(50000 / 59343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42827791 / 250000000) (34262233 / 200000000) (Real.log (59343 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (59343 / 50000) = -Real.log (50000 / 59343) := by
    rw [show ((59343 / 50000) : ℝ) = ((50000 / 59343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103425991 / 500000000) ≤ -Real.log (40657 / 50000) ∧
    -Real.log (40657 / 50000) ≤ (206851983 / 1000000000) := by
  have h := checkLog_sound (w := (9343 / 90657)) (n := 12)
    (lo := (103425991 / 500000000)) (hi := (206851983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40657) = 1/(40657 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-206851983 / 1000000000) (-103425991 / 500000000) (Real.log (40657 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10729061 / 62500000) ≤ -Real.log (12500 / 14841) ∧
    -Real.log (12500 / 14841) ≤ (171664977 / 1000000000) := by
  have h := checkLog_sound (w := (2341 / 27341)) (n := 12)
    (lo := (10729061 / 62500000)) (hi := (171664977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14841 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14841 / 12500) = 1/(12500 / 14841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10729061 / 62500000) (171664977 / 1000000000) (Real.log (14841 / 12500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14841 / 12500) = -Real.log (12500 / 14841) := by
    rw [show ((14841 / 12500) : ℝ) = ((12500 / 14841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25921079 / 125000000) ≤ -Real.log (10159 / 12500) ∧
    -Real.log (10159 / 12500) ≤ (207368633 / 1000000000) := by
  have h := checkLog_sound (w := (2341 / 22659)) (n := 12)
    (lo := (25921079 / 125000000)) (hi := (207368633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10159) = 1/(10159 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-207368633 / 1000000000) (-25921079 / 125000000) (Real.log (10159 / 12500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31310123 / 250000000) ≤ -Real.log (1000000 / 1133421) ∧
    -Real.log (1000000 / 1133421) ≤ (125240493 / 1000000000) := by
  have h := checkLog_sound (w := (133421 / 2133421)) (n := 12)
    (lo := (31310123 / 250000000)) (hi := (125240493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133421 / 1000000) = 1/(1000000 / 1133421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31310123 / 250000000) (125240493 / 1000000000) (Real.log (1133421 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1133421 / 1000000) = -Real.log (1000000 / 1133421) := by
    rw [show ((1133421 / 1000000) : ℝ) = ((1000000 / 1133421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (71601001 / 500000000) ≤ -Real.log (866579 / 1000000) ∧
    -Real.log (866579 / 1000000) ≤ (143202003 / 1000000000) := by
  have h := checkLog_sound (w := (133421 / 1866579)) (n := 12)
    (lo := (71601001 / 500000000)) (hi := (143202003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866579) = 1/(866579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-143202003 / 1000000000) (-71601001 / 500000000) (Real.log (866579 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25102087 / 200000000) ≤ -Real.log (1000000 / 1133727) ∧
    -Real.log (1000000 / 1133727) ≤ (31377609 / 250000000) := by
  have h := checkLog_sound (w := (133727 / 2133727)) (n := 12)
    (lo := (25102087 / 200000000)) (hi := (31377609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133727 / 1000000) = 1/(1000000 / 1133727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25102087 / 200000000) (31377609 / 250000000) (Real.log (1133727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1133727 / 1000000) = -Real.log (1000000 / 1133727) := by
    rw [show ((1133727 / 1000000) : ℝ) = ((1000000 / 1133727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (143555177 / 1000000000) ≤ -Real.log (866273 / 1000000) ∧
    -Real.log (866273 / 1000000) ≤ (71777589 / 500000000) := by
  have h := checkLog_sound (w := (133727 / 1866273)) (n := 12)
    (lo := (143555177 / 1000000000)) (hi := (71777589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866273) = 1/(866273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-71777589 / 500000000) (-143555177 / 1000000000) (Real.log (866273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (269840659 / 500000000) ≤ -Real.log (12500000000 / 21443251127) ∧
    -Real.log (12500000000 / 21443251127) ≤ (539681319 / 1000000000) := by
  have h := checkLog_sound (w := (8943251127 / 33943251127)) (n := 12)
    (lo := (269840659 / 500000000)) (hi := (539681319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21443251127 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21443251127 / 12500000000) = 1/(12500000000 / 21443251127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (269840659 / 500000000) (539681319 / 1000000000) (Real.log (21443251127 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (21443251127 / 12500000000) = -Real.log (12500000000 / 21443251127) := by
    rw [show ((21443251127 / 12500000000) : ℝ) = ((12500000000 / 21443251127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (540940823 / 1000000000) ≤ -Real.log (25000000000 / 42940552017) ∧
    -Real.log (25000000000 / 42940552017) ≤ (67617603 / 125000000) := by
  have h := checkLog_sound (w := (17940552017 / 67940552017)) (n := 12)
    (lo := (540940823 / 1000000000)) (hi := (67617603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42940552017 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42940552017 / 25000000000) = 1/(25000000000 / 42940552017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (540940823 / 1000000000) (67617603 / 125000000) (Real.log (42940552017 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42940552017 / 25000000000) = -Real.log (25000000000 / 42940552017) := by
    rw [show ((42940552017 / 25000000000) : ℝ) = ((25000000000 / 42940552017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (189081573 / 500000000) ≤ -Real.log (250000000000 / 364900263177) ∧
    -Real.log (250000000000 / 364900263177) ≤ (378163147 / 1000000000) := by
  have h := checkLog_sound (w := (114900263177 / 614900263177)) (n := 12)
    (lo := (189081573 / 500000000)) (hi := (378163147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364900263177 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364900263177 / 250000000000) = 1/(250000000000 / 364900263177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (189081573 / 500000000) (378163147 / 1000000000) (Real.log (364900263177 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (364900263177 / 250000000000) = -Real.log (250000000000 / 364900263177) := by
    rw [show ((364900263177 / 250000000000) : ℝ) = ((250000000000 / 364900263177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (47379201 / 125000000) ≤ -Real.log (250000000000 / 365218033271) ∧
    -Real.log (250000000000 / 365218033271) ≤ (379033609 / 1000000000) := by
  have h := checkLog_sound (w := (115218033271 / 615218033271)) (n := 12)
    (lo := (47379201 / 125000000)) (hi := (379033609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365218033271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365218033271 / 250000000000) = 1/(250000000000 / 365218033271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (47379201 / 125000000) (379033609 / 1000000000) (Real.log (365218033271 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (365218033271 / 250000000000) = -Real.log (250000000000 / 365218033271) := by
    rw [show ((365218033271 / 250000000000) : ℝ) = ((250000000000 / 365218033271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (53688499 / 200000000) ≤ -Real.log (500000000000 / 653962881629) ∧
    -Real.log (500000000000 / 653962881629) ≤ (2097207 / 7812500) := by
  have h := checkLog_sound (w := (153962881629 / 1153962881629)) (n := 12)
    (lo := (53688499 / 200000000)) (hi := (2097207 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653962881629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653962881629 / 500000000000) = 1/(500000000000 / 653962881629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (53688499 / 200000000) (2097207 / 7812500) (Real.log (653962881629 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (653962881629 / 500000000000) = -Real.log (500000000000 / 653962881629) := by
    rw [show ((653962881629 / 500000000000) : ℝ) = ((500000000000 / 653962881629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (269065613 / 1000000000) ≤ -Real.log (500000000000 / 654370504449) ∧
    -Real.log (500000000000 / 654370504449) ≤ (134532807 / 500000000) := by
  have h := checkLog_sound (w := (154370504449 / 1154370504449)) (n := 12)
    (lo := (269065613 / 1000000000)) (hi := (134532807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654370504449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654370504449 / 500000000000) = 1/(500000000000 / 654370504449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (269065613 / 1000000000) (134532807 / 500000000) (Real.log (654370504449 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (654370504449 / 500000000000) = -Real.log (500000000000 / 654370504449) := by
    rw [show ((654370504449 / 500000000000) : ℝ) = ((500000000000 / 654370504449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9022371 / 500000000) ≤ -Real.log (982117089471 / 1000000000000) ∧
    -Real.log (982117089471 / 1000000000000) ≤ (18044743 / 1000000000) := by
  have h := checkLog_sound (w := (17882910529 / 1982117089471)) (n := 12)
    (lo := (9022371 / 500000000)) (hi := (18044743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982117089471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982117089471) = 1/(982117089471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18044743 / 1000000000) (-9022371 / 500000000) (Real.log (982117089471 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17961509 / 1000000000) ≤ -Real.log (982198836759 / 1000000000000) ∧
    -Real.log (982198836759 / 1000000000000) ≤ (1796151 / 100000000) := by
  have h := checkLog_sound (w := (17801163241 / 1982198836759)) (n := 12)
    (lo := (17961509 / 1000000000)) (hi := (1796151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982198836759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982198836759) = 1/(982198836759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1796151 / 100000000) (-17961509 / 1000000000) (Real.log (982198836759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell023
