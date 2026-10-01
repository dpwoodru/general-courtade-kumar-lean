import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell141
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

theorem reflection_log_1_neg : (287584411 / 1000000000) ≤ -Real.log (2560 / 3413) ∧
    -Real.log (2560 / 3413) ≤ (71896103 / 250000000) := by
  have h := checkLog_sound (w := (853 / 5973)) (n := 12)
    (lo := (287584411 / 1000000000)) (hi := (71896103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3413 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3413 / 2560) = 1/(2560 / 3413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (287584411 / 1000000000) (71896103 / 250000000) (Real.log (3413 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3413 / 2560) = -Real.log (2560 / 3413) := by
    rw [show ((3413 / 2560) : ℝ) = ((2560 / 3413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (202634907 / 500000000) ≤ -Real.log (1707 / 2560) ∧
    -Real.log (1707 / 2560) ≤ (81053963 / 200000000) := by
  have h := checkLog_sound (w := (853 / 4267)) (n := 12)
    (lo := (202634907 / 500000000)) (hi := (81053963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1707) = 1/(1707 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-81053963 / 200000000) (-202634907 / 500000000) (Real.log (1707 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (143572409 / 500000000) ≤ -Real.log (5120 / 6823) ∧
    -Real.log (5120 / 6823) ≤ (287144819 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 11943)) (n := 12)
    (lo := (143572409 / 500000000)) (hi := (287144819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6823 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6823 / 5120) = 1/(5120 / 6823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (143572409 / 500000000) (287144819 / 1000000000) (Real.log (6823 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6823 / 5120) = -Real.log (5120 / 6823) := by
    rw [show ((6823 / 5120) : ℝ) = ((5120 / 6823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (80878293 / 200000000) ≤ -Real.log (3417 / 5120) ∧
    -Real.log (3417 / 5120) ≤ (202195733 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 8537)) (n := 12)
    (lo := (80878293 / 200000000)) (hi := (202195733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3417) = 1/(3417 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-202195733 / 500000000) (-80878293 / 200000000) (Real.log (3417 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (212148931 / 1000000000) ≤ -Real.log (250000 / 309083) ∧
    -Real.log (250000 / 309083) ≤ (53037233 / 250000000) := by
  have h := checkLog_sound (w := (59083 / 559083)) (n := 12)
    (lo := (212148931 / 1000000000)) (hi := (53037233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309083 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309083 / 250000) = 1/(250000 / 309083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (212148931 / 1000000000) (53037233 / 250000000) (Real.log (309083 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (309083 / 250000) = -Real.log (250000 / 309083) := by
    rw [show ((309083 / 250000) : ℝ) = ((250000 / 309083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (269622139 / 1000000000) ≤ -Real.log (190917 / 250000) ∧
    -Real.log (190917 / 250000) ≤ (13481107 / 50000000) := by
  have h := checkLog_sound (w := (59083 / 440917)) (n := 12)
    (lo := (269622139 / 1000000000)) (hi := (13481107 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190917) = 1/(190917 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13481107 / 50000000) (-269622139 / 1000000000) (Real.log (190917 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42498041 / 200000000) ≤ -Real.log (500000 / 618377) ∧
    -Real.log (500000 / 618377) ≤ (106245103 / 500000000) := by
  have h := checkLog_sound (w := (118377 / 1118377)) (n := 12)
    (lo := (42498041 / 200000000)) (hi := (106245103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618377 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618377 / 500000) = 1/(500000 / 618377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42498041 / 200000000) (106245103 / 500000000) (Real.log (618377 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (618377 / 500000) = -Real.log (500000 / 618377) := by
    rw [show ((618377 / 500000) : ℝ) = ((500000 / 618377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33771861 / 125000000) ≤ -Real.log (381623 / 500000) ∧
    -Real.log (381623 / 500000) ≤ (270174889 / 1000000000) := by
  have h := checkLog_sound (w := (118377 / 881623)) (n := 12)
    (lo := (33771861 / 125000000)) (hi := (270174889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381623) = 1/(381623 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-270174889 / 1000000000) (-33771861 / 125000000) (Real.log (381623 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156780647 / 1000000000) ≤ -Real.log (1000000 / 1169739) ∧
    -Real.log (1000000 / 1169739) ≤ (19597581 / 125000000) := by
  have h := checkLog_sound (w := (169739 / 2169739)) (n := 12)
    (lo := (156780647 / 1000000000)) (hi := (19597581 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169739 / 1000000) = 1/(1000000 / 1169739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156780647 / 1000000000) (19597581 / 125000000) (Real.log (1169739 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1169739 / 1000000) = -Real.log (1000000 / 1169739) := by
    rw [show ((1169739 / 1000000) : ℝ) = ((1000000 / 1169739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (186015169 / 1000000000) ≤ -Real.log (830261 / 1000000) ∧
    -Real.log (830261 / 1000000) ≤ (18601517 / 100000000) := by
  have h := checkLog_sound (w := (169739 / 1830261)) (n := 12)
    (lo := (186015169 / 1000000000)) (hi := (18601517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830261) = 1/(830261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18601517 / 100000000) (-186015169 / 1000000000) (Real.log (830261 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157047337 / 1000000000) ≤ -Real.log (1000000 / 1170051) ∧
    -Real.log (1000000 / 1170051) ≤ (78523669 / 500000000) := by
  have h := checkLog_sound (w := (170051 / 2170051)) (n := 12)
    (lo := (157047337 / 1000000000)) (hi := (78523669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170051 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170051 / 1000000) = 1/(1000000 / 1170051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157047337 / 1000000000) (78523669 / 500000000) (Real.log (1170051 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1170051 / 1000000) = -Real.log (1000000 / 1170051) := by
    rw [show ((1170051 / 1000000) : ℝ) = ((1000000 / 1170051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7455641 / 40000000) ≤ -Real.log (829949 / 1000000) ∧
    -Real.log (829949 / 1000000) ≤ (93195513 / 500000000) := by
  have h := checkLog_sound (w := (170051 / 1829949)) (n := 12)
    (lo := (7455641 / 40000000)) (hi := (93195513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829949) = 1/(829949 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93195513 / 500000000) (-7455641 / 40000000) (Real.log (829949 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (172884071 / 250000000) ≤ -Real.log (62500000000 / 124798800117) ∧
    -Real.log (62500000000 / 124798800117) ≤ (138307257 / 200000000) := by
  have h := checkLog_sound (w := (62298800117 / 187298800117)) (n := 12)
    (lo := (172884071 / 250000000)) (hi := (138307257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124798800117 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124798800117 / 62500000000) = 1/(62500000000 / 124798800117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (172884071 / 250000000) (138307257 / 200000000) (Real.log (124798800117 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (124798800117 / 62500000000) = -Real.log (62500000000 / 124798800117) := by
    rw [show ((124798800117 / 62500000000) : ℝ) = ((62500000000 / 124798800117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (346427113 / 500000000) ≤ -Real.log (25000000000 / 49985354423) ∧
    -Real.log (25000000000 / 49985354423) ≤ (692854227 / 1000000000) := by
  have h := checkLog_sound (w := (24985354423 / 74985354423)) (n := 12)
    (lo := (346427113 / 500000000)) (hi := (692854227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49985354423 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49985354423 / 25000000000) = 1/(25000000000 / 49985354423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (346427113 / 500000000) (692854227 / 1000000000) (Real.log (49985354423 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (49985354423 / 25000000000) = -Real.log (25000000000 / 49985354423) := by
    rw [show ((49985354423 / 25000000000) : ℝ) = ((25000000000 / 49985354423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (48177107 / 100000000) ≤ -Real.log (50000000000 / 80946956007) ∧
    -Real.log (50000000000 / 80946956007) ≤ (481771071 / 1000000000) := by
  have h := checkLog_sound (w := (30946956007 / 130946956007)) (n := 12)
    (lo := (48177107 / 100000000)) (hi := (481771071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80946956007 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80946956007 / 50000000000) = 1/(50000000000 / 80946956007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48177107 / 100000000) (481771071 / 1000000000) (Real.log (80946956007 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (80946956007 / 50000000000) = -Real.log (50000000000 / 80946956007) := by
    rw [show ((80946956007 / 50000000000) : ℝ) = ((50000000000 / 80946956007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (482665093 / 1000000000) ≤ -Real.log (250000000000 / 405096783999) ∧
    -Real.log (250000000000 / 405096783999) ≤ (241332547 / 500000000) := by
  have h := checkLog_sound (w := (155096783999 / 655096783999)) (n := 12)
    (lo := (482665093 / 1000000000)) (hi := (241332547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405096783999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405096783999 / 250000000000) = 1/(250000000000 / 405096783999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (482665093 / 1000000000) (241332547 / 500000000) (Real.log (405096783999 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (405096783999 / 250000000000) = -Real.log (250000000000 / 405096783999) := by
    rw [show ((405096783999 / 250000000000) : ℝ) = ((250000000000 / 405096783999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (42849477 / 125000000) ≤ -Real.log (10000000000 / 14088810627) ∧
    -Real.log (10000000000 / 14088810627) ≤ (342795817 / 1000000000) := by
  have h := checkLog_sound (w := (4088810627 / 24088810627)) (n := 12)
    (lo := (42849477 / 125000000)) (hi := (342795817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14088810627 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14088810627 / 10000000000) = 1/(10000000000 / 14088810627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (42849477 / 125000000) (342795817 / 1000000000) (Real.log (14088810627 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14088810627 / 10000000000) = -Real.log (10000000000 / 14088810627) := by
    rw [show ((14088810627 / 10000000000) : ℝ) = ((10000000000 / 14088810627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (343438363 / 1000000000) ≤ -Real.log (250000000000 / 352446656361) ∧
    -Real.log (250000000000 / 352446656361) ≤ (85859591 / 250000000) := by
  have h := checkLog_sound (w := (102446656361 / 602446656361)) (n := 12)
    (lo := (343438363 / 1000000000)) (hi := (85859591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352446656361 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352446656361 / 250000000000) = 1/(250000000000 / 352446656361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (343438363 / 1000000000) (85859591 / 250000000) (Real.log (352446656361 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (352446656361 / 250000000000) = -Real.log (250000000000 / 352446656361) := by
    rw [show ((352446656361 / 250000000000) : ℝ) = ((250000000000 / 352446656361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3667961 / 125000000) ≤ -Real.log (971082657399 / 1000000000000) ∧
    -Real.log (971082657399 / 1000000000000) ≤ (29343689 / 1000000000) := by
  have h := checkLog_sound (w := (28917342601 / 1971082657399)) (n := 12)
    (lo := (3667961 / 125000000)) (hi := (29343689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971082657399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971082657399) = 1/(971082657399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29343689 / 1000000000) (-3667961 / 125000000) (Real.log (971082657399 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14617261 / 500000000) ≤ -Real.log (971188671879 / 1000000000000) ∧
    -Real.log (971188671879 / 1000000000000) ≤ (29234523 / 1000000000) := by
  have h := checkLog_sound (w := (28811328121 / 1971188671879)) (n := 12)
    (lo := (14617261 / 500000000)) (hi := (29234523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971188671879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971188671879) = 1/(971188671879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29234523 / 1000000000) (-14617261 / 500000000) (Real.log (971188671879 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell141
