import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell022
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

theorem reflection_log_1_neg : (116933549 / 500000000) ≤ -Real.log (5120 / 6469) ∧
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


theorem reflection_log_1 : Bounds (116933549 / 500000000) (233867099 / 1000000000) (Real.log (6469 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6469 / 5120) = -Real.log (5120 / 6469) := by
    rw [show ((6469 / 5120) : ℝ) = ((5120 / 6469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15290711 / 50000000) ≤ -Real.log (3771 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-305814221 / 1000000000) (-15290711 / 50000000) (Real.log (3771 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5835081 / 25000000) ≤ -Real.log (2560 / 3233) ∧
    -Real.log (2560 / 3233) ≤ (233403241 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 5793)) (n := 12)
    (lo := (5835081 / 25000000)) (hi := (233403241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3233 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3233 / 2560) = 1/(2560 / 3233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5835081 / 25000000) (233403241 / 1000000000) (Real.log (3233 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3233 / 2560) = -Real.log (2560 / 3233) := by
    rw [show ((3233 / 2560) : ℝ) = ((2560 / 3233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19063687 / 62500000) ≤ -Real.log (1887 / 2560) ∧
    -Real.log (1887 / 2560) ≤ (305018993 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 4447)) (n := 12)
    (lo := (19063687 / 62500000)) (hi := (305018993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1887) = 1/(1887 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-305018993 / 1000000000) (-19063687 / 62500000) (Real.log (1887 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2671233 / 15625000) ≤ -Real.log (500000 / 593221) ∧
    -Real.log (500000 / 593221) ≤ (170958913 / 1000000000) := by
  have h := checkLog_sound (w := (93221 / 1093221)) (n := 12)
    (lo := (2671233 / 15625000)) (hi := (170958913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593221 / 500000) = 1/(500000 / 593221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2671233 / 15625000) (170958913 / 1000000000) (Real.log (593221 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593221 / 500000) = -Real.log (500000 / 593221) := by
    rw [show ((593221 / 500000) : ℝ) = ((500000 / 593221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (206338057 / 1000000000) ≤ -Real.log (406779 / 500000) ∧
    -Real.log (406779 / 500000) ≤ (103169029 / 500000000) := by
  have h := checkLog_sound (w := (93221 / 906779)) (n := 12)
    (lo := (206338057 / 1000000000)) (hi := (103169029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406779) = 1/(406779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-103169029 / 500000000) (-206338057 / 1000000000) (Real.log (406779 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171312849 / 1000000000) ≤ -Real.log (500000 / 593431) ∧
    -Real.log (500000 / 593431) ≤ (3426257 / 20000000) := by
  have h := checkLog_sound (w := (93431 / 1093431)) (n := 12)
    (lo := (171312849 / 1000000000)) (hi := (3426257 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593431 / 500000) = 1/(500000 / 593431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171312849 / 1000000000) (3426257 / 20000000) (Real.log (593431 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (593431 / 500000) = -Real.log (500000 / 593431) := by
    rw [show ((593431 / 500000) : ℝ) = ((500000 / 593431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103427221 / 500000000) ≤ -Real.log (406569 / 500000) ∧
    -Real.log (406569 / 500000) ≤ (206854443 / 1000000000) := by
  have h := checkLog_sound (w := (93431 / 906569)) (n := 12)
    (lo := (103427221 / 500000000)) (hi := (206854443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406569) = 1/(406569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-206854443 / 1000000000) (-103427221 / 500000000) (Real.log (406569 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62486121 / 500000000) ≤ -Real.log (1000000 / 1133117) ∧
    -Real.log (1000000 / 1133117) ≤ (124972243 / 1000000000) := by
  have h := checkLog_sound (w := (133117 / 2133117)) (n := 12)
    (lo := (62486121 / 500000000)) (hi := (124972243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133117 / 1000000) = 1/(1000000 / 1133117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62486121 / 500000000) (124972243 / 1000000000) (Real.log (1133117 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1133117 / 1000000) = -Real.log (1000000 / 1133117) := by
    rw [show ((1133117 / 1000000) : ℝ) = ((1000000 / 1133117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (142851259 / 1000000000) ≤ -Real.log (866883 / 1000000) ∧
    -Real.log (866883 / 1000000) ≤ (7142563 / 50000000) := by
  have h := checkLog_sound (w := (133117 / 1866883)) (n := 12)
    (lo := (142851259 / 1000000000)) (hi := (7142563 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866883) = 1/(866883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7142563 / 50000000) (-142851259 / 1000000000) (Real.log (866883 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1001931 / 8000000) ≤ -Real.log (500000 / 566711) ∧
    -Real.log (500000 / 566711) ≤ (3913793 / 31250000) := by
  have h := checkLog_sound (w := (66711 / 1066711)) (n := 12)
    (lo := (1001931 / 8000000)) (hi := (3913793 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566711 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566711 / 500000) = 1/(500000 / 566711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1001931 / 8000000) (3913793 / 31250000) (Real.log (566711 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (566711 / 500000) = -Real.log (500000 / 566711) := by
    rw [show ((566711 / 500000) : ℝ) = ((500000 / 566711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (35800789 / 250000000) ≤ -Real.log (433289 / 500000) ∧
    -Real.log (433289 / 500000) ≤ (143203157 / 1000000000) := by
  have h := checkLog_sound (w := (66711 / 933289)) (n := 12)
    (lo := (35800789 / 250000000)) (hi := (143203157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433289) = 1/(433289 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-143203157 / 1000000000) (-35800789 / 250000000) (Real.log (433289 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67302779 / 125000000) ≤ -Real.log (100000000000 / 171330153683) ∧
    -Real.log (100000000000 / 171330153683) ≤ (538422233 / 1000000000) := by
  have h := checkLog_sound (w := (71330153683 / 271330153683)) (n := 12)
    (lo := (67302779 / 125000000)) (hi := (538422233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171330153683 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171330153683 / 100000000000) = 1/(100000000000 / 171330153683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67302779 / 125000000) (538422233 / 1000000000) (Real.log (171330153683 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (171330153683 / 100000000000) = -Real.log (100000000000 / 171330153683) := by
    rw [show ((171330153683 / 100000000000) : ℝ) = ((100000000000 / 171330153683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (269840659 / 500000000) ≤ -Real.log (500000000000 / 857730045081) ∧
    -Real.log (500000000000 / 857730045081) ≤ (539681319 / 1000000000) := by
  have h := checkLog_sound (w := (357730045081 / 1357730045081)) (n := 12)
    (lo := (269840659 / 500000000)) (hi := (539681319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857730045081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857730045081 / 500000000000) = 1/(500000000000 / 857730045081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (269840659 / 500000000) (539681319 / 1000000000) (Real.log (857730045081 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (857730045081 / 500000000000) = -Real.log (500000000000 / 857730045081) := by
    rw [show ((857730045081 / 500000000000) : ℝ) = ((500000000000 / 857730045081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (37729697 / 100000000) ≤ -Real.log (100000000000 / 145833732813) ∧
    -Real.log (100000000000 / 145833732813) ≤ (377296971 / 1000000000) := by
  have h := checkLog_sound (w := (45833732813 / 245833732813)) (n := 12)
    (lo := (37729697 / 100000000)) (hi := (377296971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145833732813 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145833732813 / 100000000000) = 1/(100000000000 / 145833732813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37729697 / 100000000) (377296971 / 1000000000) (Real.log (145833732813 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145833732813 / 100000000000) = -Real.log (100000000000 / 145833732813) := by
    rw [show ((145833732813 / 100000000000) : ℝ) = ((100000000000 / 145833732813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (378167291 / 1000000000) ≤ -Real.log (500000000000 / 729803551181) ∧
    -Real.log (500000000000 / 729803551181) ≤ (94541823 / 250000000) := by
  have h := checkLog_sound (w := (229803551181 / 1229803551181)) (n := 12)
    (lo := (378167291 / 1000000000)) (hi := (94541823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729803551181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729803551181 / 500000000000) = 1/(500000000000 / 729803551181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (378167291 / 1000000000) (94541823 / 250000000) (Real.log (729803551181 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (729803551181 / 500000000000) = -Real.log (500000000000 / 729803551181) := by
    rw [show ((729803551181 / 500000000000) : ℝ) = ((500000000000 / 729803551181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (267823501 / 1000000000) ≤ -Real.log (50000000000 / 65355820797) ∧
    -Real.log (50000000000 / 65355820797) ≤ (133911751 / 500000000) := by
  have h := checkLog_sound (w := (15355820797 / 115355820797)) (n := 12)
    (lo := (267823501 / 1000000000)) (hi := (133911751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65355820797 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65355820797 / 50000000000) = 1/(50000000000 / 65355820797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (267823501 / 1000000000) (133911751 / 500000000) (Real.log (65355820797 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65355820797 / 50000000000) = -Real.log (50000000000 / 65355820797) := by
    rw [show ((65355820797 / 50000000000) : ℝ) = ((50000000000 / 65355820797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (268444531 / 1000000000) ≤ -Real.log (250000000000 / 326982106631) ∧
    -Real.log (250000000000 / 326982106631) ≤ (67111133 / 250000000) := by
  have h := checkLog_sound (w := (76982106631 / 576982106631)) (n := 12)
    (lo := (268444531 / 1000000000)) (hi := (67111133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326982106631 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326982106631 / 250000000000) = 1/(250000000000 / 326982106631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (268444531 / 1000000000) (67111133 / 250000000) (Real.log (326982106631 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326982106631 / 250000000000) = -Real.log (250000000000 / 326982106631) := by
    rw [show ((326982106631 / 250000000000) : ℝ) = ((250000000000 / 326982106631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17961781 / 1000000000) ≤ -Real.log (245549642479 / 250000000000) ∧
    -Real.log (245549642479 / 250000000000) ≤ (8980891 / 500000000) := by
  have h := checkLog_sound (w := (4450357521 / 495549642479)) (n := 12)
    (lo := (17961781 / 1000000000)) (hi := (8980891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245549642479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245549642479) = 1/(245549642479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8980891 / 500000000) (-17961781 / 1000000000) (Real.log (245549642479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17879017 / 1000000000) ≤ -Real.log (982279864311 / 1000000000000) ∧
    -Real.log (982279864311 / 1000000000000) ≤ (8939509 / 500000000) := by
  have h := checkLog_sound (w := (17720135689 / 1982279864311)) (n := 12)
    (lo := (17879017 / 1000000000)) (hi := (8939509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982279864311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982279864311) = 1/(982279864311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8939509 / 500000000) (-17879017 / 1000000000) (Real.log (982279864311 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell022
