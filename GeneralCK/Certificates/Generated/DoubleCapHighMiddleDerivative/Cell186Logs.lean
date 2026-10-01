import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell186
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

theorem reflection_log_1_neg : (307168703 / 1000000000) ≤ -Real.log (5120 / 6961) ∧
    -Real.log (5120 / 6961) ≤ (4799511 / 15625000) := by
  have h := checkLog_sound (w := (1841 / 12081)) (n := 12)
    (lo := (307168703 / 1000000000)) (hi := (4799511 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6961 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6961 / 5120) = 1/(5120 / 6961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (307168703 / 1000000000) (4799511 / 15625000) (Real.log (6961 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6961 / 5120) = -Real.log (5120 / 6961) := by
    rw [show ((6961 / 5120) : ℝ) = ((5120 / 6961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445615941 / 1000000000) ≤ -Real.log (3279 / 5120) ∧
    -Real.log (3279 / 5120) ≤ (222807971 / 500000000) := by
  have h := checkLog_sound (w := (1841 / 8399)) (n := 12)
    (lo := (445615941 / 1000000000)) (hi := (222807971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3279) = 1/(3279 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-222807971 / 500000000) (-445615941 / 1000000000) (Real.log (3279 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (306737637 / 1000000000) ≤ -Real.log (2560 / 3479) ∧
    -Real.log (2560 / 3479) ≤ (153368819 / 500000000) := by
  have h := checkLog_sound (w := (919 / 6039)) (n := 12)
    (lo := (306737637 / 1000000000)) (hi := (153368819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3479 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3479 / 2560) = 1/(2560 / 3479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (306737637 / 1000000000) (153368819 / 500000000) (Real.log (3479 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3479 / 2560) = -Real.log (2560 / 3479) := by
    rw [show ((3479 / 2560) : ℝ) = ((2560 / 3479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (222350723 / 500000000) ≤ -Real.log (1641 / 2560) ∧
    -Real.log (1641 / 2560) ≤ (444701447 / 1000000000) := by
  have h := checkLog_sound (w := (919 / 4201)) (n := 12)
    (lo := (222350723 / 500000000)) (hi := (444701447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1641) = 1/(1641 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-444701447 / 1000000000) (-222350723 / 500000000) (Real.log (1641 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (227359451 / 1000000000) ≤ -Real.log (1000000 / 1255281) ∧
    -Real.log (1000000 / 1255281) ≤ (56839863 / 250000000) := by
  have h := checkLog_sound (w := (255281 / 2255281)) (n := 12)
    (lo := (227359451 / 1000000000)) (hi := (56839863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255281 / 1000000) = 1/(1000000 / 1255281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (227359451 / 1000000000) (56839863 / 250000000) (Real.log (1255281 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1255281 / 1000000) = -Real.log (1000000 / 1255281) := by
    rw [show ((1255281 / 1000000) : ℝ) = ((1000000 / 1255281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (36843539 / 125000000) ≤ -Real.log (744719 / 1000000) ∧
    -Real.log (744719 / 1000000) ≤ (294748313 / 1000000000) := by
  have h := checkLog_sound (w := (255281 / 1744719)) (n := 12)
    (lo := (36843539 / 125000000)) (hi := (294748313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744719) = 1/(744719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294748313 / 1000000000) (-36843539 / 125000000) (Real.log (744719 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (227696371 / 1000000000) ≤ -Real.log (125000 / 156963) ∧
    -Real.log (125000 / 156963) ≤ (56924093 / 250000000) := by
  have h := checkLog_sound (w := (31963 / 281963)) (n := 12)
    (lo := (227696371 / 1000000000)) (hi := (56924093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156963 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156963 / 125000) = 1/(125000 / 156963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (227696371 / 1000000000) (56924093 / 250000000) (Real.log (156963 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (156963 / 125000) = -Real.log (125000 / 156963) := by
    rw [show ((156963 / 125000) : ℝ) = ((125000 / 156963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (295316473 / 1000000000) ≤ -Real.log (93037 / 125000) ∧
    -Real.log (93037 / 125000) ≤ (147658237 / 500000000) := by
  have h := checkLog_sound (w := (31963 / 218037)) (n := 12)
    (lo := (295316473 / 1000000000)) (hi := (147658237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93037) = 1/(93037 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-147658237 / 500000000) (-295316473 / 1000000000) (Real.log (93037 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1687541 / 10000000) ≤ -Real.log (1000000 / 1183829) ∧
    -Real.log (1000000 / 1183829) ≤ (168754101 / 1000000000) := by
  have h := checkLog_sound (w := (183829 / 2183829)) (n := 12)
    (lo := (1687541 / 10000000)) (hi := (168754101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183829 / 1000000) = 1/(1000000 / 1183829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1687541 / 10000000) (168754101 / 1000000000) (Real.log (1183829 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1183829 / 1000000) = -Real.log (1000000 / 1183829) := by
    rw [show ((1183829 / 1000000) : ℝ) = ((1000000 / 1183829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (203131387 / 1000000000) ≤ -Real.log (816171 / 1000000) ∧
    -Real.log (816171 / 1000000) ≤ (50782847 / 250000000) := by
  have h := checkLog_sound (w := (183829 / 1816171)) (n := 12)
    (lo := (203131387 / 1000000000)) (hi := (50782847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816171) = 1/(816171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50782847 / 250000000) (-203131387 / 1000000000) (Real.log (816171 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33804199 / 200000000) ≤ -Real.log (200000 / 236829) ∧
    -Real.log (200000 / 236829) ≤ (42255249 / 250000000) := by
  have h := checkLog_sound (w := (36829 / 436829)) (n := 12)
    (lo := (33804199 / 200000000)) (hi := (42255249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236829 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236829 / 200000) = 1/(200000 / 236829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33804199 / 200000000) (42255249 / 250000000) (Real.log (236829 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (236829 / 200000) = -Real.log (200000 / 236829) := by
    rw [show ((236829 / 200000) : ℝ) = ((200000 / 236829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40703727 / 200000000) ≤ -Real.log (163171 / 200000) ∧
    -Real.log (163171 / 200000) ≤ (50879659 / 250000000) := by
  have h := checkLog_sound (w := (36829 / 363171)) (n := 12)
    (lo := (40703727 / 200000000)) (hi := (50879659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163171) = 1/(163171 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50879659 / 250000000) (-40703727 / 200000000) (Real.log (163171 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (751439083 / 1000000000) ≤ -Real.log (25000000000 / 53001218769) ∧
    -Real.log (25000000000 / 53001218769) ≤ (150287817 / 200000000) := by
  have h := checkLog_sound (w := (3001218769 / 103001218769)) (n := 12)
    (lo := (58291903 / 1000000000)) (hi := (910811 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53001218769 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53001218769 / 50000000000) = 1/(25000000000 / 53001218769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (751439083 / 1000000000) (150287817 / 200000000) (Real.log (53001218769 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (53001218769 / 25000000000) = -Real.log (25000000000 / 53001218769) := by
    rw [show ((53001218769 / 25000000000) : ℝ) = ((25000000000 / 53001218769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (752784643 / 1000000000) ≤ -Real.log (500000000000 / 1061451662093) ∧
    -Real.log (500000000000 / 1061451662093) ≤ (150556929 / 200000000) := by
  have h := checkLog_sound (w := (61451662093 / 2061451662093)) (n := 12)
    (lo := (59637463 / 1000000000)) (hi := (7454683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061451662093 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061451662093 / 1000000000000) = 1/(500000000000 / 1061451662093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (752784643 / 1000000000) (150556929 / 200000000) (Real.log (1061451662093 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1061451662093 / 500000000000) = -Real.log (500000000000 / 1061451662093) := by
    rw [show ((1061451662093 / 500000000000) : ℝ) = ((500000000000 / 1061451662093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (130526941 / 250000000) ≤ -Real.log (7812500000 / 13168568027) ∧
    -Real.log (7812500000 / 13168568027) ≤ (104421553 / 200000000) := by
  have h := checkLog_sound (w := (5356068027 / 20981068027)) (n := 12)
    (lo := (130526941 / 250000000)) (hi := (104421553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13168568027 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13168568027 / 7812500000) = 1/(7812500000 / 13168568027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130526941 / 250000000) (104421553 / 200000000) (Real.log (13168568027 / 7812500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13168568027 / 7812500000) = -Real.log (7812500000 / 13168568027) := by
    rw [show ((13168568027 / 7812500000) : ℝ) = ((7812500000 / 13168568027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104602569 / 200000000) ≤ -Real.log (125000000000 / 210887872567) ∧
    -Real.log (125000000000 / 210887872567) ≤ (261506423 / 500000000) := by
  have h := checkLog_sound (w := (85887872567 / 335887872567)) (n := 12)
    (lo := (104602569 / 200000000)) (hi := (261506423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210887872567 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210887872567 / 125000000000) = 1/(125000000000 / 210887872567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104602569 / 200000000) (261506423 / 500000000) (Real.log (210887872567 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (210887872567 / 125000000000) = -Real.log (125000000000 / 210887872567) := by
    rw [show ((210887872567 / 125000000000) : ℝ) = ((125000000000 / 210887872567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (371885487 / 1000000000) ≤ -Real.log (625000000 / 906541797) ∧
    -Real.log (625000000 / 906541797) ≤ (23242843 / 62500000) := by
  have h := checkLog_sound (w := (281541797 / 1531541797)) (n := 12)
    (lo := (371885487 / 1000000000)) (hi := (23242843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906541797 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906541797 / 625000000) = 1/(625000000 / 906541797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (371885487 / 1000000000) (23242843 / 62500000) (Real.log (906541797 / 625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (906541797 / 625000000) = -Real.log (625000000 / 906541797) := by
    rw [show ((906541797 / 625000000) : ℝ) = ((625000000 / 906541797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (372539631 / 1000000000) ≤ -Real.log (15625000000 / 22678374987) ∧
    -Real.log (15625000000 / 22678374987) ≤ (23283727 / 62500000) := by
  have h := checkLog_sound (w := (7053374987 / 38303374987)) (n := 12)
    (lo := (372539631 / 1000000000)) (hi := (23283727 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22678374987 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22678374987 / 15625000000) = 1/(15625000000 / 22678374987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (372539631 / 1000000000) (23283727 / 62500000) (Real.log (22678374987 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22678374987 / 15625000000) = -Real.log (15625000000 / 22678374987) := by
    rw [show ((22678374987 / 15625000000) : ℝ) = ((15625000000 / 22678374987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (862441 / 25000000) ≤ -Real.log (38643624759 / 40000000000) ∧
    -Real.log (38643624759 / 40000000000) ≤ (34497641 / 1000000000) := by
  have h := checkLog_sound (w := (1356375241 / 78643624759)) (n := 12)
    (lo := (862441 / 25000000)) (hi := (34497641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38643624759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38643624759) = 1/(38643624759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34497641 / 1000000000) (-862441 / 25000000) (Real.log (38643624759 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17188643 / 500000000) ≤ -Real.log (966206898759 / 1000000000000) ∧
    -Real.log (966206898759 / 1000000000000) ≤ (34377287 / 1000000000) := by
  have h := checkLog_sound (w := (33793101241 / 1966206898759)) (n := 12)
    (lo := (17188643 / 500000000)) (hi := (34377287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966206898759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966206898759) = 1/(966206898759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34377287 / 1000000000) (-17188643 / 500000000) (Real.log (966206898759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell186
