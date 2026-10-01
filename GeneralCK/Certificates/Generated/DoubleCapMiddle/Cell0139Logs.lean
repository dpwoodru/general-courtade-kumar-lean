import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0139
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_1_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (299236159 / 1000000000) ≤ -Real.log (2560 / 3453) ∧
    -Real.log (2560 / 3453) ≤ (935113 / 3125000) := by
  have h := checkLog_sound (w := (893 / 6013)) (n := 12)
    (lo := (299236159 / 1000000000)) (hi := (935113 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3453 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3453 / 2560) = 1/(2560 / 3453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (299236159 / 1000000000) (935113 / 3125000) (Real.log (3453 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3453 / 2560) = -Real.log (2560 / 3453) := by
    rw [show ((3453 / 2560) : ℝ) = ((2560 / 3453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (214490827 / 500000000) ≤ -Real.log (1667 / 2560) ∧
    -Real.log (1667 / 2560) ≤ (85796331 / 200000000) := by
  have h := checkLog_sound (w := (893 / 4227)) (n := 12)
    (lo := (214490827 / 500000000)) (hi := (85796331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1667) = 1/(1667 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-85796331 / 200000000) (-214490827 / 500000000) (Real.log (1667 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (530628251 / 1000000000) ≤ -Real.log (10 / 17) ∧
    -Real.log (10 / 17) ≤ (132657063 / 250000000) := by
  have h := checkLog_sound (w := (7 / 27)) (n := 12)
    (lo := (530628251 / 1000000000)) (hi := (132657063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17 / 10) = 1/(10 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (530628251 / 1000000000) (132657063 / 250000000) (Real.log (17 / 10)) := by
  have h := reflection_log_5_neg
  have he : Real.log (17 / 10) = -Real.log (10 / 17) := by
    rw [show ((17 / 10) : ℝ) = ((10 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1203972803 / 1000000000) ≤ -Real.log (3 / 10) ∧
    -Real.log (3 / 10) ≤ (240794561 / 200000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 3) = 1/(3 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-240794561 / 200000000) (-1203972803 / 1000000000) (Real.log (3 / 10)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (529248623 / 1000000000) ≤ -Real.log (1280 / 2173) ∧
    -Real.log (1280 / 2173) ≤ (33078039 / 62500000) := by
  have h := checkLog_sound (w := (893 / 3453)) (n := 12)
    (lo := (529248623 / 1000000000)) (hi := (33078039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2173 / 1280) = 1/(1280 / 2173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (529248623 / 1000000000) (33078039 / 62500000) (Real.log (2173 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2173 / 1280) = -Real.log (1280 / 2173) := by
    rw [show ((2173 / 1280) : ℝ) = ((1280 / 2173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1196190663 / 1000000000) ≤ -Real.log (387 / 1280) ∧
    -Real.log (387 / 1280) ≤ (239238133 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 387) = 1/(387 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-239238133 / 200000000) (-1196190663 / 1000000000) (Real.log (387 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40954411 / 100000000) ≤ -Real.log (1000000 / 1506131) ∧
    -Real.log (1000000 / 1506131) ≤ (409544111 / 1000000000) := by
  have h := checkLog_sound (w := (506131 / 2506131)) (n := 12)
    (lo := (40954411 / 100000000)) (hi := (409544111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1506131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1506131 / 1000000) = 1/(1000000 / 1506131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40954411 / 100000000) (409544111 / 1000000000) (Real.log (1506131 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1506131 / 1000000) = -Real.log (1000000 / 1506131) := by
    rw [show ((1506131 / 1000000) : ℝ) = ((1000000 / 1506131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (352742489 / 500000000) ≤ -Real.log (493869 / 1000000) ∧
    -Real.log (493869 / 1000000) ≤ (35274249 / 50000000) := by
  have h := checkLog_sound (w := (6131 / 993869)) (n := 12)
    (lo := (6168899 / 500000000)) (hi := (12337799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 493869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 493869) = 1/(493869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-35274249 / 50000000) (-352742489 / 500000000) (Real.log (493869 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (410748459 / 1000000000) ≤ -Real.log (500000 / 753973) ∧
    -Real.log (500000 / 753973) ≤ (20537423 / 50000000) := by
  have h := checkLog_sound (w := (253973 / 1253973)) (n := 12)
    (lo := (410748459 / 1000000000)) (hi := (20537423 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753973 / 500000) = 1/(500000 / 753973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (410748459 / 1000000000) (20537423 / 50000000) (Real.log (753973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (753973 / 500000) = -Real.log (500000 / 753973) := by
    rw [show ((753973 / 500000) : ℝ) = ((500000 / 753973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (709166811 / 1000000000) ≤ -Real.log (246027 / 500000) ∧
    -Real.log (246027 / 500000) ≤ (709166813 / 1000000000) := by
  have h := checkLog_sound (w := (3973 / 496027)) (n := 12)
    (lo := (16019631 / 1000000000)) (hi := (1001227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246027) = 1/(246027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-709166813 / 1000000000) (-709166811 / 1000000000) (Real.log (246027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325765841 / 1000000000) ≤ -Real.log (1000000 / 1385091) ∧
    -Real.log (1000000 / 1385091) ≤ (162882921 / 500000000) := by
  have h := checkLog_sound (w := (385091 / 2385091)) (n := 12)
    (lo := (325765841 / 1000000000)) (hi := (162882921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385091 / 1000000) = 1/(1000000 / 1385091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325765841 / 1000000000) (162882921 / 500000000) (Real.log (1385091 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1385091 / 1000000) = -Real.log (1000000 / 1385091) := by
    rw [show ((1385091 / 1000000) : ℝ) = ((1000000 / 1385091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (486280989 / 1000000000) ≤ -Real.log (614909 / 1000000) ∧
    -Real.log (614909 / 1000000) ≤ (48628099 / 100000000) := by
  have h := checkLog_sound (w := (385091 / 1614909)) (n := 12)
    (lo := (486280989 / 1000000000)) (hi := (48628099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614909) = 1/(614909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-48628099 / 100000000) (-486280989 / 1000000000) (Real.log (614909 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (326913843 / 1000000000) ≤ -Real.log (500000 / 693341) ∧
    -Real.log (500000 / 693341) ≤ (81728461 / 250000000) := by
  have h := checkLog_sound (w := (193341 / 1193341)) (n := 12)
    (lo := (326913843 / 1000000000)) (hi := (81728461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693341 / 500000) = 1/(500000 / 693341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (326913843 / 1000000000) (81728461 / 250000000) (Real.log (693341 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (693341 / 500000) = -Real.log (500000 / 693341) := by
    rw [show ((693341 / 500000) : ℝ) = ((500000 / 693341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (488871717 / 1000000000) ≤ -Real.log (306659 / 500000) ∧
    -Real.log (306659 / 500000) ≤ (244435859 / 500000000) := by
  have h := checkLog_sound (w := (193341 / 806659)) (n := 12)
    (lo := (488871717 / 1000000000)) (hi := (244435859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 306659) = 1/(306659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-244435859 / 500000000) (-488871717 / 1000000000) (Real.log (306659 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1115029089 / 1000000000) ≤ -Real.log (500000000000 / 1524828446409) ∧
    -Real.log (500000000000 / 1524828446409) ≤ (1115029091 / 1000000000) := by
  have h := checkLog_sound (w := (524828446409 / 2524828446409)) (n := 12)
    (lo := (421881909 / 1000000000)) (hi := (42188191 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524828446409 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1524828446409 / 1000000000000) = 1/(500000000000 / 1524828446409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1115029089 / 1000000000) (1115029091 / 1000000000) (Real.log (1524828446409 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1524828446409 / 500000000000) = -Real.log (500000000000 / 1524828446409) := by
    rw [show ((1524828446409 / 500000000000) : ℝ) = ((500000000000 / 1524828446409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1119915271 / 1000000000) ≤ -Real.log (500000000000 / 1532297268187) ∧
    -Real.log (500000000000 / 1532297268187) ≤ (1119915273 / 1000000000) := by
  have h := checkLog_sound (w := (532297268187 / 2532297268187)) (n := 12)
    (lo := (426768091 / 1000000000)) (hi := (106692023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1532297268187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1532297268187 / 1000000000000) = 1/(500000000000 / 1532297268187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1119915271 / 1000000000) (1119915273 / 1000000000) (Real.log (1532297268187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1532297268187 / 500000000000) = -Real.log (500000000000 / 1532297268187) := by
    rw [show ((1532297268187 / 500000000000) : ℝ) = ((500000000000 / 1532297268187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (81204683 / 100000000) ≤ -Real.log (31250000000 / 70391055831) ∧
    -Real.log (31250000000 / 70391055831) ≤ (50752927 / 62500000) := by
  have h := checkLog_sound (w := (7891055831 / 132891055831)) (n := 12)
    (lo := (2377993 / 20000000)) (hi := (118899651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70391055831 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70391055831 / 62500000000) = 1/(31250000000 / 70391055831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (81204683 / 100000000) (50752927 / 62500000) (Real.log (70391055831 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (70391055831 / 31250000000) = -Real.log (31250000000 / 70391055831) := by
    rw [show ((70391055831 / 31250000000) : ℝ) = ((31250000000 / 70391055831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (20394639 / 25000000) ≤ -Real.log (250000000000 / 565237772249) ∧
    -Real.log (250000000000 / 565237772249) ≤ (407892781 / 500000000) := by
  have h := checkLog_sound (w := (65237772249 / 1065237772249)) (n := 12)
    (lo := (6131919 / 50000000)) (hi := (122638381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565237772249 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565237772249 / 500000000000) = 1/(250000000000 / 565237772249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (20394639 / 25000000) (407892781 / 500000000) (Real.log (565237772249 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (565237772249 / 250000000000) = -Real.log (250000000000 / 565237772249) := by
    rw [show ((565237772249 / 250000000000) : ℝ) = ((250000000000 / 565237772249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0139
