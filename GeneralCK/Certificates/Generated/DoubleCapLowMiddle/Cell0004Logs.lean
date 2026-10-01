import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0004
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

theorem reflection_log_1_neg : (341454703 / 500000000) ≤ -Real.log (51200 / 101357) ∧
    -Real.log (51200 / 101357) ≤ (682909407 / 1000000000) := by
  have h := checkLog_sound (w := (50157 / 152557)) (n := 12)
    (lo := (341454703 / 500000000)) (hi := (682909407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101357 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101357 / 51200) = 1/(51200 / 101357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341454703 / 500000000) (682909407 / 1000000000) (Real.log (101357 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101357 / 51200) = -Real.log (51200 / 101357) := by
    rw [show ((101357 / 51200) : ℝ) = ((51200 / 101357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3893638353 / 1000000000) ≤ -Real.log (1043 / 51200) ∧
    -Real.log (1043 / 51200) ≤ (3893638359 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1043) = 1/(1043 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3893638359 / 1000000000) (-3893638353 / 1000000000) (Real.log (1043 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34143127 / 50000000) ≤ -Real.log (250000000000 / 494884033203) ∧
    -Real.log (250000000000 / 494884033203) ≤ (682862541 / 1000000000) := by
  have h := checkLog_sound (w := (244884033203 / 744884033203)) (n := 12)
    (lo := (34143127 / 50000000)) (hi := (682862541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494884033203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494884033203 / 250000000000) = 1/(250000000000 / 494884033203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34143127 / 50000000) (682862541 / 1000000000) (Real.log (494884033203 / 250000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (494884033203 / 250000000000) = -Real.log (250000000000 / 494884033203) := by
    rw [show ((494884033203 / 250000000000) : ℝ) = ((250000000000 / 494884033203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3889094521 / 1000000000) ≤ -Real.log (5115966797 / 250000000000) ∧
    -Real.log (5115966797 / 250000000000) ≤ (3889094527 / 1000000000) := by
  have h := checkLog_sound (w := (2696533203 / 12928466797)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7812500000 / 5115966797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7812500000 / 5115966797) = 1/(5115966797 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3889094527 / 1000000000) (-3889094521 / 1000000000) (Real.log (5115966797 / 250000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (336282867 / 500000000) ≤ -Real.log (25600 / 50157) ∧
    -Real.log (25600 / 50157) ≤ (134513147 / 200000000) := by
  have h := checkLog_sound (w := (24557 / 75757)) (n := 12)
    (lo := (336282867 / 500000000)) (hi := (134513147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50157 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50157 / 25600) = 1/(25600 / 50157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (336282867 / 500000000) (134513147 / 200000000) (Real.log (50157 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50157 / 25600) = -Real.log (25600 / 50157) := by
    rw [show ((50157 / 25600) : ℝ) = ((25600 / 50157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3200491173 / 1000000000) ≤ -Real.log (1043 / 25600) ∧
    -Real.log (1043 / 25600) ≤ (1600245589 / 500000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1043) = 1/(1043 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1600245589 / 500000000) (-3200491173 / 1000000000) (Real.log (1043 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672471027 / 1000000000) ≤ -Real.log (102400 / 200609) ∧
    -Real.log (102400 / 200609) ≤ (168117757 / 250000000) := by
  have h := checkLog_sound (w := (98209 / 303009)) (n := 12)
    (lo := (672471027 / 1000000000)) (hi := (168117757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200609 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200609 / 102400) = 1/(102400 / 200609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672471027 / 1000000000) (168117757 / 250000000) (Real.log (200609 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200609 / 102400) = -Real.log (102400 / 200609) := by
    rw [show ((200609 / 102400) : ℝ) = ((102400 / 200609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3195947341 / 1000000000) ≤ -Real.log (4191 / 102400) ∧
    -Real.log (4191 / 102400) ≤ (1597973673 / 500000000) := by
  have h := checkLog_sound (w := (2209 / 10591)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4191) = 1/(4191 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1597973673 / 500000000) (-3195947341 / 1000000000) (Real.log (4191 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684413149 / 1000000000) ≤ -Real.log (62500 / 123913) ∧
    -Real.log (62500 / 123913) ≤ (13688263 / 20000000) := by
  have h := checkLog_sound (w := (61413 / 186413)) (n := 12)
    (lo := (684413149 / 1000000000)) (hi := (13688263 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123913 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123913 / 62500) = 1/(62500 / 123913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684413149 / 1000000000) (13688263 / 20000000) (Real.log (123913 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123913 / 62500) = -Real.log (62500 / 123913) := by
    rw [show ((123913 / 62500) : ℝ) = ((62500 / 123913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (810348989 / 200000000) ≤ -Real.log (1087 / 62500) ∧
    -Real.log (1087 / 62500) ≤ (4051744951 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 24321)) (n := 12)
    (lo := (117201809 / 200000000)) (hi := (293004523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8696) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8696) = 1/(1087 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4051744951 / 1000000000) (-810348989 / 200000000) (Real.log (1087 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342225741 / 500000000) ≤ -Real.log (250000 / 495671) ∧
    -Real.log (250000 / 495671) ≤ (684451483 / 1000000000) := by
  have h := checkLog_sound (w := (245671 / 745671)) (n := 12)
    (lo := (342225741 / 500000000)) (hi := (684451483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495671 / 250000) = 1/(250000 / 495671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342225741 / 500000000) (684451483 / 1000000000) (Real.log (495671 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495671 / 250000) = -Real.log (250000 / 495671) := by
    rw [show ((495671 / 250000) : ℝ) = ((250000 / 495671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2028062173 / 500000000) ≤ -Real.log (4329 / 250000) ∧
    -Real.log (4329 / 250000) ≤ (63376943 / 15625000) := by
  have h := checkLog_sound (w := (6967 / 24283)) (n := 12)
    (lo := (295194223 / 500000000)) (hi := (590388447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8658) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8658) = 1/(4329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-63376943 / 15625000) (-2028062173 / 500000000) (Real.log (4329 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171095091 / 250000000) ≤ -Real.log (1000000 / 1982543) ∧
    -Real.log (1000000 / 1982543) ≤ (136876073 / 200000000) := by
  have h := checkLog_sound (w := (982543 / 2982543)) (n := 12)
    (lo := (171095091 / 250000000)) (hi := (136876073 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982543 / 1000000) = 1/(1000000 / 1982543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171095091 / 250000000) (136876073 / 200000000) (Real.log (1982543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982543 / 1000000) = -Real.log (1000000 / 1982543) := by
    rw [show ((1982543 / 1000000) : ℝ) = ((1000000 / 1982543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4048014561 / 1000000000) ≤ -Real.log (17457 / 1000000) ∧
    -Real.log (17457 / 1000000) ≤ (4048014567 / 1000000000) := by
  have h := checkLog_sound (w := (13793 / 48707)) (n := 12)
    (lo := (582278661 / 1000000000)) (hi := (291139331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17457) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17457) = 1/(17457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4048014567 / 1000000000) (-4048014561 / 1000000000) (Real.log (17457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (342209601 / 500000000) ≤ -Real.log (50000 / 99131) ∧
    -Real.log (50000 / 99131) ≤ (684419203 / 1000000000) := by
  have h := checkLog_sound (w := (49131 / 149131)) (n := 12)
    (lo := (342209601 / 500000000)) (hi := (684419203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99131 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99131 / 50000) = 1/(50000 / 99131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (342209601 / 500000000) (684419203 / 1000000000) (Real.log (99131 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (99131 / 50000) = -Real.log (50000 / 99131) := by
    rw [show ((99131 / 50000) : ℝ) = ((50000 / 99131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1013108789 / 250000000) ≤ -Real.log (869 / 50000) ∧
    -Real.log (869 / 50000) ≤ (2026217581 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 4863)) (n := 12)
    (lo := (73337407 / 125000000)) (hi := (586699257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1738) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1738) = 1/(869 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2026217581 / 500000000) (-1013108789 / 250000000) (Real.log (869 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2368079047 / 500000000) ≤ -Real.log (125000000000 / 14249425022999) ∧
    -Real.log (125000000000 / 14249425022999) ≤ (4736158101 / 1000000000) := by
  have h := checkLog_sound (w := (6249425022999 / 22249425022999)) (n := 12)
    (lo := (288637507 / 500000000)) (hi := (115455003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14249425022999 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14249425022999 / 8000000000000) = 1/(125000000000 / 14249425022999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2368079047 / 500000000) (4736158101 / 1000000000) (Real.log (14249425022999 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14249425022999 / 125000000000) = -Real.log (125000000000 / 14249425022999) := by
    rw [show ((14249425022999 / 125000000000) : ℝ) = ((125000000000 / 14249425022999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1185143957 / 250000000) ≤ -Real.log (250000000000 / 28625028875029) ∧
    -Real.log (250000000000 / 28625028875029) ≤ (948115167 / 200000000) := by
  have h := checkLog_sound (w := (12625028875029 / 44625028875029)) (n := 12)
    (lo := (145423187 / 250000000)) (hi := (581692749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28625028875029 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28625028875029 / 16000000000000) = 1/(250000000000 / 28625028875029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1185143957 / 250000000) (948115167 / 200000000) (Real.log (28625028875029 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28625028875029 / 250000000000) = -Real.log (250000000000 / 28625028875029) := by
    rw [show ((28625028875029 / 250000000000) : ℝ) = ((250000000000 / 28625028875029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (189295797 / 40000000) ≤ -Real.log (500000000000 / 56783611158847) ∧
    -Real.log (500000000000 / 56783611158847) ≤ (1183098733 / 250000000) := by
  have h := checkLog_sound (w := (24783611158847 / 88783611158847)) (n := 12)
    (lo := (114702369 / 200000000)) (hi := (286755923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56783611158847 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56783611158847 / 32000000000000) = 1/(500000000000 / 56783611158847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (189295797 / 40000000) (1183098733 / 250000000) (Real.log (56783611158847 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56783611158847 / 500000000000) = -Real.log (500000000000 / 56783611158847) := by
    rw [show ((56783611158847 / 500000000000) : ℝ) = ((500000000000 / 56783611158847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2368427179 / 500000000) ≤ -Real.log (31250000000 / 3564837456847) ∧
    -Real.log (31250000000 / 3564837456847) ≤ (947370873 / 200000000) := by
  have h := checkLog_sound (w := (1564837456847 / 5564837456847)) (n := 12)
    (lo := (288985639 / 500000000)) (hi := (577971279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3564837456847 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3564837456847 / 2000000000000) = 1/(31250000000 / 3564837456847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2368427179 / 500000000) (947370873 / 200000000) (Real.log (3564837456847 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3564837456847 / 31250000000) = -Real.log (31250000000 / 3564837456847) := by
    rw [show ((3564837456847 / 31250000000) : ℝ) = ((31250000000 / 3564837456847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0004
