import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_960_neg : (6224517 / 1000000000) ≤ -Real.log (993794814471 / 1000000000000) ∧
    -Real.log (993794814471 / 1000000000000) ≤ (3112259 / 500000000) := by
  have h := checkLog_sound (w := (6205185529 / 1993794814471)) (n := 12)
    (lo := (6224517 / 1000000000)) (hi := (3112259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993794814471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993794814471) = 1/(993794814471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_960 : Bounds (-3112259 / 500000000) (-6224517 / 1000000000) (Real.log (993794814471 / 1000000000000)) := by
  have h := reflection_log_960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_961_neg : (78936543 / 500000000) ≤ -Real.log (250000000000 / 292754391697) ∧
    -Real.log (250000000000 / 292754391697) ≤ (157873087 / 1000000000) := by
  have h := checkLog_sound (w := (42754391697 / 542754391697)) (n := 12)
    (lo := (78936543 / 500000000)) (hi := (157873087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292754391697 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292754391697 / 250000000000) = 1/(250000000000 / 292754391697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_961 : Bounds (78936543 / 500000000) (157873087 / 1000000000) (Real.log (292754391697 / 250000000000)) := by
  have h := reflection_log_961_neg
  have he : Real.log (292754391697 / 250000000000) = -Real.log (250000000000 / 292754391697) := by
    rw [show ((292754391697 / 250000000000) : ℝ) = ((250000000000 / 292754391697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_962_neg : (15829169 / 100000000) ≤ -Real.log (125000000000 / 146438482811) ∧
    -Real.log (125000000000 / 146438482811) ≤ (158291691 / 1000000000) := by
  have h := checkLog_sound (w := (21438482811 / 271438482811)) (n := 12)
    (lo := (15829169 / 100000000)) (hi := (158291691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146438482811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146438482811 / 125000000000) = 1/(125000000000 / 146438482811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_962 : Bounds (15829169 / 100000000) (158291691 / 1000000000) (Real.log (146438482811 / 125000000000)) := by
  have h := reflection_log_962_neg
  have he : Real.log (146438482811 / 125000000000) = -Real.log (125000000000 / 146438482811) := by
    rw [show ((146438482811 / 125000000000) : ℝ) = ((125000000000 / 146438482811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_963_neg : (316618769 / 1000000000) ≤ -Real.log (500000000000 / 686239620403) ∧
    -Real.log (500000000000 / 686239620403) ≤ (31661877 / 100000000) := by
  have h := checkLog_sound (w := (186239620403 / 1186239620403)) (n := 12)
    (lo := (316618769 / 1000000000)) (hi := (31661877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686239620403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686239620403 / 500000000000) = 1/(500000000000 / 686239620403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_963 : Bounds (316618769 / 1000000000) (31661877 / 100000000) (Real.log (686239620403 / 500000000000)) := by
  have h := reflection_log_963_neg
  have he : Real.log (686239620403 / 500000000000) = -Real.log (500000000000 / 686239620403) := by
    rw [show ((686239620403 / 500000000000) : ℝ) = ((500000000000 / 686239620403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_964_neg : (158411913 / 500000000) ≤ -Real.log (250000000000 / 343190176771) ∧
    -Real.log (250000000000 / 343190176771) ≤ (316823827 / 1000000000) := by
  have h := checkLog_sound (w := (93190176771 / 593190176771)) (n := 12)
    (lo := (158411913 / 500000000)) (hi := (316823827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343190176771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343190176771 / 250000000000) = 1/(250000000000 / 343190176771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_964 : Bounds (158411913 / 500000000) (316823827 / 1000000000) (Real.log (343190176771 / 250000000000)) := by
  have h := reflection_log_964_neg
  have he : Real.log (343190176771 / 250000000000) = -Real.log (250000000000 / 343190176771) := by
    rw [show ((343190176771 / 250000000000) : ℝ) = ((250000000000 / 343190176771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_965_neg : (73001647 / 500000000) ≤ -Real.log (2500 / 2893) ∧
    -Real.log (2500 / 2893) ≤ (29200659 / 200000000) := by
  have h := checkLog_sound (w := (393 / 5393)) (n := 12)
    (lo := (73001647 / 500000000)) (hi := (29200659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2893 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2893 / 2500) = 1/(2500 / 2893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_965 : Bounds (73001647 / 500000000) (29200659 / 200000000) (Real.log (2893 / 2500)) := by
  have h := reflection_log_965_neg
  have he : Real.log (2893 / 2500) = -Real.log (2500 / 2893) := by
    rw [show ((2893 / 2500) : ℝ) = ((2500 / 2893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_966_neg : (171025597 / 1000000000) ≤ -Real.log (2107 / 2500) ∧
    -Real.log (2107 / 2500) ≤ (85512799 / 500000000) := by
  have h := checkLog_sound (w := (393 / 4607)) (n := 12)
    (lo := (171025597 / 1000000000)) (hi := (85512799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2107) = 1/(2107 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_966 : Bounds (-85512799 / 500000000) (-171025597 / 1000000000) (Real.log (2107 / 2500)) := by
  have h := reflection_log_966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_967_neg : (157187 / 1000000000) ≤ -Real.log (2500000 / 2500393) ∧
    -Real.log (2500000 / 2500393) ≤ (39297 / 250000000) := by
  have h := checkLog_sound (w := (393 / 5000393)) (n := 12)
    (lo := (157187 / 1000000000)) (hi := (39297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500393 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500393 / 2500000) = 1/(2500000 / 2500393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_967 : Bounds (157187 / 1000000000) (39297 / 250000000) (Real.log (2500393 / 2500000)) := by
  have h := reflection_log_967_neg
  have he : Real.log (2500393 / 2500000) = -Real.log (2500000 / 2500393) := by
    rw [show ((2500393 / 2500000) : ℝ) = ((2500000 / 2500393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_968_neg : (39303 / 250000000) ≤ -Real.log (2499607 / 2500000) ∧
    -Real.log (2499607 / 2500000) ≤ (157213 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4999607)) (n := 12)
    (lo := (39303 / 250000000)) (hi := (157213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499607) = 1/(2499607 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_968 : Bounds (-157213 / 1000000000) (-39303 / 250000000) (Real.log (2499607 / 2500000)) := by
  have h := reflection_log_968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_969_neg : (9483829 / 125000000) ≤ -Real.log (1000000 / 1078823) ∧
    -Real.log (1000000 / 1078823) ≤ (75870633 / 1000000000) := by
  have h := checkLog_sound (w := (78823 / 2078823)) (n := 12)
    (lo := (9483829 / 125000000)) (hi := (75870633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078823 / 1000000) = 1/(1000000 / 1078823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_969 : Bounds (9483829 / 125000000) (75870633 / 1000000000) (Real.log (1078823 / 1000000)) := by
  have h := reflection_log_969_neg
  have he : Real.log (1078823 / 1000000) = -Real.log (1000000 / 1078823) := by
    rw [show ((1078823 / 1000000) : ℝ) = ((1000000 / 1078823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_970_neg : (41051539 / 500000000) ≤ -Real.log (921177 / 1000000) ∧
    -Real.log (921177 / 1000000) ≤ (82103079 / 1000000000) := by
  have h := checkLog_sound (w := (78823 / 1921177)) (n := 12)
    (lo := (41051539 / 500000000)) (hi := (82103079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921177) = 1/(921177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_970 : Bounds (-82103079 / 1000000000) (-41051539 / 500000000) (Real.log (921177 / 1000000)) := by
  have h := reflection_log_970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_971_neg : (38032171 / 500000000) ≤ -Real.log (125000 / 134879) ∧
    -Real.log (125000 / 134879) ≤ (76064343 / 1000000000) := by
  have h := checkLog_sound (w := (9879 / 259879)) (n := 12)
    (lo := (38032171 / 500000000)) (hi := (76064343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134879 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134879 / 125000) = 1/(125000 / 134879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_971 : Bounds (38032171 / 500000000) (76064343 / 1000000000) (Real.log (134879 / 125000)) := by
  have h := reflection_log_971_neg
  have he : Real.log (134879 / 125000) = -Real.log (125000 / 134879) := by
    rw [show ((134879 / 125000) : ℝ) = ((125000 / 134879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_972_neg : (20582497 / 250000000) ≤ -Real.log (115121 / 125000) ∧
    -Real.log (115121 / 125000) ≤ (82329989 / 1000000000) := by
  have h := checkLog_sound (w := (9879 / 240121)) (n := 12)
    (lo := (20582497 / 250000000)) (hi := (82329989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115121) = 1/(115121 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_972 : Bounds (-82329989 / 1000000000) (-20582497 / 250000000) (Real.log (115121 / 125000)) := by
  have h := reflection_log_972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_973_neg : (1253129 / 200000000) ≤ -Real.log (15527405359 / 15625000000) ∧
    -Real.log (15527405359 / 15625000000) ≤ (3132823 / 500000000) := by
  have h := checkLog_sound (w := (97594641 / 31152405359)) (n := 12)
    (lo := (1253129 / 200000000)) (hi := (3132823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15527405359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15527405359) = 1/(15527405359 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_973 : Bounds (-3132823 / 500000000) (-1253129 / 200000000) (Real.log (15527405359 / 15625000000)) := by
  have h := reflection_log_973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_974_neg : (3116223 / 500000000) ≤ -Real.log (993786934671 / 1000000000000) ∧
    -Real.log (993786934671 / 1000000000000) ≤ (6232447 / 1000000000) := by
  have h := checkLog_sound (w := (6213065329 / 1993786934671)) (n := 12)
    (lo := (3116223 / 500000000)) (hi := (6232447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993786934671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993786934671) = 1/(993786934671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_974 : Bounds (-6232447 / 1000000000) (-3116223 / 500000000) (Real.log (993786934671 / 1000000000000)) := by
  have h := reflection_log_974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_975_neg : (15797371 / 100000000) ≤ -Real.log (250000000000 / 292783851529) ∧
    -Real.log (250000000000 / 292783851529) ≤ (157973711 / 1000000000) := by
  have h := checkLog_sound (w := (42783851529 / 542783851529)) (n := 12)
    (lo := (15797371 / 100000000)) (hi := (157973711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292783851529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292783851529 / 250000000000) = 1/(250000000000 / 292783851529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_975 : Bounds (15797371 / 100000000) (157973711 / 1000000000) (Real.log (292783851529 / 250000000000)) := by
  have h := reflection_log_975_neg
  have he : Real.log (292783851529 / 250000000000) = -Real.log (250000000000 / 292783851529) := by
    rw [show ((292783851529 / 250000000000) : ℝ) = ((250000000000 / 292783851529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_976_neg : (158394331 / 1000000000) ≤ -Real.log (100000000000 / 117162811303) ∧
    -Real.log (100000000000 / 117162811303) ≤ (39598583 / 250000000) := by
  have h := checkLog_sound (w := (17162811303 / 217162811303)) (n := 12)
    (lo := (158394331 / 1000000000)) (hi := (39598583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117162811303 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117162811303 / 100000000000) = 1/(100000000000 / 117162811303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_976 : Bounds (158394331 / 1000000000) (39598583 / 250000000) (Real.log (117162811303 / 100000000000)) := by
  have h := reflection_log_976_neg
  have he : Real.log (117162811303 / 100000000000) = -Real.log (100000000000 / 117162811303) := by
    rw [show ((117162811303 / 100000000000) : ℝ) = ((100000000000 / 117162811303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_977_neg : (158411913 / 500000000) ≤ -Real.log (500000000000 / 686380353541) ∧
    -Real.log (500000000000 / 686380353541) ≤ (316823827 / 1000000000) := by
  have h := checkLog_sound (w := (186380353541 / 1186380353541)) (n := 12)
    (lo := (158411913 / 500000000)) (hi := (316823827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686380353541 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686380353541 / 500000000000) = 1/(500000000000 / 686380353541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_977 : Bounds (158411913 / 500000000) (316823827 / 1000000000) (Real.log (686380353541 / 500000000000)) := by
  have h := reflection_log_977_neg
  have he : Real.log (686380353541 / 500000000000) = -Real.log (500000000000 / 686380353541) := by
    rw [show ((686380353541 / 500000000000) : ℝ) = ((500000000000 / 686380353541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_978_neg : (317028891 / 1000000000) ≤ -Real.log (125000000000 / 171630280019) ∧
    -Real.log (125000000000 / 171630280019) ≤ (79257223 / 250000000) := by
  have h := checkLog_sound (w := (46630280019 / 296630280019)) (n := 12)
    (lo := (317028891 / 1000000000)) (hi := (79257223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171630280019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171630280019 / 125000000000) = 1/(125000000000 / 171630280019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_978 : Bounds (317028891 / 1000000000) (79257223 / 250000000) (Real.log (171630280019 / 125000000000)) := by
  have h := reflection_log_978_neg
  have he : Real.log (171630280019 / 125000000000) = -Real.log (125000000000 / 171630280019) := by
    rw [show ((171630280019 / 125000000000) : ℝ) = ((125000000000 / 171630280019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_979_neg : (29217941 / 200000000) ≤ -Real.log (10000 / 11573) ∧
    -Real.log (10000 / 11573) ≤ (73044853 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 21573)) (n := 12)
    (lo := (29217941 / 200000000)) (hi := (73044853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11573 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11573 / 10000) = 1/(10000 / 11573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_979 : Bounds (29217941 / 200000000) (73044853 / 500000000) (Real.log (11573 / 10000)) := by
  have h := reflection_log_979_neg
  have he : Real.log (11573 / 10000) = -Real.log (10000 / 11573) := by
    rw [show ((11573 / 10000) : ℝ) = ((10000 / 11573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_980_neg : (2674129 / 15625000) ≤ -Real.log (8427 / 10000) ∧
    -Real.log (8427 / 10000) ≤ (171144257 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 18427)) (n := 12)
    (lo := (2674129 / 15625000)) (hi := (171144257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8427) = 1/(8427 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_980 : Bounds (-171144257 / 1000000000) (-2674129 / 15625000) (Real.log (8427 / 10000)) := by
  have h := reflection_log_980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_981_neg : (157287 / 1000000000) ≤ -Real.log (10000000 / 10001573) ∧
    -Real.log (10000000 / 10001573) ≤ (19661 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 20001573)) (n := 12)
    (lo := (157287 / 1000000000)) (hi := (19661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001573 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001573 / 10000000) = 1/(10000000 / 10001573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_981 : Bounds (157287 / 1000000000) (19661 / 125000000) (Real.log (10001573 / 10000000)) := by
  have h := reflection_log_981_neg
  have he : Real.log (10001573 / 10000000) = -Real.log (10000000 / 10001573) := by
    rw [show ((10001573 / 10000000) : ℝ) = ((10000000 / 10001573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_982_neg : (1229 / 7812500) ≤ -Real.log (9998427 / 10000000) ∧
    -Real.log (9998427 / 10000000) ≤ (157313 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 19998427)) (n := 12)
    (lo := (1229 / 7812500)) (hi := (157313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998427) = 1/(9998427 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_982 : Bounds (-157313 / 1000000000) (-1229 / 7812500) (Real.log (9998427 / 10000000)) := by
  have h := reflection_log_982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_983_neg : (4744869 / 62500000) ≤ -Real.log (500000 / 539437) ∧
    -Real.log (500000 / 539437) ≤ (15183581 / 200000000) := by
  have h := checkLog_sound (w := (39437 / 1039437)) (n := 12)
    (lo := (4744869 / 62500000)) (hi := (15183581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539437 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539437 / 500000) = 1/(500000 / 539437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_983 : Bounds (4744869 / 62500000) (15183581 / 200000000) (Real.log (539437 / 500000)) := by
  have h := reflection_log_983_neg
  have he : Real.log (539437 / 500000) = -Real.log (500000 / 539437) := by
    rw [show ((539437 / 500000) : ℝ) = ((500000 / 539437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_984_neg : (20539611 / 250000000) ≤ -Real.log (460563 / 500000) ∧
    -Real.log (460563 / 500000) ≤ (16431689 / 200000000) := by
  have h := checkLog_sound (w := (39437 / 960563)) (n := 12)
    (lo := (20539611 / 250000000)) (hi := (16431689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460563) = 1/(460563 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_984 : Bounds (-16431689 / 200000000) (-20539611 / 250000000) (Real.log (460563 / 500000)) := by
  have h := reflection_log_984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_985_neg : (76110679 / 1000000000) ≤ -Real.log (500000 / 539541) ∧
    -Real.log (500000 / 539541) ≤ (1902767 / 25000000) := by
  have h := checkLog_sound (w := (39541 / 1039541)) (n := 12)
    (lo := (76110679 / 1000000000)) (hi := (1902767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539541 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539541 / 500000) = 1/(500000 / 539541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_985 : Bounds (76110679 / 1000000000) (1902767 / 25000000) (Real.log (539541 / 500000)) := by
  have h := reflection_log_985_neg
  have he : Real.log (539541 / 500000) = -Real.log (500000 / 539541) := by
    rw [show ((539541 / 500000) : ℝ) = ((500000 / 539541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_986_neg : (2059607 / 25000000) ≤ -Real.log (460459 / 500000) ∧
    -Real.log (460459 / 500000) ≤ (82384281 / 1000000000) := by
  have h := checkLog_sound (w := (39541 / 960459)) (n := 12)
    (lo := (2059607 / 25000000)) (hi := (82384281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460459) = 1/(460459 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_986 : Bounds (-82384281 / 1000000000) (-2059607 / 25000000) (Real.log (460459 / 500000)) := by
  have h := reflection_log_986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_987_neg : (3921 / 625000) ≤ -Real.log (248436509319 / 250000000000) ∧
    -Real.log (248436509319 / 250000000000) ≤ (6273601 / 1000000000) := by
  have h := checkLog_sound (w := (1563490681 / 498436509319)) (n := 12)
    (lo := (3921 / 625000)) (hi := (6273601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248436509319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248436509319) = 1/(248436509319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_987 : Bounds (-6273601 / 1000000000) (-3921 / 625000) (Real.log (248436509319 / 250000000000)) := by
  have h := reflection_log_987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_988_neg : (6240539 / 1000000000) ≤ -Real.log (248444723031 / 250000000000) ∧
    -Real.log (248444723031 / 250000000000) ≤ (312027 / 50000000) := by
  have h := checkLog_sound (w := (1555276969 / 498444723031)) (n := 12)
    (lo := (6240539 / 1000000000)) (hi := (312027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248444723031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248444723031) = 1/(248444723031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_988 : Bounds (-312027 / 50000000) (-6240539 / 1000000000) (Real.log (248444723031 / 250000000000)) := by
  have h := reflection_log_988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_989_neg : (39519087 / 250000000) ≤ -Real.log (62500000000 / 73203475963) ∧
    -Real.log (62500000000 / 73203475963) ≤ (158076349 / 1000000000) := by
  have h := checkLog_sound (w := (10703475963 / 135703475963)) (n := 12)
    (lo := (39519087 / 250000000)) (hi := (158076349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73203475963 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73203475963 / 62500000000) = 1/(62500000000 / 73203475963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_989 : Bounds (39519087 / 250000000) (158076349 / 1000000000) (Real.log (73203475963 / 62500000000)) := by
  have h := reflection_log_989_neg
  have he : Real.log (73203475963 / 62500000000) = -Real.log (62500000000 / 73203475963) := by
    rw [show ((73203475963 / 62500000000) : ℝ) = ((62500000000 / 73203475963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_990_neg : (1981187 / 12500000) ≤ -Real.log (125000000000 / 146468252331) ∧
    -Real.log (125000000000 / 146468252331) ≤ (158494961 / 1000000000) := by
  have h := checkLog_sound (w := (21468252331 / 271468252331)) (n := 12)
    (lo := (1981187 / 12500000)) (hi := (158494961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146468252331 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146468252331 / 125000000000) = 1/(125000000000 / 146468252331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_990 : Bounds (1981187 / 12500000) (158494961 / 1000000000) (Real.log (146468252331 / 125000000000)) := by
  have h := reflection_log_990_neg
  have he : Real.log (146468252331 / 125000000000) = -Real.log (125000000000 / 146468252331) := by
    rw [show ((146468252331 / 125000000000) : ℝ) = ((125000000000 / 146468252331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_991_neg : (317028891 / 1000000000) ≤ -Real.log (20000000000 / 27460844803) ∧
    -Real.log (20000000000 / 27460844803) ≤ (79257223 / 250000000) := by
  have h := checkLog_sound (w := (7460844803 / 47460844803)) (n := 12)
    (lo := (317028891 / 1000000000)) (hi := (79257223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27460844803 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27460844803 / 20000000000) = 1/(20000000000 / 27460844803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_991 : Bounds (317028891 / 1000000000) (79257223 / 250000000) (Real.log (27460844803 / 20000000000)) := by
  have h := reflection_log_991_neg
  have he : Real.log (27460844803 / 20000000000) = -Real.log (20000000000 / 27460844803) := by
    rw [show ((27460844803 / 20000000000) : ℝ) = ((20000000000 / 27460844803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_992_neg : (158616981 / 500000000) ≤ -Real.log (500000000000 / 686661920019) ∧
    -Real.log (500000000000 / 686661920019) ≤ (317233963 / 1000000000) := by
  have h := checkLog_sound (w := (186661920019 / 1186661920019)) (n := 12)
    (lo := (158616981 / 500000000)) (hi := (317233963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686661920019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686661920019 / 500000000000) = 1/(500000000000 / 686661920019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_992 : Bounds (158616981 / 500000000) (317233963 / 1000000000) (Real.log (686661920019 / 500000000000)) := by
  have h := reflection_log_992_neg
  have he : Real.log (686661920019 / 500000000000) = -Real.log (500000000000 / 686661920019) := by
    rw [show ((686661920019 / 500000000000) : ℝ) = ((500000000000 / 686661920019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_993_neg : (14617611 / 100000000) ≤ -Real.log (5000 / 5787) ∧
    -Real.log (5000 / 5787) ≤ (146176111 / 1000000000) := by
  have h := checkLog_sound (w := (787 / 10787)) (n := 12)
    (lo := (14617611 / 100000000)) (hi := (146176111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5787 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5787 / 5000) = 1/(5000 / 5787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_993 : Bounds (14617611 / 100000000) (146176111 / 1000000000) (Real.log (5787 / 5000)) := by
  have h := reflection_log_993_neg
  have he : Real.log (5787 / 5000) = -Real.log (5000 / 5787) := by
    rw [show ((5787 / 5000) : ℝ) = ((5000 / 5787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_994_neg : (171262929 / 1000000000) ≤ -Real.log (4213 / 5000) ∧
    -Real.log (4213 / 5000) ≤ (17126293 / 100000000) := by
  have h := checkLog_sound (w := (787 / 9213)) (n := 12)
    (lo := (171262929 / 1000000000)) (hi := (17126293 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4213) = 1/(4213 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_994 : Bounds (-17126293 / 100000000) (-171262929 / 1000000000) (Real.log (4213 / 5000)) := by
  have h := reflection_log_994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_995_neg : (157387 / 1000000000) ≤ -Real.log (5000000 / 5000787) ∧
    -Real.log (5000000 / 5000787) ≤ (39347 / 250000000) := by
  have h := checkLog_sound (w := (787 / 10000787)) (n := 12)
    (lo := (157387 / 1000000000)) (hi := (39347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000787 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000787 / 5000000) = 1/(5000000 / 5000787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_995 : Bounds (157387 / 1000000000) (39347 / 250000000) (Real.log (5000787 / 5000000)) := by
  have h := reflection_log_995_neg
  have he : Real.log (5000787 / 5000000) = -Real.log (5000000 / 5000787) := by
    rw [show ((5000787 / 5000000) : ℝ) = ((5000000 / 5000787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_996_neg : (39353 / 250000000) ≤ -Real.log (4999213 / 5000000) ∧
    -Real.log (4999213 / 5000000) ≤ (157413 / 1000000000) := by
  have h := checkLog_sound (w := (787 / 9999213)) (n := 12)
    (lo := (39353 / 250000000)) (hi := (157413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999213) = 1/(4999213 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_996 : Bounds (-157413 / 1000000000) (-39353 / 250000000) (Real.log (4999213 / 5000000)) := by
  have h := reflection_log_996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_997_neg : (3038607 / 40000000) ≤ -Real.log (40000 / 43157) ∧
    -Real.log (40000 / 43157) ≤ (9495647 / 125000000) := by
  have h := checkLog_sound (w := (3157 / 83157)) (n := 12)
    (lo := (3038607 / 40000000)) (hi := (9495647 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43157 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43157 / 40000) = 1/(40000 / 43157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_997 : Bounds (3038607 / 40000000) (9495647 / 125000000) (Real.log (43157 / 40000)) := by
  have h := reflection_log_997_neg
  have he : Real.log (43157 / 40000) = -Real.log (40000 / 43157) := by
    rw [show ((43157 / 40000) : ℝ) = ((40000 / 43157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_998_neg : (20553453 / 250000000) ≤ -Real.log (36843 / 40000) ∧
    -Real.log (36843 / 40000) ≤ (82213813 / 1000000000) := by
  have h := checkLog_sound (w := (3157 / 76843)) (n := 12)
    (lo := (20553453 / 250000000)) (hi := (82213813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36843) = 1/(36843 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_998 : Bounds (-82213813 / 1000000000) (-20553453 / 250000000) (Real.log (36843 / 40000)) := by
  have h := reflection_log_998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_999_neg : (3807897 / 50000000) ≤ -Real.log (1000000 / 1079133) ∧
    -Real.log (1000000 / 1079133) ≤ (76157941 / 1000000000) := by
  have h := checkLog_sound (w := (79133 / 2079133)) (n := 12)
    (lo := (3807897 / 50000000)) (hi := (76157941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079133 / 1000000) = 1/(1000000 / 1079133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_999 : Bounds (3807897 / 50000000) (76157941 / 1000000000) (Real.log (1079133 / 1000000)) := by
  have h := reflection_log_999_neg
  have he : Real.log (1079133 / 1000000) = -Real.log (1000000 / 1079133) := by
    rw [show ((1079133 / 1000000) : ℝ) = ((1000000 / 1079133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1000_neg : (82439661 / 1000000000) ≤ -Real.log (920867 / 1000000) ∧
    -Real.log (920867 / 1000000) ≤ (41219831 / 500000000) := by
  have h := checkLog_sound (w := (79133 / 1920867)) (n := 12)
    (lo := (82439661 / 1000000000)) (hi := (41219831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920867) = 1/(920867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1000 : Bounds (-41219831 / 500000000) (-82439661 / 1000000000) (Real.log (920867 / 1000000)) := by
  have h := reflection_log_1000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1001_neg : (157043 / 25000000) ≤ -Real.log (993737968311 / 1000000000000) ∧
    -Real.log (993737968311 / 1000000000000) ≤ (6281721 / 1000000000) := by
  have h := checkLog_sound (w := (6262031689 / 1993737968311)) (n := 12)
    (lo := (157043 / 25000000)) (hi := (6281721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993737968311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993737968311) = 1/(993737968311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1001 : Bounds (-6281721 / 1000000000) (-157043 / 25000000) (Real.log (993737968311 / 1000000000000)) := by
  have h := reflection_log_1001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1002_neg : (6248637 / 1000000000) ≤ -Real.log (1590033351 / 1600000000) ∧
    -Real.log (1590033351 / 1600000000) ≤ (3124319 / 500000000) := by
  have h := checkLog_sound (w := (9966649 / 3190033351)) (n := 12)
    (lo := (6248637 / 1000000000)) (hi := (3124319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590033351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590033351) = 1/(1590033351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1002 : Bounds (-3124319 / 500000000) (-6248637 / 1000000000) (Real.log (1590033351 / 1600000000)) := by
  have h := reflection_log_1002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1003_neg : (158178987 / 1000000000) ≤ -Real.log (500000000000 / 585687919007) ∧
    -Real.log (500000000000 / 585687919007) ≤ (39544747 / 250000000) := by
  have h := checkLog_sound (w := (85687919007 / 1085687919007)) (n := 12)
    (lo := (158178987 / 1000000000)) (hi := (39544747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585687919007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585687919007 / 500000000000) = 1/(500000000000 / 585687919007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1003 : Bounds (158178987 / 1000000000) (39544747 / 250000000) (Real.log (585687919007 / 500000000000)) := by
  have h := reflection_log_1003_neg
  have he : Real.log (585687919007 / 500000000000) = -Real.log (500000000000 / 585687919007) := by
    rw [show ((585687919007 / 500000000000) : ℝ) = ((500000000000 / 585687919007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1004_neg : (79298801 / 500000000) ≤ -Real.log (62500000000 / 73241643473) ∧
    -Real.log (62500000000 / 73241643473) ≤ (158597603 / 1000000000) := by
  have h := checkLog_sound (w := (10741643473 / 135741643473)) (n := 12)
    (lo := (79298801 / 500000000)) (hi := (158597603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73241643473 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73241643473 / 62500000000) = 1/(62500000000 / 73241643473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1004 : Bounds (79298801 / 500000000) (158597603 / 1000000000) (Real.log (73241643473 / 62500000000)) := by
  have h := reflection_log_1004_neg
  have he : Real.log (73241643473 / 62500000000) = -Real.log (62500000000 / 73241643473) := by
    rw [show ((73241643473 / 62500000000) : ℝ) = ((62500000000 / 73241643473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1005_neg : (158616981 / 500000000) ≤ -Real.log (250000000000 / 343330960009) ∧
    -Real.log (250000000000 / 343330960009) ≤ (317233963 / 1000000000) := by
  have h := checkLog_sound (w := (93330960009 / 593330960009)) (n := 12)
    (lo := (158616981 / 500000000)) (hi := (317233963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343330960009 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343330960009 / 250000000000) = 1/(250000000000 / 343330960009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1005 : Bounds (158616981 / 500000000) (317233963 / 1000000000) (Real.log (343330960009 / 250000000000)) := by
  have h := reflection_log_1005_neg
  have he : Real.log (343330960009 / 250000000000) = -Real.log (250000000000 / 343330960009) := by
    rw [show ((343330960009 / 250000000000) : ℝ) = ((250000000000 / 343330960009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1006_neg : (317439039 / 1000000000) ≤ -Real.log (500000000000 / 686802753383) ∧
    -Real.log (500000000000 / 686802753383) ≤ (991997 / 3125000) := by
  have h := checkLog_sound (w := (186802753383 / 1186802753383)) (n := 12)
    (lo := (317439039 / 1000000000)) (hi := (991997 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686802753383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686802753383 / 500000000000) = 1/(500000000000 / 686802753383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1006 : Bounds (317439039 / 1000000000) (991997 / 3125000) (Real.log (686802753383 / 500000000000)) := by
  have h := reflection_log_1006_neg
  have he : Real.log (686802753383 / 500000000000) = -Real.log (500000000000 / 686802753383) := by
    rw [show ((686802753383 / 500000000000) : ℝ) = ((500000000000 / 686802753383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1007_neg : (73131253 / 500000000) ≤ -Real.log (400 / 463) ∧
    -Real.log (400 / 463) ≤ (146262507 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 863)) (n := 12)
    (lo := (73131253 / 500000000)) (hi := (146262507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 400) = 1/(400 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1007 : Bounds (73131253 / 500000000) (146262507 / 1000000000) (Real.log (463 / 400)) := by
  have h := reflection_log_1007_neg
  have he : Real.log (463 / 400) = -Real.log (400 / 463) := by
    rw [show ((463 / 400) : ℝ) = ((400 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1008_neg : (10711351 / 62500000) ≤ -Real.log (337 / 400) ∧
    -Real.log (337 / 400) ≤ (171381617 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 737)) (n := 12)
    (lo := (10711351 / 62500000)) (hi := (171381617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 337) = 1/(337 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1008 : Bounds (-171381617 / 1000000000) (-10711351 / 62500000) (Real.log (337 / 400)) := by
  have h := reflection_log_1008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1009_neg : (157487 / 1000000000) ≤ -Real.log (400000 / 400063) ∧
    -Real.log (400000 / 400063) ≤ (9843 / 62500000) := by
  have h := checkLog_sound (w := (63 / 800063)) (n := 12)
    (lo := (157487 / 1000000000)) (hi := (9843 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400063 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400063 / 400000) = 1/(400000 / 400063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1009 : Bounds (157487 / 1000000000) (9843 / 62500000) (Real.log (400063 / 400000)) := by
  have h := reflection_log_1009_neg
  have he : Real.log (400063 / 400000) = -Real.log (400000 / 400063) := by
    rw [show ((400063 / 400000) : ℝ) = ((400000 / 400063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1010_neg : (19689 / 125000000) ≤ -Real.log (399937 / 400000) ∧
    -Real.log (399937 / 400000) ≤ (157513 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 799937)) (n := 12)
    (lo := (19689 / 125000000)) (hi := (157513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399937) = 1/(399937 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1010 : Bounds (-157513 / 1000000000) (-19689 / 125000000) (Real.log (399937 / 400000)) := by
  have h := reflection_log_1010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1011_neg : (19002879 / 250000000) ≤ -Real.log (40000 / 43159) ∧
    -Real.log (40000 / 43159) ≤ (76011517 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 83159)) (n := 12)
    (lo := (19002879 / 250000000)) (hi := (76011517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43159 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43159 / 40000) = 1/(40000 / 43159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1011 : Bounds (19002879 / 250000000) (76011517 / 1000000000) (Real.log (43159 / 40000)) := by
  have h := reflection_log_1011_neg
  have he : Real.log (43159 / 40000) = -Real.log (40000 / 43159) := by
    rw [show ((43159 / 40000) : ℝ) = ((40000 / 43159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1012_neg : (41134049 / 500000000) ≤ -Real.log (36841 / 40000) ∧
    -Real.log (36841 / 40000) ≤ (82268099 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 76841)) (n := 12)
    (lo := (41134049 / 500000000)) (hi := (82268099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36841) = 1/(36841 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1012 : Bounds (-82268099 / 1000000000) (-41134049 / 500000000) (Real.log (36841 / 40000)) := by
  have h := reflection_log_1012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1013_neg : (190513 / 2500000) ≤ -Real.log (62500 / 67449) ∧
    -Real.log (62500 / 67449) ≤ (76205201 / 1000000000) := by
  have h := checkLog_sound (w := (4949 / 129949)) (n := 12)
    (lo := (190513 / 2500000)) (hi := (76205201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67449 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67449 / 62500) = 1/(62500 / 67449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1013 : Bounds (190513 / 2500000) (76205201 / 1000000000) (Real.log (67449 / 62500)) := by
  have h := reflection_log_1013_neg
  have he : Real.log (67449 / 62500) = -Real.log (62500 / 67449) := by
    rw [show ((67449 / 62500) : ℝ) = ((62500 / 67449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1014_neg : (16499009 / 200000000) ≤ -Real.log (57551 / 62500) ∧
    -Real.log (57551 / 62500) ≤ (41247523 / 500000000) := by
  have h := checkLog_sound (w := (4949 / 120051)) (n := 12)
    (lo := (16499009 / 200000000)) (hi := (41247523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57551) = 1/(57551 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1014 : Bounds (-41247523 / 500000000) (-16499009 / 200000000) (Real.log (57551 / 62500)) := by
  have h := reflection_log_1014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1015_neg : (1257969 / 200000000) ≤ -Real.log (3881757399 / 3906250000) ∧
    -Real.log (3881757399 / 3906250000) ≤ (3144923 / 500000000) := by
  have h := checkLog_sound (w := (24492601 / 7788007399)) (n := 12)
    (lo := (1257969 / 200000000)) (hi := (3144923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3881757399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3881757399) = 1/(3881757399 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1015 : Bounds (-3144923 / 500000000) (-1257969 / 200000000) (Real.log (3881757399 / 3906250000)) := by
  have h := reflection_log_1015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1016_neg : (3128291 / 500000000) ≤ -Real.log (1590020719 / 1600000000) ∧
    -Real.log (1590020719 / 1600000000) ≤ (6256583 / 1000000000) := by
  have h := checkLog_sound (w := (9979281 / 3190020719)) (n := 12)
    (lo := (3128291 / 500000000)) (hi := (6256583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1590020719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1590020719) = 1/(1590020719 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1016 : Bounds (-6256583 / 1000000000) (-3128291 / 500000000) (Real.log (1590020719 / 1600000000)) := by
  have h := reflection_log_1016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1017_neg : (31655923 / 200000000) ≤ -Real.log (12500000000 / 14643671453) ∧
    -Real.log (12500000000 / 14643671453) ≤ (2473119 / 15625000) := by
  have h := checkLog_sound (w := (2143671453 / 27143671453)) (n := 12)
    (lo := (31655923 / 200000000)) (hi := (2473119 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14643671453 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14643671453 / 12500000000) = 1/(12500000000 / 14643671453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1017 : Bounds (31655923 / 200000000) (2473119 / 15625000) (Real.log (14643671453 / 12500000000)) := by
  have h := reflection_log_1017_neg
  have he : Real.log (14643671453 / 12500000000) = -Real.log (12500000000 / 14643671453) := by
    rw [show ((14643671453 / 12500000000) : ℝ) = ((12500000000 / 14643671453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1018_neg : (31740049 / 200000000) ≤ -Real.log (250000000000 / 292996646453) ∧
    -Real.log (250000000000 / 292996646453) ≤ (79350123 / 500000000) := by
  have h := checkLog_sound (w := (42996646453 / 542996646453)) (n := 12)
    (lo := (31740049 / 200000000)) (hi := (79350123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292996646453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292996646453 / 250000000000) = 1/(250000000000 / 292996646453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1018 : Bounds (31740049 / 200000000) (79350123 / 500000000) (Real.log (292996646453 / 250000000000)) := by
  have h := reflection_log_1018_neg
  have he : Real.log (292996646453 / 250000000000) = -Real.log (250000000000 / 292996646453) := by
    rw [show ((292996646453 / 250000000000) : ℝ) = ((250000000000 / 292996646453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1019_neg : (317439039 / 1000000000) ≤ -Real.log (250000000000 / 343401376691) ∧
    -Real.log (250000000000 / 343401376691) ≤ (991997 / 3125000) := by
  have h := checkLog_sound (w := (93401376691 / 593401376691)) (n := 12)
    (lo := (317439039 / 1000000000)) (hi := (991997 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343401376691 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343401376691 / 250000000000) = 1/(250000000000 / 343401376691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1019 : Bounds (317439039 / 1000000000) (991997 / 3125000) (Real.log (343401376691 / 250000000000)) := by
  have h := reflection_log_1019_neg
  have he : Real.log (343401376691 / 250000000000) = -Real.log (250000000000 / 343401376691) := by
    rw [show ((343401376691 / 250000000000) : ℝ) = ((250000000000 / 343401376691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1020_neg : (317644123 / 1000000000) ≤ -Real.log (500000000000 / 686943620179) ∧
    -Real.log (500000000000 / 686943620179) ≤ (79411031 / 250000000) := by
  have h := checkLog_sound (w := (186943620179 / 1186943620179)) (n := 12)
    (lo := (317644123 / 1000000000)) (hi := (79411031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686943620179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686943620179 / 500000000000) = 1/(500000000000 / 686943620179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1020 : Bounds (317644123 / 1000000000) (79411031 / 250000000) (Real.log (686943620179 / 500000000000)) := by
  have h := reflection_log_1020_neg
  have he : Real.log (686943620179 / 500000000000) = -Real.log (500000000000 / 686943620179) := by
    rw [show ((686943620179 / 500000000000) : ℝ) = ((500000000000 / 686943620179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1021_neg : (4573403 / 31250000) ≤ -Real.log (1250 / 1447) ∧
    -Real.log (1250 / 1447) ≤ (146348897 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2697)) (n := 12)
    (lo := (4573403 / 31250000)) (hi := (146348897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447 / 1250) = 1/(1250 / 1447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1021 : Bounds (4573403 / 31250000) (146348897 / 1000000000) (Real.log (1447 / 1250)) := by
  have h := reflection_log_1021_neg
  have he : Real.log (1447 / 1250) = -Real.log (1250 / 1447) := by
    rw [show ((1447 / 1250) : ℝ) = ((1250 / 1447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1022_neg : (85750159 / 500000000) ≤ -Real.log (1053 / 1250) ∧
    -Real.log (1053 / 1250) ≤ (171500319 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2303)) (n := 12)
    (lo := (85750159 / 500000000)) (hi := (171500319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1053) = 1/(1053 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1022 : Bounds (-171500319 / 1000000000) (-85750159 / 500000000) (Real.log (1053 / 1250)) := by
  have h := reflection_log_1022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1023_neg : (157587 / 1000000000) ≤ -Real.log (1250000 / 1250197) ∧
    -Real.log (1250000 / 1250197) ≤ (39397 / 250000000) := by
  have h := checkLog_sound (w := (197 / 2500197)) (n := 12)
    (lo := (157587 / 1000000000)) (hi := (39397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250197 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250197 / 1250000) = 1/(1250000 / 1250197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1023 : Bounds (157587 / 1000000000) (39397 / 250000000) (Real.log (1250197 / 1250000)) := by
  have h := reflection_log_1023_neg
  have he : Real.log (1250197 / 1250000) = -Real.log (1250000 / 1250197) := by
    rw [show ((1250197 / 1250000) : ℝ) = ((1250000 / 1250197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
