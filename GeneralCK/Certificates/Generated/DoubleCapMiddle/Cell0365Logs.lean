import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0365
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

theorem reflection_log_1_neg : (104292481 / 500000000) ≤ -Real.log (2048 / 2523) ∧
    -Real.log (2048 / 2523) ≤ (208584963 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 4571)) (n := 12)
    (lo := (104292481 / 500000000)) (hi := (208584963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2048) = 1/(2048 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104292481 / 500000000) (208584963 / 1000000000) (Real.log (2523 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2523 / 2048) = -Real.log (2048 / 2523) := by
    rw [show ((2523 / 2048) : ℝ) = ((2048 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (263879083 / 1000000000) ≤ -Real.log (1573 / 2048) ∧
    -Real.log (1573 / 2048) ≤ (65969771 / 250000000) := by
  have h := checkLog_sound (w := (475 / 3621)) (n := 12)
    (lo := (263879083 / 1000000000)) (hi := (65969771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1573) = 1/(1573 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65969771 / 250000000) (-263879083 / 1000000000) (Real.log (1573 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104173561 / 500000000) ≤ -Real.log (2560 / 3153) ∧
    -Real.log (2560 / 3153) ≤ (208347123 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 5713)) (n := 12)
    (lo := (104173561 / 500000000)) (hi := (208347123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3153 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3153 / 2560) = 1/(2560 / 3153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104173561 / 500000000) (208347123 / 1000000000) (Real.log (3153 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3153 / 2560) = -Real.log (2560 / 3153) := by
    rw [show ((3153 / 2560) : ℝ) = ((2560 / 3153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (263497719 / 1000000000) ≤ -Real.log (1967 / 2560) ∧
    -Real.log (1967 / 2560) ≤ (6587443 / 25000000) := by
  have h := checkLog_sound (w := (593 / 4527)) (n := 12)
    (lo := (263497719 / 1000000000)) (hi := (6587443 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1967) = 1/(1967 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6587443 / 25000000) (-263497719 / 1000000000) (Real.log (1967 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95270423 / 250000000) ≤ -Real.log (1024 / 1499) ∧
    -Real.log (1024 / 1499) ≤ (381081693 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 2523)) (n := 12)
    (lo := (95270423 / 250000000)) (hi := (381081693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1024) = 1/(1024 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95270423 / 250000000) (381081693 / 1000000000) (Real.log (1499 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1499 / 1024) = -Real.log (1024 / 1499) := by
    rw [show ((1499 / 1024) : ℝ) = ((1024 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155843341 / 250000000) ≤ -Real.log (549 / 1024) ∧
    -Real.log (549 / 1024) ≤ (124674673 / 200000000) := by
  have h := checkLog_sound (w := (475 / 1573)) (n := 12)
    (lo := (155843341 / 250000000)) (hi := (124674673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 549) = 1/(549 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-124674673 / 200000000) (-155843341 / 250000000) (Real.log (549 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (76136269 / 200000000) ≤ -Real.log (1280 / 1873) ∧
    -Real.log (1280 / 1873) ≤ (190340673 / 500000000) := by
  have h := checkLog_sound (w := (593 / 3153)) (n := 12)
    (lo := (76136269 / 200000000)) (hi := (190340673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1873 / 1280) = 1/(1280 / 1873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (76136269 / 200000000) (190340673 / 500000000) (Real.log (1873 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1873 / 1280) = -Real.log (1280 / 1873) := by
    rw [show ((1873 / 1280) : ℝ) = ((1280 / 1873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77785133 / 125000000) ≤ -Real.log (687 / 1280) ∧
    -Real.log (687 / 1280) ≤ (124456213 / 200000000) := by
  have h := checkLog_sound (w := (593 / 1967)) (n := 12)
    (lo := (77785133 / 125000000)) (hi := (124456213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 687) = 1/(687 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124456213 / 200000000) (-77785133 / 125000000) (Real.log (687 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57158157 / 200000000) ≤ -Real.log (500000 / 665407) ∧
    -Real.log (500000 / 665407) ≤ (142895393 / 500000000) := by
  have h := checkLog_sound (w := (165407 / 1165407)) (n := 12)
    (lo := (57158157 / 200000000)) (hi := (142895393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665407 / 500000) = 1/(500000 / 665407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57158157 / 200000000) (142895393 / 500000000) (Real.log (665407 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (665407 / 500000) = -Real.log (500000 / 665407) := by
    rw [show ((665407 / 500000) : ℝ) = ((500000 / 665407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40169323 / 100000000) ≤ -Real.log (334593 / 500000) ∧
    -Real.log (334593 / 500000) ≤ (401693231 / 1000000000) := by
  have h := checkLog_sound (w := (165407 / 834593)) (n := 12)
    (lo := (40169323 / 100000000)) (hi := (401693231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334593) = 1/(334593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-401693231 / 1000000000) (-40169323 / 100000000) (Real.log (334593 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (286112341 / 1000000000) ≤ -Real.log (500000 / 665621) ∧
    -Real.log (500000 / 665621) ≤ (143056171 / 500000000) := by
  have h := checkLog_sound (w := (165621 / 1165621)) (n := 12)
    (lo := (286112341 / 1000000000)) (hi := (143056171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665621 / 500000) = 1/(500000 / 665621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (286112341 / 1000000000) (143056171 / 500000000) (Real.log (665621 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (665621 / 500000) = -Real.log (500000 / 665621) := by
    rw [show ((665621 / 500000) : ℝ) = ((500000 / 665621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (201166509 / 500000000) ≤ -Real.log (334379 / 500000) ∧
    -Real.log (334379 / 500000) ≤ (402333019 / 1000000000) := by
  have h := checkLog_sound (w := (165621 / 834379)) (n := 12)
    (lo := (201166509 / 500000000)) (hi := (402333019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334379) = 1/(334379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-402333019 / 1000000000) (-201166509 / 500000000) (Real.log (334379 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108050203 / 500000000) ≤ -Real.log (1000000 / 1241227) ∧
    -Real.log (1000000 / 1241227) ≤ (216100407 / 1000000000) := by
  have h := checkLog_sound (w := (241227 / 2241227)) (n := 12)
    (lo := (108050203 / 500000000)) (hi := (216100407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241227 / 1000000) = 1/(1000000 / 1241227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108050203 / 500000000) (216100407 / 1000000000) (Real.log (1241227 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1241227 / 1000000) = -Real.log (1000000 / 1241227) := by
    rw [show ((1241227 / 1000000) : ℝ) = ((1000000 / 1241227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17253289 / 62500000) ≤ -Real.log (758773 / 1000000) ∧
    -Real.log (758773 / 1000000) ≤ (2208421 / 8000000) := by
  have h := checkLog_sound (w := (241227 / 1758773)) (n := 12)
    (lo := (17253289 / 62500000)) (hi := (2208421 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758773) = 1/(758773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2208421 / 8000000) (-17253289 / 62500000) (Real.log (758773 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (216367847 / 1000000000) ≤ -Real.log (1000000 / 1241559) ∧
    -Real.log (1000000 / 1241559) ≤ (27045981 / 125000000) := by
  have h := checkLog_sound (w := (241559 / 2241559)) (n := 12)
    (lo := (216367847 / 1000000000)) (hi := (27045981 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241559 / 1000000) = 1/(1000000 / 1241559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (216367847 / 1000000000) (27045981 / 125000000) (Real.log (1241559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1241559 / 1000000) = -Real.log (1000000 / 1241559) := by
    rw [show ((1241559 / 1000000) : ℝ) = ((1000000 / 1241559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (69122567 / 250000000) ≤ -Real.log (758441 / 1000000) ∧
    -Real.log (758441 / 1000000) ≤ (276490269 / 1000000000) := by
  have h := checkLog_sound (w := (241559 / 1758441)) (n := 12)
    (lo := (69122567 / 250000000)) (hi := (276490269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758441) = 1/(758441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-276490269 / 1000000000) (-69122567 / 250000000) (Real.log (758441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (137496803 / 200000000) ≤ -Real.log (100000000000 / 198870568123) ∧
    -Real.log (100000000000 / 198870568123) ≤ (42967751 / 62500000) := by
  have h := checkLog_sound (w := (98870568123 / 298870568123)) (n := 12)
    (lo := (137496803 / 200000000)) (hi := (42967751 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198870568123 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198870568123 / 100000000000) = 1/(100000000000 / 198870568123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (137496803 / 200000000) (42967751 / 62500000) (Real.log (198870568123 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (198870568123 / 100000000000) = -Real.log (100000000000 / 198870568123) := by
    rw [show ((198870568123 / 100000000000) : ℝ) = ((100000000000 / 198870568123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (688445359 / 1000000000) ≤ -Real.log (500000000000 / 995309214993) ∧
    -Real.log (500000000000 / 995309214993) ≤ (8605567 / 12500000) := by
  have h := checkLog_sound (w := (495309214993 / 1495309214993)) (n := 12)
    (lo := (688445359 / 1000000000)) (hi := (8605567 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((995309214993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(995309214993 / 500000000000) = 1/(500000000000 / 995309214993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (688445359 / 1000000000) (8605567 / 12500000) (Real.log (995309214993 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (995309214993 / 500000000000) = -Real.log (500000000000 / 995309214993) := by
    rw [show ((995309214993 / 500000000000) : ℝ) = ((500000000000 / 995309214993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (49215303 / 100000000) ≤ -Real.log (500000000000 / 817917216347) ∧
    -Real.log (500000000000 / 817917216347) ≤ (492153031 / 1000000000) := by
  have h := checkLog_sound (w := (317917216347 / 1317917216347)) (n := 12)
    (lo := (49215303 / 100000000)) (hi := (492153031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817917216347 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817917216347 / 500000000000) = 1/(500000000000 / 817917216347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (49215303 / 100000000) (492153031 / 1000000000) (Real.log (817917216347 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (817917216347 / 500000000000) = -Real.log (500000000000 / 817917216347) := by
    rw [show ((817917216347 / 500000000000) : ℝ) = ((500000000000 / 817917216347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (123214529 / 250000000) ≤ -Real.log (250000000000 / 409247060747) ∧
    -Real.log (250000000000 / 409247060747) ≤ (492858117 / 1000000000) := by
  have h := checkLog_sound (w := (159247060747 / 659247060747)) (n := 12)
    (lo := (123214529 / 250000000)) (hi := (492858117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409247060747 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409247060747 / 250000000000) = 1/(250000000000 / 409247060747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (123214529 / 250000000) (492858117 / 1000000000) (Real.log (409247060747 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (409247060747 / 250000000000) = -Real.log (250000000000 / 409247060747) := by
    rw [show ((409247060747 / 250000000000) : ℝ) = ((250000000000 / 409247060747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0365
