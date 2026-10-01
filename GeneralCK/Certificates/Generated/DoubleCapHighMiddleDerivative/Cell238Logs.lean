import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell238
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

theorem reflection_log_1_neg : (329331849 / 1000000000) ≤ -Real.log (5120 / 7117) ∧
    -Real.log (5120 / 7117) ≤ (6586637 / 20000000) := by
  have h := checkLog_sound (w := (1997 / 12237)) (n := 12)
    (lo := (329331849 / 1000000000)) (hi := (6586637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7117 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7117 / 5120) = 1/(5120 / 7117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (329331849 / 1000000000) (6586637 / 20000000) (Real.log (7117 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7117 / 5120) = -Real.log (5120 / 7117) := by
    rw [show ((7117 / 5120) : ℝ) = ((5120 / 7117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (12359009 / 25000000) ≤ -Real.log (3123 / 5120) ∧
    -Real.log (3123 / 5120) ≤ (494360361 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 8243)) (n := 12)
    (lo := (12359009 / 25000000)) (hi := (494360361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3123) = 1/(3123 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-494360361 / 1000000000) (-12359009 / 25000000) (Real.log (3123 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (164455117 / 500000000) ≤ -Real.log (2560 / 3557) ∧
    -Real.log (2560 / 3557) ≤ (65782047 / 200000000) := by
  have h := checkLog_sound (w := (997 / 6117)) (n := 12)
    (lo := (164455117 / 500000000)) (hi := (65782047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3557 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3557 / 2560) = 1/(2560 / 3557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (164455117 / 500000000) (65782047 / 200000000) (Real.log (3557 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3557 / 2560) = -Real.log (2560 / 3557) := by
    rw [show ((3557 / 2560) : ℝ) = ((2560 / 3557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (493400207 / 1000000000) ≤ -Real.log (1563 / 2560) ∧
    -Real.log (1563 / 2560) ≤ (30837513 / 62500000) := by
  have h := checkLog_sound (w := (997 / 4123)) (n := 12)
    (lo := (493400207 / 1000000000)) (hi := (30837513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1563) = 1/(1563 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30837513 / 62500000) (-493400207 / 1000000000) (Real.log (1563 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (244704631 / 1000000000) ≤ -Real.log (250000 / 319311) ∧
    -Real.log (250000 / 319311) ≤ (30588079 / 125000000) := by
  have h := checkLog_sound (w := (69311 / 569311)) (n := 12)
    (lo := (244704631 / 1000000000)) (hi := (30588079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319311 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319311 / 250000) = 1/(250000 / 319311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (244704631 / 1000000000) (30588079 / 125000000) (Real.log (319311 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (319311 / 250000) = -Real.log (250000 / 319311) := by
    rw [show ((319311 / 250000) : ℝ) = ((250000 / 319311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (81170899 / 250000000) ≤ -Real.log (180689 / 250000) ∧
    -Real.log (180689 / 250000) ≤ (324683597 / 1000000000) := by
  have h := checkLog_sound (w := (69311 / 430689)) (n := 12)
    (lo := (81170899 / 250000000)) (hi := (324683597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 180689) = 1/(180689 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-324683597 / 1000000000) (-81170899 / 250000000) (Real.log (180689 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (245036541 / 1000000000) ≤ -Real.log (250000 / 319417) ∧
    -Real.log (250000 / 319417) ≤ (122518271 / 500000000) := by
  have h := checkLog_sound (w := (69417 / 569417)) (n := 12)
    (lo := (245036541 / 1000000000)) (hi := (122518271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319417 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319417 / 250000) = 1/(250000 / 319417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (245036541 / 1000000000) (122518271 / 500000000) (Real.log (319417 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (319417 / 250000) = -Real.log (250000 / 319417) := by
    rw [show ((319417 / 250000) : ℝ) = ((250000 / 319417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325270411 / 1000000000) ≤ -Real.log (180583 / 250000) ∧
    -Real.log (180583 / 250000) ≤ (81317603 / 250000000) := by
  have h := checkLog_sound (w := (69417 / 430583)) (n := 12)
    (lo := (325270411 / 1000000000)) (hi := (81317603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 180583) = 1/(180583 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-81317603 / 250000000) (-325270411 / 1000000000) (Real.log (180583 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182575691 / 1000000000) ≤ -Real.log (200000 / 240061) ∧
    -Real.log (200000 / 240061) ≤ (45643923 / 250000000) := by
  have h := checkLog_sound (w := (40061 / 440061)) (n := 12)
    (lo := (182575691 / 1000000000)) (hi := (45643923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240061 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240061 / 200000) = 1/(200000 / 240061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182575691 / 1000000000) (45643923 / 250000000) (Real.log (240061 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (240061 / 200000) = -Real.log (200000 / 240061) := by
    rw [show ((240061 / 200000) : ℝ) = ((200000 / 240061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111762437 / 500000000) ≤ -Real.log (159939 / 200000) ∧
    -Real.log (159939 / 200000) ≤ (1788199 / 8000000) := by
  have h := checkLog_sound (w := (40061 / 359939)) (n := 12)
    (lo := (111762437 / 500000000)) (hi := (1788199 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 159939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 159939) = 1/(159939 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1788199 / 8000000) (-111762437 / 500000000) (Real.log (159939 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91421127 / 500000000) ≤ -Real.log (1600 / 1921) ∧
    -Real.log (1600 / 1921) ≤ (36568451 / 200000000) := by
  have h := checkLog_sound (w := (321 / 3521)) (n := 12)
    (lo := (91421127 / 500000000)) (hi := (36568451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1600) = 1/(1600 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91421127 / 500000000) (36568451 / 200000000) (Real.log (1921 / 1600)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1921 / 1600) = -Real.log (1600 / 1921) := by
    rw [show ((1921 / 1600) : ℝ) = ((1600 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (111962553 / 500000000) ≤ -Real.log (1279 / 1600) ∧
    -Real.log (1279 / 1600) ≤ (223925107 / 1000000000) := by
  have h := checkLog_sound (w := (321 / 2879)) (n := 12)
    (lo := (111962553 / 500000000)) (hi := (223925107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 1279) = 1/(1279 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-223925107 / 1000000000) (-111962553 / 500000000) (Real.log (1279 / 1600)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20557761 / 25000000) ≤ -Real.log (250000000000 / 568937939859) ∧
    -Real.log (250000000000 / 568937939859) ≤ (411155221 / 500000000) := by
  have h := checkLog_sound (w := (68937939859 / 1068937939859)) (n := 12)
    (lo := (6458163 / 50000000)) (hi := (129163261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568937939859 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(568937939859 / 500000000000) = 1/(250000000000 / 568937939859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20557761 / 25000000) (411155221 / 500000000) (Real.log (568937939859 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (568937939859 / 250000000000) = -Real.log (250000000000 / 568937939859) := by
    rw [show ((568937939859 / 250000000000) : ℝ) = ((250000000000 / 568937939859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (823692209 / 1000000000) ≤ -Real.log (500000000000 / 1139449247519) ∧
    -Real.log (500000000000 / 1139449247519) ≤ (823692211 / 1000000000) := by
  have h := checkLog_sound (w := (139449247519 / 2139449247519)) (n := 12)
    (lo := (130545029 / 1000000000)) (hi := (13054503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139449247519 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1139449247519 / 1000000000000) = 1/(500000000000 / 1139449247519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (823692209 / 1000000000) (823692211 / 1000000000) (Real.log (1139449247519 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1139449247519 / 500000000000) = -Real.log (500000000000 / 1139449247519) := by
    rw [show ((1139449247519 / 500000000000) : ℝ) = ((500000000000 / 1139449247519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (142347057 / 250000000) ≤ -Real.log (500000000000 / 883592803103) ∧
    -Real.log (500000000000 / 883592803103) ≤ (569388229 / 1000000000) := by
  have h := checkLog_sound (w := (383592803103 / 1383592803103)) (n := 12)
    (lo := (142347057 / 250000000)) (hi := (569388229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883592803103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(883592803103 / 500000000000) = 1/(500000000000 / 883592803103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142347057 / 250000000) (569388229 / 1000000000) (Real.log (883592803103 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (883592803103 / 500000000000) = -Real.log (500000000000 / 883592803103) := by
    rw [show ((883592803103 / 500000000000) : ℝ) = ((500000000000 / 883592803103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (570306953 / 1000000000) ≤ -Real.log (500000000000 / 884404955063) ∧
    -Real.log (500000000000 / 884404955063) ≤ (285153477 / 500000000) := by
  have h := checkLog_sound (w := (384404955063 / 1384404955063)) (n := 12)
    (lo := (570306953 / 1000000000)) (hi := (285153477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884404955063 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884404955063 / 500000000000) = 1/(500000000000 / 884404955063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (570306953 / 1000000000) (285153477 / 500000000) (Real.log (884404955063 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (884404955063 / 500000000000) = -Real.log (500000000000 / 884404955063) := by
    rw [show ((884404955063 / 500000000000) : ℝ) = ((500000000000 / 884404955063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (81220113 / 200000000) ≤ -Real.log (250000000000 / 375238372129) ∧
    -Real.log (250000000000 / 375238372129) ≤ (203050283 / 500000000) := by
  have h := checkLog_sound (w := (125238372129 / 625238372129)) (n := 12)
    (lo := (81220113 / 200000000)) (hi := (203050283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375238372129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375238372129 / 250000000000) = 1/(250000000000 / 375238372129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81220113 / 200000000) (203050283 / 500000000) (Real.log (375238372129 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (375238372129 / 250000000000) = -Real.log (250000000000 / 375238372129) := by
    rw [show ((375238372129 / 250000000000) : ℝ) = ((250000000000 / 375238372129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406767361 / 1000000000) ≤ -Real.log (125000000000 / 187744331509) ∧
    -Real.log (125000000000 / 187744331509) ≤ (203383681 / 500000000) := by
  have h := checkLog_sound (w := (62744331509 / 312744331509)) (n := 12)
    (lo := (406767361 / 1000000000)) (hi := (203383681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187744331509 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187744331509 / 125000000000) = 1/(125000000000 / 187744331509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406767361 / 1000000000) (203383681 / 500000000) (Real.log (187744331509 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (187744331509 / 125000000000) = -Real.log (125000000000 / 187744331509) := by
    rw [show ((187744331509 / 125000000000) : ℝ) = ((125000000000 / 187744331509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10270713 / 250000000) ≤ -Real.log (2456959 / 2560000) ∧
    -Real.log (2456959 / 2560000) ≤ (41082853 / 1000000000) := by
  have h := checkLog_sound (w := (103041 / 5016959)) (n := 12)
    (lo := (10270713 / 250000000)) (hi := (41082853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 2456959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 2456959) = 1/(2456959 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41082853 / 1000000000) (-10270713 / 250000000) (Real.log (2456959 / 2560000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20474591 / 500000000) ≤ -Real.log (38395116279 / 40000000000) ∧
    -Real.log (38395116279 / 40000000000) ≤ (40949183 / 1000000000) := by
  have h := checkLog_sound (w := (1604883721 / 78395116279)) (n := 12)
    (lo := (20474591 / 500000000)) (hi := (40949183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38395116279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38395116279) = 1/(38395116279 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-40949183 / 1000000000) (-20474591 / 500000000) (Real.log (38395116279 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell238
