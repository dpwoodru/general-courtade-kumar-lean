import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0357
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

theorem reflection_log_1_neg : (52621413 / 250000000) ≤ -Real.log (10240 / 12639) ∧
    -Real.log (10240 / 12639) ≤ (210485653 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 22879)) (n := 12)
    (lo := (52621413 / 250000000)) (hi := (210485653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12639 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12639 / 10240) = 1/(10240 / 12639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52621413 / 250000000) (210485653 / 1000000000) (Real.log (12639 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12639 / 10240) = -Real.log (10240 / 12639) := by
    rw [show ((12639 / 10240) : ℝ) = ((10240 / 12639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133467621 / 500000000) ≤ -Real.log (7841 / 10240) ∧
    -Real.log (7841 / 10240) ≤ (266935243 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 18081)) (n := 12)
    (lo := (133467621 / 500000000)) (hi := (266935243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7841) = 1/(7841 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-266935243 / 1000000000) (-133467621 / 500000000) (Real.log (7841 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (210248263 / 1000000000) ≤ -Real.log (2560 / 3159) ∧
    -Real.log (2560 / 3159) ≤ (26281033 / 125000000) := by
  have h := checkLog_sound (w := (599 / 5719)) (n := 12)
    (lo := (210248263 / 1000000000)) (hi := (26281033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3159 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3159 / 2560) = 1/(2560 / 3159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (210248263 / 1000000000) (26281033 / 125000000) (Real.log (3159 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3159 / 2560) = -Real.log (2560 / 3159) := by
    rw [show ((3159 / 2560) : ℝ) = ((2560 / 3159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (266552711 / 1000000000) ≤ -Real.log (1961 / 2560) ∧
    -Real.log (1961 / 2560) ≤ (33319089 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4521)) (n := 12)
    (lo := (266552711 / 1000000000)) (hi := (33319089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1961) = 1/(1961 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33319089 / 125000000) (-266552711 / 1000000000) (Real.log (1961 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (384278711 / 1000000000) ≤ -Real.log (5120 / 7519) ∧
    -Real.log (5120 / 7519) ≤ (48034839 / 125000000) := by
  have h := checkLog_sound (w := (2399 / 12639)) (n := 12)
    (lo := (384278711 / 1000000000)) (hi := (48034839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7519 / 5120) = 1/(5120 / 7519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (384278711 / 1000000000) (48034839 / 125000000) (Real.log (7519 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7519 / 5120) = -Real.log (5120 / 7519) := by
    rw [show ((7519 / 5120) : ℝ) = ((5120 / 7519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (632154979 / 1000000000) ≤ -Real.log (2721 / 5120) ∧
    -Real.log (2721 / 5120) ≤ (31607749 / 50000000) := by
  have h := checkLog_sound (w := (2399 / 7841)) (n := 12)
    (lo := (632154979 / 1000000000)) (hi := (31607749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2721) = 1/(2721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-31607749 / 50000000) (-632154979 / 1000000000) (Real.log (2721 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (191939821 / 500000000) ≤ -Real.log (1280 / 1879) ∧
    -Real.log (1280 / 1879) ≤ (383879643 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 3159)) (n := 12)
    (lo := (191939821 / 500000000)) (hi := (383879643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1879 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1879 / 1280) = 1/(1280 / 1879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (191939821 / 500000000) (383879643 / 1000000000) (Real.log (1879 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1879 / 1280) = -Real.log (1280 / 1879) := by
    rw [show ((1879 / 1280) : ℝ) = ((1280 / 1879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12621061 / 20000000) ≤ -Real.log (681 / 1280) ∧
    -Real.log (681 / 1280) ≤ (631053051 / 1000000000) := by
  have h := checkLog_sound (w := (599 / 1961)) (n := 12)
    (lo := (12621061 / 20000000)) (hi := (631053051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 681) = 1/(681 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-631053051 / 1000000000) (-12621061 / 20000000) (Real.log (681 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9011167 / 31250000) ≤ -Real.log (500000 / 667117) ∧
    -Real.log (500000 / 667117) ≤ (57671469 / 200000000) := by
  have h := checkLog_sound (w := (167117 / 1167117)) (n := 12)
    (lo := (9011167 / 31250000)) (hi := (57671469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667117 / 500000) = 1/(500000 / 667117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9011167 / 31250000) (57671469 / 200000000) (Real.log (667117 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667117 / 500000) = -Real.log (500000 / 667117) := by
    rw [show ((667117 / 500000) : ℝ) = ((500000 / 667117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (406817021 / 1000000000) ≤ -Real.log (332883 / 500000) ∧
    -Real.log (332883 / 500000) ≤ (203408511 / 500000000) := by
  have h := checkLog_sound (w := (167117 / 832883)) (n := 12)
    (lo := (406817021 / 1000000000)) (hi := (203408511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332883) = 1/(332883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203408511 / 500000000) (-406817021 / 1000000000) (Real.log (332883 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11547153 / 40000000) ≤ -Real.log (1000000 / 1334663) ∧
    -Real.log (1000000 / 1334663) ≤ (144339413 / 500000000) := by
  have h := checkLog_sound (w := (334663 / 2334663)) (n := 12)
    (lo := (11547153 / 40000000)) (hi := (144339413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334663 / 1000000) = 1/(1000000 / 1334663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11547153 / 40000000) (144339413 / 500000000) (Real.log (1334663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1334663 / 1000000) = -Real.log (1000000 / 1334663) := by
    rw [show ((1334663 / 1000000) : ℝ) = ((1000000 / 1334663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (407461599 / 1000000000) ≤ -Real.log (665337 / 1000000) ∧
    -Real.log (665337 / 1000000) ≤ (509327 / 1250000) := by
  have h := checkLog_sound (w := (334663 / 1665337)) (n := 12)
    (lo := (407461599 / 1000000000)) (hi := (509327 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665337) = 1/(665337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-509327 / 1250000) (-407461599 / 1000000000) (Real.log (665337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109117361 / 500000000) ≤ -Real.log (1000000 / 1243879) ∧
    -Real.log (1000000 / 1243879) ≤ (218234723 / 1000000000) := by
  have h := checkLog_sound (w := (243879 / 2243879)) (n := 12)
    (lo := (109117361 / 500000000)) (hi := (218234723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243879 / 1000000) = 1/(1000000 / 1243879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109117361 / 500000000) (218234723 / 1000000000) (Real.log (1243879 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1243879 / 1000000) = -Real.log (1000000 / 1243879) := by
    rw [show ((1243879 / 1000000) : ℝ) = ((1000000 / 1243879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139776931 / 500000000) ≤ -Real.log (756121 / 1000000) ∧
    -Real.log (756121 / 1000000) ≤ (279553863 / 1000000000) := by
  have h := checkLog_sound (w := (243879 / 1756121)) (n := 12)
    (lo := (139776931 / 500000000)) (hi := (279553863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756121) = 1/(756121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-279553863 / 1000000000) (-139776931 / 500000000) (Real.log (756121 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (218502397 / 1000000000) ≤ -Real.log (250000 / 311053) ∧
    -Real.log (250000 / 311053) ≤ (109251199 / 500000000) := by
  have h := checkLog_sound (w := (61053 / 561053)) (n := 12)
    (lo := (218502397 / 1000000000)) (hi := (109251199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311053 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311053 / 250000) = 1/(250000 / 311053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218502397 / 1000000000) (109251199 / 500000000) (Real.log (311053 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (311053 / 250000) = -Real.log (250000 / 311053) := by
    rw [show ((311053 / 250000) : ℝ) = ((250000 / 311053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55998873 / 200000000) ≤ -Real.log (188947 / 250000) ∧
    -Real.log (188947 / 250000) ≤ (139997183 / 500000000) := by
  have h := checkLog_sound (w := (61053 / 438947)) (n := 12)
    (lo := (55998873 / 200000000)) (hi := (139997183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188947) = 1/(188947 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139997183 / 500000000) (-55998873 / 200000000) (Real.log (188947 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (139034873 / 200000000) ≤ -Real.log (100000000000 / 200405848301) ∧
    -Real.log (100000000000 / 200405848301) ≤ (695174367 / 1000000000) := by
  have h := checkLog_sound (w := (405848301 / 400405848301)) (n := 12)
    (lo := (405437 / 200000000)) (hi := (1013593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200405848301 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200405848301 / 200000000000) = 1/(100000000000 / 200405848301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (139034873 / 200000000) (695174367 / 1000000000) (Real.log (200405848301 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (200405848301 / 100000000000) = -Real.log (100000000000 / 200405848301) := by
    rw [show ((200405848301 / 100000000000) : ℝ) = ((100000000000 / 200405848301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (87017553 / 125000000) ≤ -Real.log (500000000000 / 1002997728971) ∧
    -Real.log (500000000000 / 1002997728971) ≤ (348070213 / 500000000) := by
  have h := checkLog_sound (w := (2997728971 / 2002997728971)) (n := 12)
    (lo := (748311 / 250000000)) (hi := (598649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002997728971 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002997728971 / 1000000000000) = 1/(500000000000 / 1002997728971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (87017553 / 125000000) (348070213 / 500000000) (Real.log (1002997728971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1002997728971 / 500000000000) = -Real.log (500000000000 / 1002997728971) := by
    rw [show ((1002997728971 / 500000000000) : ℝ) = ((500000000000 / 1002997728971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (99557717 / 200000000) ≤ -Real.log (15625000000 / 25704363951) ∧
    -Real.log (15625000000 / 25704363951) ≤ (248894293 / 500000000) := by
  have h := checkLog_sound (w := (10079363951 / 41329363951)) (n := 12)
    (lo := (99557717 / 200000000)) (hi := (248894293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25704363951 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25704363951 / 15625000000) = 1/(15625000000 / 25704363951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (99557717 / 200000000) (248894293 / 500000000) (Real.log (25704363951 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (25704363951 / 15625000000) = -Real.log (15625000000 / 25704363951) := by
    rw [show ((25704363951 / 15625000000) : ℝ) = ((15625000000 / 25704363951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (498496763 / 1000000000) ≤ -Real.log (62500000000 / 102890294633) ∧
    -Real.log (62500000000 / 102890294633) ≤ (124624191 / 250000000) := by
  have h := checkLog_sound (w := (40390294633 / 165390294633)) (n := 12)
    (lo := (498496763 / 1000000000)) (hi := (124624191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102890294633 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102890294633 / 62500000000) = 1/(62500000000 / 102890294633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (498496763 / 1000000000) (124624191 / 250000000) (Real.log (102890294633 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (102890294633 / 62500000000) = -Real.log (62500000000 / 102890294633) := by
    rw [show ((102890294633 / 62500000000) : ℝ) = ((62500000000 / 102890294633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0357
