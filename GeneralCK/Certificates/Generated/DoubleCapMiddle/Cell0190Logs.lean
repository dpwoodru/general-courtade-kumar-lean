import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0190
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

theorem reflection_log_1_neg : (67536601 / 250000000) ≤ -Real.log (1280 / 1677) ∧
    -Real.log (1280 / 1677) ≤ (54029281 / 200000000) := by
  have h := checkLog_sound (w := (397 / 2957)) (n := 12)
    (lo := (67536601 / 250000000)) (hi := (54029281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1280) = 1/(1280 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67536601 / 250000000) (54029281 / 200000000) (Real.log (1677 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1677 / 1280) = -Real.log (1280 / 1677) := by
    rw [show ((1677 / 1280) : ℝ) = ((1280 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92822539 / 250000000) ≤ -Real.log (883 / 1280) ∧
    -Real.log (883 / 1280) ≤ (371290157 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2163)) (n := 12)
    (lo := (92822539 / 250000000)) (hi := (371290157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 883) = 1/(883 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-371290157 / 1000000000) (-92822539 / 250000000) (Real.log (883 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (269699077 / 1000000000) ≤ -Real.log (1024 / 1341) ∧
    -Real.log (1024 / 1341) ≤ (134849539 / 500000000) := by
  have h := checkLog_sound (w := (317 / 2365)) (n := 12)
    (lo := (269699077 / 1000000000)) (hi := (134849539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341 / 1024) = 1/(1024 / 1341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (269699077 / 1000000000) (134849539 / 500000000) (Real.log (1341 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1341 / 1024) = -Real.log (1024 / 1341) := by
    rw [show ((1341 / 1024) : ℝ) = ((1024 / 1341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (370441139 / 1000000000) ≤ -Real.log (707 / 1024) ∧
    -Real.log (707 / 1024) ≤ (18522057 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1731)) (n := 12)
    (lo := (370441139 / 1000000000)) (hi := (18522057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 707) = 1/(707 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18522057 / 50000000) (-370441139 / 1000000000) (Real.log (707 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (482619031 / 1000000000) ≤ -Real.log (640 / 1037) ∧
    -Real.log (640 / 1037) ≤ (60327379 / 125000000) := by
  have h := checkLog_sound (w := (397 / 1677)) (n := 12)
    (lo := (482619031 / 1000000000)) (hi := (60327379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1037 / 640) = 1/(640 / 1037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (482619031 / 1000000000) (60327379 / 125000000) (Real.log (1037 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1037 / 640) = -Real.log (640 / 1037) := by
    rw [show ((1037 / 640) : ℝ) = ((640 / 1037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (242101683 / 250000000) ≤ -Real.log (243 / 640) ∧
    -Real.log (243 / 640) ≤ (484203367 / 500000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 243) = 1/(243 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-484203367 / 500000000) (-242101683 / 250000000) (Real.log (243 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (48189553 / 100000000) ≤ -Real.log (512 / 829) ∧
    -Real.log (512 / 829) ≤ (481895531 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1341)) (n := 12)
    (lo := (48189553 / 100000000)) (hi := (481895531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829 / 512) = 1/(512 / 829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (48189553 / 100000000) (481895531 / 1000000000) (Real.log (829 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (829 / 512) = -Real.log (512 / 829) := by
    rw [show ((829 / 512) : ℝ) = ((512 / 829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (193065013 / 200000000) ≤ -Real.log (195 / 512) ∧
    -Real.log (195 / 512) ≤ (965325067 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 451)) (n := 12)
    (lo := (54435577 / 200000000)) (hi := (136088943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 195) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 195) = 1/(195 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-965325067 / 1000000000) (-193065013 / 200000000) (Real.log (195 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (368946341 / 1000000000) ≤ -Real.log (100000 / 144621) ∧
    -Real.log (100000 / 144621) ≤ (184473171 / 500000000) := by
  have h := checkLog_sound (w := (44621 / 244621)) (n := 12)
    (lo := (368946341 / 1000000000)) (hi := (184473171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144621 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144621 / 100000) = 1/(100000 / 144621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (368946341 / 1000000000) (184473171 / 500000000) (Real.log (144621 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (144621 / 100000) = -Real.log (100000 / 144621) := by
    rw [show ((144621 / 100000) : ℝ) = ((100000 / 144621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23638789 / 40000000) ≤ -Real.log (55379 / 100000) ∧
    -Real.log (55379 / 100000) ≤ (295484863 / 500000000) := by
  have h := checkLog_sound (w := (44621 / 155379)) (n := 12)
    (lo := (23638789 / 40000000)) (hi := (295484863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 55379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 55379) = 1/(55379 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-295484863 / 500000000) (-23638789 / 40000000) (Real.log (55379 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184779049 / 500000000) ≤ -Real.log (200000 / 289419) ∧
    -Real.log (200000 / 289419) ≤ (369558099 / 1000000000) := by
  have h := checkLog_sound (w := (89419 / 489419)) (n := 12)
    (lo := (184779049 / 500000000)) (hi := (369558099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289419 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289419 / 200000) = 1/(200000 / 289419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184779049 / 500000000) (369558099 / 1000000000) (Real.log (289419 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (289419 / 200000) = -Real.log (200000 / 289419) := by
    rw [show ((289419 / 200000) : ℝ) = ((200000 / 289419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (296284541 / 500000000) ≤ -Real.log (110581 / 200000) ∧
    -Real.log (110581 / 200000) ≤ (592569083 / 1000000000) := by
  have h := checkLog_sound (w := (89419 / 310581)) (n := 12)
    (lo := (296284541 / 500000000)) (hi := (592569083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 110581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 110581) = 1/(110581 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-592569083 / 1000000000) (-296284541 / 500000000) (Real.log (110581 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288090489 / 1000000000) ≤ -Real.log (500000 / 666939) ∧
    -Real.log (500000 / 666939) ≤ (28809049 / 100000000) := by
  have h := checkLog_sound (w := (166939 / 1166939)) (n := 12)
    (lo := (288090489 / 1000000000)) (hi := (28809049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666939 / 500000) = 1/(500000 / 666939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288090489 / 1000000000) (28809049 / 100000000) (Real.log (666939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (666939 / 500000) = -Real.log (500000 / 666939) := by
    rw [show ((666939 / 500000) : ℝ) = ((500000 / 666939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (203141221 / 500000000) ≤ -Real.log (333061 / 500000) ∧
    -Real.log (333061 / 500000) ≤ (406282443 / 1000000000) := by
  have h := checkLog_sound (w := (166939 / 833061)) (n := 12)
    (lo := (203141221 / 500000000)) (hi := (406282443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 333061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 333061) = 1/(333061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-406282443 / 1000000000) (-203141221 / 500000000) (Real.log (333061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (288644359 / 1000000000) ≤ -Real.log (1000000 / 1334617) ∧
    -Real.log (1000000 / 1334617) ≤ (7216109 / 25000000) := by
  have h := checkLog_sound (w := (334617 / 2334617)) (n := 12)
    (lo := (288644359 / 1000000000)) (hi := (7216109 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334617 / 1000000) = 1/(1000000 / 1334617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (288644359 / 1000000000) (7216109 / 25000000) (Real.log (1334617 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1334617 / 1000000) = -Real.log (1000000 / 1334617) := by
    rw [show ((1334617 / 1000000) : ℝ) = ((1000000 / 1334617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25462029 / 62500000) ≤ -Real.log (665383 / 1000000) ∧
    -Real.log (665383 / 1000000) ≤ (81478493 / 200000000) := by
  have h := checkLog_sound (w := (334617 / 1665383)) (n := 12)
    (lo := (25462029 / 62500000)) (hi := (81478493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665383) = 1/(665383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-81478493 / 200000000) (-25462029 / 62500000) (Real.log (665383 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (479958033 / 500000000) ≤ -Real.log (500000000000 / 1305738637389) ∧
    -Real.log (500000000000 / 1305738637389) ≤ (239979017 / 250000000) := by
  have h := checkLog_sound (w := (305738637389 / 2305738637389)) (n := 12)
    (lo := (133384443 / 500000000)) (hi := (266768887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305738637389 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1305738637389 / 1000000000000) = 1/(500000000000 / 1305738637389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (479958033 / 500000000) (239979017 / 250000000) (Real.log (1305738637389 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1305738637389 / 500000000000) = -Real.log (500000000000 / 1305738637389) := by
    rw [show ((1305738637389 / 500000000000) : ℝ) = ((500000000000 / 1305738637389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (48106359 / 50000000) ≤ -Real.log (500000000000 / 1308628968811) ∧
    -Real.log (500000000000 / 1308628968811) ≤ (481063591 / 500000000) := by
  have h := checkLog_sound (w := (308628968811 / 2308628968811)) (n := 12)
    (lo := (13449 / 50000)) (hi := (268980001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308628968811 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1308628968811 / 1000000000000) = 1/(500000000000 / 1308628968811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (48106359 / 50000000) (481063591 / 500000000) (Real.log (1308628968811 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1308628968811 / 500000000000) = -Real.log (500000000000 / 1308628968811) := by
    rw [show ((1308628968811 / 500000000000) : ℝ) = ((500000000000 / 1308628968811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (69437293 / 100000000) ≤ -Real.log (125000000000 / 250306625513) ∧
    -Real.log (125000000000 / 250306625513) ≤ (173593233 / 250000000) := by
  have h := checkLog_sound (w := (306625513 / 500306625513)) (n := 12)
    (lo := (4903 / 4000000)) (hi := (1225751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250306625513 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250306625513 / 250000000000) = 1/(125000000000 / 250306625513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (69437293 / 100000000) (173593233 / 250000000) (Real.log (250306625513 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (250306625513 / 125000000000) = -Real.log (125000000000 / 250306625513) := by
    rw [show ((250306625513 / 125000000000) : ℝ) = ((125000000000 / 250306625513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (696036823 / 1000000000) ≤ -Real.log (100000000000 / 200578764411) ∧
    -Real.log (100000000000 / 200578764411) ≤ (27841473 / 40000000) := by
  have h := checkLog_sound (w := (578764411 / 400578764411)) (n := 12)
    (lo := (2889643 / 1000000000)) (hi := (722411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200578764411 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200578764411 / 200000000000) = 1/(100000000000 / 200578764411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (696036823 / 1000000000) (27841473 / 40000000) (Real.log (200578764411 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (200578764411 / 100000000000) = -Real.log (100000000000 / 200578764411) := by
    rw [show ((200578764411 / 100000000000) : ℝ) = ((100000000000 / 200578764411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0190
