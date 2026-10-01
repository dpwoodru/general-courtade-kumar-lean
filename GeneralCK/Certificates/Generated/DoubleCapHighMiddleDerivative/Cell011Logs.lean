import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell011
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

theorem reflection_log_1_neg : (22875279 / 100000000) ≤ -Real.log (1280 / 1609) ∧
    -Real.log (1280 / 1609) ≤ (228752791 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2889)) (n := 12)
    (lo := (22875279 / 100000000)) (hi := (228752791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609 / 1280) = 1/(1280 / 1609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22875279 / 100000000) (228752791 / 1000000000) (Real.log (1609 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1609 / 1280) = -Real.log (1280 / 1609) := by
    rw [show ((1609 / 1280) : ℝ) = ((1280 / 1609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148550647 / 500000000) ≤ -Real.log (951 / 1280) ∧
    -Real.log (951 / 1280) ≤ (59420259 / 200000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 951) = 1/(951 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59420259 / 200000000) (-148550647 / 500000000) (Real.log (951 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (228286553 / 1000000000) ≤ -Real.log (5120 / 6433) ∧
    -Real.log (5120 / 6433) ≤ (114143277 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 11553)) (n := 12)
    (lo := (228286553 / 1000000000)) (hi := (114143277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6433 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6433 / 5120) = 1/(5120 / 6433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (228286553 / 1000000000) (114143277 / 500000000) (Real.log (6433 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6433 / 5120) = -Real.log (5120 / 6433) := by
    rw [show ((6433 / 5120) : ℝ) = ((5120 / 6433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (296312961 / 1000000000) ≤ -Real.log (3807 / 5120) ∧
    -Real.log (3807 / 5120) ≤ (148156481 / 500000000) := by
  have h := checkLog_sound (w := (1313 / 8927)) (n := 12)
    (lo := (296312961 / 1000000000)) (hi := (148156481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3807) = 1/(3807 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-148156481 / 500000000) (-296312961 / 1000000000) (Real.log (3807 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20884597 / 125000000) ≤ -Real.log (200000 / 236369) ∧
    -Real.log (200000 / 236369) ≤ (167076777 / 1000000000) := by
  have h := checkLog_sound (w := (36369 / 436369)) (n := 12)
    (lo := (20884597 / 125000000)) (hi := (167076777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236369 / 200000) = 1/(200000 / 236369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20884597 / 125000000) (167076777 / 1000000000) (Real.log (236369 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (236369 / 200000) = -Real.log (200000 / 236369) := by
    rw [show ((236369 / 200000) : ℝ) = ((200000 / 236369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (200703473 / 1000000000) ≤ -Real.log (163631 / 200000) ∧
    -Real.log (163631 / 200000) ≤ (100351737 / 500000000) := by
  have h := checkLog_sound (w := (36369 / 363631)) (n := 12)
    (lo := (200703473 / 1000000000)) (hi := (100351737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163631) = 1/(163631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-100351737 / 500000000) (-200703473 / 1000000000) (Real.log (163631 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41857811 / 250000000) ≤ -Real.log (125000 / 147783) ∧
    -Real.log (125000 / 147783) ≤ (33486249 / 200000000) := by
  have h := checkLog_sound (w := (22783 / 272783)) (n := 12)
    (lo := (41857811 / 250000000)) (hi := (33486249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147783 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147783 / 125000) = 1/(125000 / 147783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41857811 / 250000000) (33486249 / 200000000) (Real.log (147783 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (147783 / 125000) = -Real.log (125000 / 147783) := by
    rw [show ((147783 / 125000) : ℝ) = ((125000 / 147783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50303933 / 250000000) ≤ -Real.log (102217 / 125000) ∧
    -Real.log (102217 / 125000) ≤ (201215733 / 1000000000) := by
  have h := checkLog_sound (w := (22783 / 227217)) (n := 12)
    (lo := (50303933 / 250000000)) (hi := (201215733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102217) = 1/(102217 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-201215733 / 1000000000) (-50303933 / 250000000) (Real.log (102217 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122016727 / 1000000000) ≤ -Real.log (1000000 / 1129773) ∧
    -Real.log (1000000 / 1129773) ≤ (15252091 / 125000000) := by
  have h := checkLog_sound (w := (129773 / 2129773)) (n := 12)
    (lo := (122016727 / 1000000000)) (hi := (15252091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129773 / 1000000) = 1/(1000000 / 1129773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122016727 / 1000000000) (15252091 / 125000000) (Real.log (1129773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1129773 / 1000000) = -Real.log (1000000 / 1129773) := by
    rw [show ((1129773 / 1000000) : ℝ) = ((1000000 / 1129773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139001181 / 1000000000) ≤ -Real.log (870227 / 1000000) ∧
    -Real.log (870227 / 1000000) ≤ (69500591 / 500000000) := by
  have h := checkLog_sound (w := (129773 / 1870227)) (n := 12)
    (lo := (139001181 / 1000000000)) (hi := (69500591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870227) = 1/(870227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69500591 / 500000000) (-139001181 / 1000000000) (Real.log (870227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1910729 / 15625000) ≤ -Real.log (500000 / 565039) ∧
    -Real.log (500000 / 565039) ≤ (122286657 / 1000000000) := by
  have h := checkLog_sound (w := (65039 / 1065039)) (n := 12)
    (lo := (1910729 / 15625000)) (hi := (122286657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565039 / 500000) = 1/(500000 / 565039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1910729 / 15625000) (122286657 / 1000000000) (Real.log (565039 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (565039 / 500000) = -Real.log (500000 / 565039) := by
    rw [show ((565039 / 500000) : ℝ) = ((500000 / 565039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69675863 / 500000000) ≤ -Real.log (434961 / 500000) ∧
    -Real.log (434961 / 500000) ≤ (139351727 / 1000000000) := by
  have h := checkLog_sound (w := (65039 / 934961)) (n := 12)
    (lo := (69675863 / 500000000)) (hi := (139351727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434961) = 1/(434961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139351727 / 1000000000) (-69675863 / 500000000) (Real.log (434961 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (104919903 / 200000000) ≤ -Real.log (500000000000 / 844890990281) ∧
    -Real.log (500000000000 / 844890990281) ≤ (131149879 / 250000000) := by
  have h := checkLog_sound (w := (344890990281 / 1344890990281)) (n := 12)
    (lo := (104919903 / 200000000)) (hi := (131149879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((844890990281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(844890990281 / 500000000000) = 1/(500000000000 / 844890990281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (104919903 / 200000000) (131149879 / 250000000) (Real.log (844890990281 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (844890990281 / 500000000000) = -Real.log (500000000000 / 844890990281) := by
    rw [show ((844890990281 / 500000000000) : ℝ) = ((500000000000 / 844890990281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131463521 / 250000000) ≤ -Real.log (62500000000 / 105743953733) ∧
    -Real.log (62500000000 / 105743953733) ≤ (105170817 / 200000000) := by
  have h := checkLog_sound (w := (43243953733 / 168243953733)) (n := 12)
    (lo := (131463521 / 250000000)) (hi := (105170817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105743953733 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105743953733 / 62500000000) = 1/(62500000000 / 105743953733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (131463521 / 250000000) (105170817 / 200000000) (Real.log (105743953733 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (105743953733 / 62500000000) = -Real.log (62500000000 / 105743953733) := by
    rw [show ((105743953733 / 62500000000) : ℝ) = ((62500000000 / 105743953733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (1471121 / 4000000) ≤ -Real.log (500000000000 / 722262285263) ∧
    -Real.log (500000000000 / 722262285263) ≤ (367780251 / 1000000000) := by
  have h := checkLog_sound (w := (222262285263 / 1222262285263)) (n := 12)
    (lo := (1471121 / 4000000)) (hi := (367780251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722262285263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722262285263 / 500000000000) = 1/(500000000000 / 722262285263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1471121 / 4000000) (367780251 / 1000000000) (Real.log (722262285263 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (722262285263 / 500000000000) = -Real.log (500000000000 / 722262285263) := by
    rw [show ((722262285263 / 500000000000) : ℝ) = ((500000000000 / 722262285263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (368646977 / 1000000000) ≤ -Real.log (125000000000 / 180722140153) ∧
    -Real.log (125000000000 / 180722140153) ≤ (184323489 / 500000000) := by
  have h := checkLog_sound (w := (55722140153 / 305722140153)) (n := 12)
    (lo := (368646977 / 1000000000)) (hi := (184323489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180722140153 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180722140153 / 125000000000) = 1/(125000000000 / 180722140153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (368646977 / 1000000000) (184323489 / 500000000) (Real.log (180722140153 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (180722140153 / 125000000000) = -Real.log (125000000000 / 180722140153) := by
    rw [show ((180722140153 / 125000000000) : ℝ) = ((125000000000 / 180722140153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (261017909 / 1000000000) ≤ -Real.log (50000000000 / 64912545807) ∧
    -Real.log (50000000000 / 64912545807) ≤ (26101791 / 100000000) := by
  have h := checkLog_sound (w := (14912545807 / 114912545807)) (n := 12)
    (lo := (261017909 / 1000000000)) (hi := (26101791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64912545807 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64912545807 / 50000000000) = 1/(50000000000 / 64912545807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (261017909 / 1000000000) (26101791 / 100000000) (Real.log (64912545807 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (64912545807 / 50000000000) = -Real.log (50000000000 / 64912545807) := by
    rw [show ((64912545807 / 50000000000) : ℝ) = ((50000000000 / 64912545807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (261638383 / 1000000000) ≤ -Real.log (500000000000 / 649528348519) ∧
    -Real.log (500000000000 / 649528348519) ≤ (16352399 / 62500000) := by
  have h := checkLog_sound (w := (149528348519 / 1149528348519)) (n := 12)
    (lo := (261638383 / 1000000000)) (hi := (16352399 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649528348519 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649528348519 / 500000000000) = 1/(500000000000 / 649528348519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (261638383 / 1000000000) (16352399 / 62500000) (Real.log (649528348519 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649528348519 / 500000000000) = -Real.log (500000000000 / 649528348519) := by
    rw [show ((649528348519 / 500000000000) : ℝ) = ((500000000000 / 649528348519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17065069 / 1000000000) ≤ -Real.log (245769928479 / 250000000000) ∧
    -Real.log (245769928479 / 250000000000) ≤ (1706507 / 100000000) := by
  have h := checkLog_sound (w := (4230071521 / 495769928479)) (n := 12)
    (lo := (17065069 / 1000000000)) (hi := (1706507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245769928479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245769928479) = 1/(245769928479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1706507 / 100000000) (-17065069 / 1000000000) (Real.log (245769928479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8492227 / 500000000) ≤ -Real.log (983158968471 / 1000000000000) ∧
    -Real.log (983158968471 / 1000000000000) ≤ (3396891 / 200000000) := by
  have h := checkLog_sound (w := (16841031529 / 1983158968471)) (n := 12)
    (lo := (8492227 / 500000000)) (hi := (3396891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983158968471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983158968471) = 1/(983158968471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3396891 / 200000000) (-8492227 / 500000000) (Real.log (983158968471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell011
