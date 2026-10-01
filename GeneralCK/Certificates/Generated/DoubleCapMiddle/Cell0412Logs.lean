import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0412
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

theorem reflection_log_1_neg : (98672429 / 500000000) ≤ -Real.log (5120 / 6237) ∧
    -Real.log (5120 / 6237) ≤ (197344859 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 11357)) (n := 12)
    (lo := (98672429 / 500000000)) (hi := (197344859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6237 / 5120) = 1/(5120 / 6237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (98672429 / 500000000) (197344859 / 1000000000) (Real.log (6237 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6237 / 5120) = -Real.log (5120 / 6237) := by
    rw [show ((6237 / 5120) : ℝ) = ((5120 / 6237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246110359 / 1000000000) ≤ -Real.log (4003 / 5120) ∧
    -Real.log (4003 / 5120) ≤ (6152759 / 25000000) := by
  have h := checkLog_sound (w := (1117 / 9123)) (n := 12)
    (lo := (246110359 / 1000000000)) (hi := (6152759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4003) = 1/(4003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6152759 / 25000000) (-246110359 / 1000000000) (Real.log (4003 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (197104329 / 1000000000) ≤ -Real.log (10240 / 12471) ∧
    -Real.log (10240 / 12471) ≤ (19710433 / 100000000) := by
  have h := checkLog_sound (w := (2231 / 22711)) (n := 12)
    (lo := (197104329 / 1000000000)) (hi := (19710433 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12471 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12471 / 10240) = 1/(10240 / 12471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (197104329 / 1000000000) (19710433 / 100000000) (Real.log (12471 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12471 / 10240) = -Real.log (10240 / 12471) := by
    rw [show ((12471 / 10240) : ℝ) = ((10240 / 12471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (24573571 / 100000000) ≤ -Real.log (8009 / 10240) ∧
    -Real.log (8009 / 10240) ≤ (245735711 / 1000000000) := by
  have h := checkLog_sound (w := (2231 / 18249)) (n := 12)
    (lo := (24573571 / 100000000)) (hi := (245735711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8009) = 1/(8009 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-245735711 / 1000000000) (-24573571 / 100000000) (Real.log (8009 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (362089943 / 1000000000) ≤ -Real.log (2560 / 3677) ∧
    -Real.log (2560 / 3677) ≤ (45261243 / 125000000) := by
  have h := checkLog_sound (w := (1117 / 6237)) (n := 12)
    (lo := (362089943 / 1000000000)) (hi := (45261243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3677 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3677 / 2560) = 1/(2560 / 3677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (362089943 / 1000000000) (45261243 / 125000000) (Real.log (3677 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3677 / 2560) = -Real.log (2560 / 3677) := by
    rw [show ((3677 / 2560) : ℝ) = ((2560 / 3677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286641489 / 500000000) ≤ -Real.log (1443 / 2560) ∧
    -Real.log (1443 / 2560) ≤ (573282979 / 1000000000) := by
  have h := checkLog_sound (w := (1117 / 4003)) (n := 12)
    (lo := (286641489 / 500000000)) (hi := (573282979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1443) = 1/(1443 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-573282979 / 1000000000) (-286641489 / 500000000) (Real.log (1443 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (361681919 / 1000000000) ≤ -Real.log (5120 / 7351) ∧
    -Real.log (5120 / 7351) ≤ (141282 / 390625) := by
  have h := checkLog_sound (w := (2231 / 12471)) (n := 12)
    (lo := (361681919 / 1000000000)) (hi := (141282 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7351 / 5120) = 1/(5120 / 7351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (361681919 / 1000000000) (141282 / 390625) (Real.log (7351 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7351 / 5120) = -Real.log (5120 / 7351) := by
    rw [show ((7351 / 5120) : ℝ) = ((5120 / 7351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (572244017 / 1000000000) ≤ -Real.log (2889 / 5120) ∧
    -Real.log (2889 / 5120) ≤ (286122009 / 500000000) := by
  have h := checkLog_sound (w := (2231 / 8009)) (n := 12)
    (lo := (572244017 / 1000000000)) (hi := (286122009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2889) = 1/(2889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-286122009 / 500000000) (-572244017 / 1000000000) (Real.log (2889 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135306231 / 500000000) ≤ -Real.log (1000000 / 1310767) ∧
    -Real.log (1000000 / 1310767) ≤ (270612463 / 1000000000) := by
  have h := checkLog_sound (w := (310767 / 2310767)) (n := 12)
    (lo := (135306231 / 500000000)) (hi := (270612463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310767 / 1000000) = 1/(1000000 / 1310767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135306231 / 500000000) (270612463 / 1000000000) (Real.log (1310767 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1310767 / 1000000) = -Real.log (1000000 / 1310767) := by
    rw [show ((1310767 / 1000000) : ℝ) = ((1000000 / 1310767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (372175893 / 1000000000) ≤ -Real.log (689233 / 1000000) ∧
    -Real.log (689233 / 1000000) ≤ (186087947 / 500000000) := by
  have h := checkLog_sound (w := (310767 / 1689233)) (n := 12)
    (lo := (372175893 / 1000000000)) (hi := (186087947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689233) = 1/(689233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186087947 / 500000000) (-372175893 / 1000000000) (Real.log (689233 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67734543 / 250000000) ≤ -Real.log (500000 / 655597) ∧
    -Real.log (500000 / 655597) ≤ (270938173 / 1000000000) := by
  have h := checkLog_sound (w := (155597 / 1155597)) (n := 12)
    (lo := (67734543 / 250000000)) (hi := (270938173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655597 / 500000) = 1/(500000 / 655597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67734543 / 250000000) (270938173 / 1000000000) (Real.log (655597 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (655597 / 500000) = -Real.log (500000 / 655597) := by
    rw [show ((655597 / 500000) : ℝ) = ((500000 / 655597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (74559123 / 200000000) ≤ -Real.log (344403 / 500000) ∧
    -Real.log (344403 / 500000) ≤ (11649863 / 31250000) := by
  have h := checkLog_sound (w := (155597 / 844403)) (n := 12)
    (lo := (74559123 / 200000000)) (hi := (11649863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 344403) = 1/(344403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11649863 / 31250000) (-74559123 / 200000000) (Real.log (344403 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (203579007 / 1000000000) ≤ -Real.log (500000 / 612891) ∧
    -Real.log (500000 / 612891) ≤ (1590461 / 7812500) := by
  have h := checkLog_sound (w := (112891 / 1112891)) (n := 12)
    (lo := (203579007 / 1000000000)) (hi := (1590461 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612891 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612891 / 500000) = 1/(500000 / 612891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (203579007 / 1000000000) (1590461 / 7812500) (Real.log (612891 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (612891 / 500000) = -Real.log (500000 / 612891) := by
    rw [show ((612891 / 500000) : ℝ) = ((500000 / 612891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (255901791 / 1000000000) ≤ -Real.log (387109 / 500000) ∧
    -Real.log (387109 / 500000) ≤ (7996931 / 31250000) := by
  have h := checkLog_sound (w := (112891 / 887109)) (n := 12)
    (lo := (255901791 / 1000000000)) (hi := (7996931 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387109) = 1/(387109 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7996931 / 31250000) (-255901791 / 1000000000) (Real.log (387109 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10192287 / 50000000) ≤ -Real.log (1000000 / 1226109) ∧
    -Real.log (1000000 / 1226109) ≤ (203845741 / 1000000000) := by
  have h := checkLog_sound (w := (226109 / 2226109)) (n := 12)
    (lo := (10192287 / 50000000)) (hi := (203845741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226109 / 1000000) = 1/(1000000 / 1226109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10192287 / 50000000) (203845741 / 1000000000) (Real.log (1226109 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1226109 / 1000000) = -Real.log (1000000 / 1226109) := by
    rw [show ((1226109 / 1000000) : ℝ) = ((1000000 / 1226109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (128162121 / 500000000) ≤ -Real.log (773891 / 1000000) ∧
    -Real.log (773891 / 1000000) ≤ (256324243 / 1000000000) := by
  have h := checkLog_sound (w := (226109 / 1773891)) (n := 12)
    (lo := (128162121 / 500000000)) (hi := (256324243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773891) = 1/(773891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-256324243 / 1000000000) (-128162121 / 500000000) (Real.log (773891 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (128557671 / 200000000) ≤ -Real.log (500000000000 / 950888161187) ∧
    -Real.log (500000000000 / 950888161187) ≤ (160697089 / 250000000) := by
  have h := checkLog_sound (w := (450888161187 / 1450888161187)) (n := 12)
    (lo := (128557671 / 200000000)) (hi := (160697089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950888161187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950888161187 / 500000000000) = 1/(500000000000 / 950888161187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (128557671 / 200000000) (160697089 / 250000000) (Real.log (950888161187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (950888161187 / 500000000000) = -Real.log (500000000000 / 950888161187) := by
    rw [show ((950888161187 / 500000000000) : ℝ) = ((500000000000 / 950888161187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (643733787 / 1000000000) ≤ -Real.log (100000000000 / 190357517211) ∧
    -Real.log (100000000000 / 190357517211) ≤ (160933447 / 250000000) := by
  have h := checkLog_sound (w := (90357517211 / 290357517211)) (n := 12)
    (lo := (643733787 / 1000000000)) (hi := (160933447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190357517211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190357517211 / 100000000000) = 1/(100000000000 / 190357517211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (643733787 / 1000000000) (160933447 / 250000000) (Real.log (190357517211 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (190357517211 / 100000000000) = -Real.log (100000000000 / 190357517211) := by
    rw [show ((190357517211 / 100000000000) : ℝ) = ((100000000000 / 190357517211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229740399 / 500000000) ≤ -Real.log (31250000000 / 49476617051) ∧
    -Real.log (31250000000 / 49476617051) ≤ (459480799 / 1000000000) := by
  have h := checkLog_sound (w := (18226617051 / 80726617051)) (n := 12)
    (lo := (229740399 / 500000000)) (hi := (459480799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49476617051 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49476617051 / 31250000000) = 1/(31250000000 / 49476617051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229740399 / 500000000) (459480799 / 1000000000) (Real.log (49476617051 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49476617051 / 31250000000) = -Real.log (31250000000 / 49476617051) := by
    rw [show ((49476617051 / 31250000000) : ℝ) = ((31250000000 / 49476617051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (230084991 / 500000000) ≤ -Real.log (20000000000 / 31686865463) ∧
    -Real.log (20000000000 / 31686865463) ≤ (460169983 / 1000000000) := by
  have h := checkLog_sound (w := (11686865463 / 51686865463)) (n := 12)
    (lo := (230084991 / 500000000)) (hi := (460169983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31686865463 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31686865463 / 20000000000) = 1/(20000000000 / 31686865463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (230084991 / 500000000) (460169983 / 1000000000) (Real.log (31686865463 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31686865463 / 20000000000) = -Real.log (20000000000 / 31686865463) := by
    rw [show ((31686865463 / 20000000000) : ℝ) = ((20000000000 / 31686865463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0412
