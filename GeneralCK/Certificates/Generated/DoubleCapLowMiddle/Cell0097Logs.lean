import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0097
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

theorem reflection_log_1_neg : (10499647 / 15625000) ≤ -Real.log (10240 / 20051) ∧
    -Real.log (10240 / 20051) ≤ (671977409 / 1000000000) := by
  have h := checkLog_sound (w := (9811 / 30291)) (n := 12)
    (lo := (10499647 / 15625000)) (hi := (671977409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20051 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20051 / 10240) = 1/(10240 / 20051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10499647 / 15625000) (671977409 / 1000000000) (Real.log (20051 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20051 / 10240) = -Real.log (10240 / 20051) := by
    rw [show ((20051 / 10240) : ℝ) = ((10240 / 20051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3172599977 / 1000000000) ≤ -Real.log (429 / 10240) ∧
    -Real.log (429 / 10240) ≤ (1586299991 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 429) = 1/(429 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1586299991 / 500000000) (-3172599977 / 1000000000) (Real.log (429 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (671787873 / 1000000000) ≤ -Real.log (12800 / 25059) ∧
    -Real.log (12800 / 25059) ≤ (335893937 / 500000000) := by
  have h := checkLog_sound (w := (12259 / 37859)) (n := 12)
    (lo := (671787873 / 1000000000)) (hi := (335893937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25059 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25059 / 12800) = 1/(12800 / 25059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (671787873 / 1000000000) (335893937 / 500000000) (Real.log (25059 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25059 / 12800) = -Real.log (12800 / 25059) := by
    rw [show ((25059 / 12800) : ℝ) = ((12800 / 25059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197736323 / 62500000) ≤ -Real.log (541 / 12800) ∧
    -Real.log (541 / 12800) ≤ (3163781173 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 541) = 1/(541 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3163781173 / 1000000000) (-197736323 / 62500000) (Real.log (541 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (325174883 / 500000000) ≤ -Real.log (5120 / 9811) ∧
    -Real.log (5120 / 9811) ≤ (650349767 / 1000000000) := by
  have h := checkLog_sound (w := (4691 / 14931)) (n := 12)
    (lo := (325174883 / 500000000)) (hi := (650349767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9811 / 5120) = 1/(5120 / 9811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (325174883 / 500000000) (650349767 / 1000000000) (Real.log (9811 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9811 / 5120) = -Real.log (5120 / 9811) := by
    rw [show ((9811 / 5120) : ℝ) = ((5120 / 9811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2479452797 / 1000000000) ≤ -Real.log (429 / 5120) ∧
    -Real.log (429 / 5120) ≤ (2479452801 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 429) = 1/(429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2479452801 / 1000000000) (-2479452797 / 1000000000) (Real.log (429 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (64996237 / 100000000) ≤ -Real.log (6400 / 12259) ∧
    -Real.log (6400 / 12259) ≤ (649962371 / 1000000000) := by
  have h := checkLog_sound (w := (5859 / 18659)) (n := 12)
    (lo := (64996237 / 100000000)) (hi := (649962371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12259 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12259 / 6400) = 1/(6400 / 12259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (64996237 / 100000000) (649962371 / 1000000000) (Real.log (12259 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12259 / 6400) = -Real.log (6400 / 12259) := by
    rw [show ((12259 / 6400) : ℝ) = ((6400 / 12259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617658497 / 250000000) ≤ -Real.log (541 / 6400) ∧
    -Real.log (541 / 6400) ≤ (308829249 / 125000000) := by
  have h := checkLog_sound (w := (259 / 1341)) (n := 12)
    (lo := (3056191 / 7812500)) (hi := (391192449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 541) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 541) = 1/(541 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-308829249 / 125000000) (-617658497 / 250000000) (Real.log (541 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168911099 / 250000000) ≤ -Real.log (1000000 / 1965299) ∧
    -Real.log (1000000 / 1965299) ≤ (675644397 / 1000000000) := by
  have h := checkLog_sound (w := (965299 / 2965299)) (n := 12)
    (lo := (168911099 / 250000000)) (hi := (675644397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965299 / 1000000) = 1/(1000000 / 1965299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168911099 / 250000000) (675644397 / 1000000000) (Real.log (1965299 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1965299 / 1000000) = -Real.log (1000000 / 1965299) := by
    rw [show ((1965299 / 1000000) : ℝ) = ((1000000 / 1965299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3360986771 / 1000000000) ≤ -Real.log (34701 / 1000000) ∧
    -Real.log (34701 / 1000000) ≤ (420123347 / 125000000) := by
  have h := checkLog_sound (w := (27799 / 97201)) (n := 12)
    (lo := (588398051 / 1000000000)) (hi := (147099513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34701) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34701) = 1/(34701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-420123347 / 125000000) (-3360986771 / 1000000000) (Real.log (34701 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42236933 / 62500000) ≤ -Real.log (1000000 / 1965587) ∧
    -Real.log (1000000 / 1965587) ≤ (675790929 / 1000000000) := by
  have h := checkLog_sound (w := (965587 / 2965587)) (n := 12)
    (lo := (42236933 / 62500000)) (hi := (675790929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965587 / 1000000) = 1/(1000000 / 1965587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42236933 / 62500000) (675790929 / 1000000000) (Real.log (1965587 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1965587 / 1000000) = -Real.log (1000000 / 1965587) := by
    rw [show ((1965587 / 1000000) : ℝ) = ((1000000 / 1965587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (842330219 / 250000000) ≤ -Real.log (34413 / 1000000) ∧
    -Real.log (34413 / 1000000) ≤ (3369320881 / 1000000000) := by
  have h := checkLog_sound (w := (28087 / 96913)) (n := 12)
    (lo := (149183039 / 250000000)) (hi := (596732157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34413) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34413) = 1/(34413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3369320881 / 1000000000) (-842330219 / 250000000) (Real.log (34413 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337738743 / 500000000) ≤ -Real.log (1000000 / 1964971) ∧
    -Real.log (1000000 / 1964971) ≤ (675477487 / 1000000000) := by
  have h := checkLog_sound (w := (964971 / 2964971)) (n := 12)
    (lo := (337738743 / 500000000)) (hi := (675477487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1964971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1964971 / 1000000) = 1/(1000000 / 1964971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337738743 / 500000000) (675477487 / 1000000000) (Real.log (1964971 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1964971 / 1000000) = -Real.log (1000000 / 1964971) := by
    rw [show ((1964971 / 1000000) : ℝ) = ((1000000 / 1964971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1675789493 / 500000000) ≤ -Real.log (35029 / 1000000) ∧
    -Real.log (35029 / 1000000) ≤ (3351578991 / 1000000000) := by
  have h := checkLog_sound (w := (27471 / 97529)) (n := 12)
    (lo := (289495133 / 500000000)) (hi := (578990267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35029) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 35029) = 1/(35029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3351578991 / 1000000000) (-1675789493 / 500000000) (Real.log (35029 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84453387 / 125000000) ≤ -Real.log (200000 / 393053) ∧
    -Real.log (200000 / 393053) ≤ (675627097 / 1000000000) := by
  have h := checkLog_sound (w := (193053 / 593053)) (n := 12)
    (lo := (84453387 / 125000000)) (hi := (675627097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393053 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393053 / 200000) = 1/(200000 / 393053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84453387 / 125000000) (675627097 / 1000000000) (Real.log (393053 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393053 / 200000) = -Real.log (200000 / 393053) := by
    rw [show ((393053 / 200000) : ℝ) = ((200000 / 393053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (840001863 / 250000000) ≤ -Real.log (6947 / 200000) ∧
    -Real.log (6947 / 200000) ≤ (3360007457 / 1000000000) := by
  have h := checkLog_sound (w := (5553 / 19447)) (n := 12)
    (lo := (146854683 / 250000000)) (hi := (587418733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6947) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6947) = 1/(6947 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3360007457 / 1000000000) (-840001863 / 250000000) (Real.log (6947 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4036631167 / 1000000000) ≤ -Real.log (31250000000 / 1769850832829) ∧
    -Real.log (31250000000 / 1769850832829) ≤ (4036631173 / 1000000000) := by
  have h := checkLog_sound (w := (769850832829 / 2769850832829)) (n := 12)
    (lo := (570895267 / 1000000000)) (hi := (142723817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1769850832829 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1769850832829 / 1000000000000) = 1/(31250000000 / 1769850832829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4036631167 / 1000000000) (4036631173 / 1000000000) (Real.log (1769850832829 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1769850832829 / 31250000000) = -Real.log (31250000000 / 1769850832829) := by
    rw [show ((1769850832829 / 31250000000) : ℝ) = ((31250000000 / 1769850832829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1011277951 / 250000000) ≤ -Real.log (20000000000 / 1142351436957) ∧
    -Real.log (20000000000 / 1142351436957) ≤ (404511181 / 100000000) := by
  have h := checkLog_sound (w := (502351436957 / 1782351436957)) (n := 12)
    (lo := (18105497 / 31250000)) (hi := (115875181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142351436957 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1142351436957 / 640000000000) = 1/(20000000000 / 1142351436957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1011277951 / 250000000) (404511181 / 100000000) (Real.log (1142351436957 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1142351436957 / 20000000000) = -Real.log (20000000000 / 1142351436957) := by
    rw [show ((1142351436957 / 20000000000) : ℝ) = ((20000000000 / 1142351436957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4027056473 / 1000000000) ≤ -Real.log (250000000000 / 14023887350481) ∧
    -Real.log (250000000000 / 14023887350481) ≤ (4027056479 / 1000000000) := by
  have h := checkLog_sound (w := (6023887350481 / 22023887350481)) (n := 12)
    (lo := (561320573 / 1000000000)) (hi := (280660287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14023887350481 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14023887350481 / 8000000000000) = 1/(250000000000 / 14023887350481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4027056473 / 1000000000) (4027056479 / 1000000000) (Real.log (14023887350481 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14023887350481 / 250000000000) = -Real.log (250000000000 / 14023887350481) := by
    rw [show ((14023887350481 / 250000000000) : ℝ) = ((250000000000 / 14023887350481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1008908637 / 250000000) ≤ -Real.log (500000000000 / 28289405498777) ∧
    -Real.log (500000000000 / 28289405498777) ≤ (2017817277 / 500000000) := by
  have h := checkLog_sound (w := (12289405498777 / 44289405498777)) (n := 12)
    (lo := (71237331 / 125000000)) (hi := (569898649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28289405498777 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28289405498777 / 16000000000000) = 1/(500000000000 / 28289405498777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1008908637 / 250000000) (2017817277 / 500000000) (Real.log (28289405498777 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28289405498777 / 500000000000) = -Real.log (500000000000 / 28289405498777) := by
    rw [show ((28289405498777 / 500000000000) : ℝ) = ((500000000000 / 28289405498777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0097
