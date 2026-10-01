import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0106
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

theorem reflection_log_1_neg : (670270301 / 1000000000) ≤ -Real.log (12800 / 25021) ∧
    -Real.log (12800 / 25021) ≤ (335135151 / 500000000) := by
  have h := checkLog_sound (w := (12221 / 37821)) (n := 12)
    (lo := (670270301 / 1000000000)) (hi := (335135151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25021 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25021 / 12800) = 1/(12800 / 25021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (670270301 / 1000000000) (335135151 / 500000000) (Real.log (25021 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25021 / 12800) = -Real.log (12800 / 25021) := by
    rw [show ((25021 / 12800) : ℝ) = ((12800 / 25021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (309589797 / 100000000) ≤ -Real.log (579 / 12800) ∧
    -Real.log (579 / 12800) ≤ (123835919 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 579) = 1/(579 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-123835919 / 40000000) (-309589797 / 100000000) (Real.log (579 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (335040221 / 500000000) ≤ -Real.log (10240 / 20013) ∧
    -Real.log (10240 / 20013) ≤ (670080443 / 1000000000) := by
  have h := checkLog_sound (w := (9773 / 30253)) (n := 12)
    (lo := (335040221 / 500000000)) (hi := (670080443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 10240) = 1/(10240 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (335040221 / 500000000) (670080443 / 1000000000) (Real.log (20013 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20013 / 10240) = -Real.log (10240 / 20013) := by
    rw [show ((20013 / 10240) : ℝ) = ((10240 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1543863819 / 500000000) ≤ -Real.log (467 / 10240) ∧
    -Real.log (467 / 10240) ≤ (3087727643 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 467) = 1/(467 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3087727643 / 1000000000) (-1543863819 / 500000000) (Real.log (467 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (646857793 / 1000000000) ≤ -Real.log (6400 / 12221) ∧
    -Real.log (6400 / 12221) ≤ (323428897 / 500000000) := by
  have h := checkLog_sound (w := (5821 / 18621)) (n := 12)
    (lo := (646857793 / 1000000000)) (hi := (323428897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12221 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12221 / 6400) = 1/(6400 / 12221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (646857793 / 1000000000) (323428897 / 500000000) (Real.log (12221 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12221 / 6400) = -Real.log (6400 / 12221) := by
    rw [show ((12221 / 6400) : ℝ) = ((6400 / 12221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (240275079 / 100000000) ≤ -Real.log (579 / 6400) ∧
    -Real.log (579 / 6400) ≤ (1201375397 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1379)) (n := 12)
    (lo := (1293237 / 4000000)) (hi := (323309251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 579) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 579) = 1/(579 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1201375397 / 500000000) (-240275079 / 100000000) (Real.log (579 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (323234521 / 500000000) ≤ -Real.log (5120 / 9773) ∧
    -Real.log (5120 / 9773) ≤ (646469043 / 1000000000) := by
  have h := checkLog_sound (w := (4653 / 14893)) (n := 12)
    (lo := (323234521 / 500000000)) (hi := (646469043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9773 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9773 / 5120) = 1/(5120 / 9773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (323234521 / 500000000) (646469043 / 1000000000) (Real.log (9773 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9773 / 5120) = -Real.log (5120 / 9773) := by
    rw [show ((9773 / 5120) : ℝ) = ((5120 / 9773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1197290229 / 500000000) ≤ -Real.log (467 / 5120) ∧
    -Real.log (467 / 5120) ≤ (1197290231 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 467) = 1/(467 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1197290231 / 500000000) (-1197290229 / 500000000) (Real.log (467 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42145927 / 62500000) ≤ -Real.log (1000000 / 1962727) ∧
    -Real.log (1000000 / 1962727) ≤ (674334833 / 1000000000) := by
  have h := checkLog_sound (w := (962727 / 2962727)) (n := 12)
    (lo := (42145927 / 62500000)) (hi := (674334833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962727 / 1000000) = 1/(1000000 / 1962727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42145927 / 62500000) (674334833 / 1000000000) (Real.log (1962727 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1962727 / 1000000) = -Real.log (1000000 / 1962727) := by
    rw [show ((1962727 / 1000000) : ℝ) = ((1000000 / 1962727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (411185759 / 125000000) ≤ -Real.log (37273 / 1000000) ∧
    -Real.log (37273 / 1000000) ≤ (3289486077 / 1000000000) := by
  have h := checkLog_sound (w := (25227 / 99773)) (n := 12)
    (lo := (64612169 / 125000000)) (hi := (516897353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37273) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37273) = 1/(37273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3289486077 / 1000000000) (-411185759 / 125000000) (Real.log (37273 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674480537 / 1000000000) ≤ -Real.log (1000000 / 1963013) ∧
    -Real.log (1000000 / 1963013) ≤ (337240269 / 500000000) := by
  have h := checkLog_sound (w := (963013 / 2963013)) (n := 12)
    (lo := (674480537 / 1000000000)) (hi := (337240269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963013 / 1000000) = 1/(1000000 / 1963013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674480537 / 1000000000) (337240269 / 500000000) (Real.log (1963013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963013 / 1000000) = -Real.log (1000000 / 1963013) := by
    rw [show ((1963013 / 1000000) : ℝ) = ((1000000 / 1963013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3297188777 / 1000000000) ≤ -Real.log (36987 / 1000000) ∧
    -Real.log (36987 / 1000000) ≤ (1648594391 / 500000000) := by
  have h := checkLog_sound (w := (25513 / 99487)) (n := 12)
    (lo := (524600057 / 1000000000)) (hi := (262300029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36987) = 1/(36987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1648594391 / 500000000) (-3297188777 / 1000000000) (Real.log (36987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674136109 / 1000000000) ≤ -Real.log (1000000 / 1962337) ∧
    -Real.log (1000000 / 1962337) ≤ (67413611 / 100000000) := by
  have h := checkLog_sound (w := (962337 / 2962337)) (n := 12)
    (lo := (674136109 / 1000000000)) (hi := (67413611 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962337 / 1000000) = 1/(1000000 / 1962337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674136109 / 1000000000) (67413611 / 100000000) (Real.log (1962337 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1962337 / 1000000) = -Real.log (1000000 / 1962337) := by
    rw [show ((1962337 / 1000000) : ℝ) = ((1000000 / 1962337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (409884637 / 125000000) ≤ -Real.log (37663 / 1000000) ∧
    -Real.log (37663 / 1000000) ≤ (3279077101 / 1000000000) := by
  have h := checkLog_sound (w := (24837 / 100163)) (n := 12)
    (lo := (63311047 / 125000000)) (hi := (506488377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37663) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37663) = 1/(37663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3279077101 / 1000000000) (-409884637 / 125000000) (Real.log (37663 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67428541 / 100000000) ≤ -Real.log (100000 / 196263) ∧
    -Real.log (100000 / 196263) ≤ (674285411 / 1000000000) := by
  have h := checkLog_sound (w := (96263 / 296263)) (n := 12)
    (lo := (67428541 / 100000000)) (hi := (674285411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196263 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196263 / 100000) = 1/(100000 / 196263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67428541 / 100000000) (674285411 / 1000000000) (Real.log (196263 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196263 / 100000) = -Real.log (100000 / 196263) := by
    rw [show ((196263 / 100000) : ℝ) = ((100000 / 196263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3286887033 / 1000000000) ≤ -Real.log (3737 / 100000) ∧
    -Real.log (3737 / 100000) ≤ (1643443519 / 500000000) := by
  have h := checkLog_sound (w := (2513 / 9987)) (n := 12)
    (lo := (514298313 / 1000000000)) (hi := (257149157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3737) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3737) = 1/(3737 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1643443519 / 500000000) (-3286887033 / 1000000000) (Real.log (3737 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (792764181 / 200000000) ≤ -Real.log (312500000 / 16455669989) ∧
    -Real.log (312500000 / 16455669989) ≤ (3963820911 / 1000000000) := by
  have h := checkLog_sound (w := (6455669989 / 26455669989)) (n := 12)
    (lo := (99617001 / 200000000)) (hi := (249042503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16455669989 / 10000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16455669989 / 10000000000) = 1/(312500000 / 16455669989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (792764181 / 200000000) (3963820911 / 1000000000) (Real.log (16455669989 / 312500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16455669989 / 312500000) = -Real.log (312500000 / 16455669989) := by
    rw [show ((16455669989 / 312500000) : ℝ) = ((312500000 / 16455669989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1985834657 / 500000000) ≤ -Real.log (100000000000 / 5307305269419) ∧
    -Real.log (100000000000 / 5307305269419) ≤ (99291733 / 25000000) := by
  have h := checkLog_sound (w := (2107305269419 / 8507305269419)) (n := 12)
    (lo := (252966707 / 500000000)) (hi := (101186683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5307305269419 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5307305269419 / 3200000000000) = 1/(100000000000 / 5307305269419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1985834657 / 500000000) (99291733 / 25000000) (Real.log (5307305269419 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5307305269419 / 100000000000) = -Real.log (100000000000 / 5307305269419) := by
    rw [show ((5307305269419 / 100000000000) : ℝ) = ((100000000000 / 5307305269419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (790642641 / 200000000) ≤ -Real.log (125000000000 / 6512814300507) ∧
    -Real.log (125000000000 / 6512814300507) ≤ (3953213211 / 1000000000) := by
  have h := checkLog_sound (w := (2512814300507 / 10512814300507)) (n := 12)
    (lo := (97495461 / 200000000)) (hi := (243738653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6512814300507 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6512814300507 / 4000000000000) = 1/(125000000000 / 6512814300507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (790642641 / 200000000) (3953213211 / 1000000000) (Real.log (6512814300507 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6512814300507 / 125000000000) = -Real.log (125000000000 / 6512814300507) := by
    rw [show ((6512814300507 / 125000000000) : ℝ) = ((125000000000 / 6512814300507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3961172443 / 1000000000) ≤ -Real.log (500000000000 / 26259432700027) ∧
    -Real.log (500000000000 / 26259432700027) ≤ (3961172449 / 1000000000) := by
  have h := checkLog_sound (w := (10259432700027 / 42259432700027)) (n := 12)
    (lo := (495436543 / 1000000000)) (hi := (1935299 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26259432700027 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26259432700027 / 16000000000000) = 1/(500000000000 / 26259432700027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3961172443 / 1000000000) (3961172449 / 1000000000) (Real.log (26259432700027 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26259432700027 / 500000000000) = -Real.log (500000000000 / 26259432700027) := by
    rw [show ((26259432700027 / 500000000000) : ℝ) = ((500000000000 / 26259432700027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0106
