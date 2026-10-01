import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0165
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

theorem reflection_log_1_neg : (128354329 / 200000000) ≤ -Real.log (6400 / 12159) ∧
    -Real.log (6400 / 12159) ≤ (320885823 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 18559)) (n := 12)
    (lo := (128354329 / 200000000)) (hi := (320885823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12159 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12159 / 6400) = 1/(6400 / 12159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128354329 / 200000000) (320885823 / 500000000) (Real.log (12159 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12159 / 6400) = -Real.log (6400 / 12159) := by
    rw [show ((12159 / 6400) : ℝ) = ((6400 / 12159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230102381 / 100000000) ≤ -Real.log (641 / 6400) ∧
    -Real.log (641 / 6400) ≤ (1150511907 / 500000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 641) = 1/(641 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1150511907 / 500000000) (-230102381 / 100000000) (Real.log (641 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320495013 / 500000000) ≤ -Real.log (12800 / 24299) ∧
    -Real.log (12800 / 24299) ≤ (640990027 / 1000000000) := by
  have h := checkLog_sound (w := (11499 / 37099)) (n := 12)
    (lo := (320495013 / 500000000)) (hi := (640990027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24299 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24299 / 12800) = 1/(12800 / 24299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320495013 / 500000000) (640990027 / 1000000000) (Real.log (24299 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24299 / 12800) = -Real.log (12800 / 24299) := by
    rw [show ((24299 / 12800) : ℝ) = ((12800 / 24299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2286311969 / 1000000000) ≤ -Real.log (1301 / 12800) ∧
    -Real.log (1301 / 12800) ≤ (2286311973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1301) = 1/(1301 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2286311973 / 1000000000) (-2286311969 / 1000000000) (Real.log (1301 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (293806519 / 500000000) ≤ -Real.log (3200 / 5759) ∧
    -Real.log (3200 / 5759) ≤ (587613039 / 1000000000) := by
  have h := checkLog_sound (w := (2559 / 8959)) (n := 12)
    (lo := (293806519 / 500000000)) (hi := (587613039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 3200) = 1/(3200 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (293806519 / 500000000) (587613039 / 1000000000) (Real.log (5759 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5759 / 3200) = -Real.log (3200 / 5759) := by
    rw [show ((5759 / 3200) : ℝ) = ((3200 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (160787663 / 100000000) ≤ -Real.log (641 / 3200) ∧
    -Real.log (641 / 3200) ≤ (1607876633 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 641) = 1/(641 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1607876633 / 1000000000) (-160787663 / 100000000) (Real.log (641 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (146490521 / 250000000) ≤ -Real.log (6400 / 11499) ∧
    -Real.log (6400 / 11499) ≤ (117192417 / 200000000) := by
  have h := checkLog_sound (w := (5099 / 17899)) (n := 12)
    (lo := (146490521 / 250000000)) (hi := (117192417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11499 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11499 / 6400) = 1/(6400 / 11499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (146490521 / 250000000) (117192417 / 200000000) (Real.log (11499 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11499 / 6400) = -Real.log (6400 / 11499) := by
    rw [show ((11499 / 6400) : ℝ) = ((6400 / 11499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1593164789 / 1000000000) ≤ -Real.log (1301 / 6400) ∧
    -Real.log (1301 / 6400) ≤ (199145599 / 125000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1301) = 1/(1301 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-199145599 / 125000000) (-1593164789 / 1000000000) (Real.log (1301 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5105477 / 7812500) ≤ -Real.log (1000000 / 1922259) ∧
    -Real.log (1000000 / 1922259) ≤ (653501057 / 1000000000) := by
  have h := checkLog_sound (w := (922259 / 2922259)) (n := 12)
    (lo := (5105477 / 7812500)) (hi := (653501057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1922259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1922259 / 1000000) = 1/(1000000 / 1922259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5105477 / 7812500) (653501057 / 1000000000) (Real.log (1922259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1922259 / 1000000) = -Real.log (1000000 / 1922259) := by
    rw [show ((1922259 / 1000000) : ℝ) = ((1000000 / 1922259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (319296561 / 125000000) ≤ -Real.log (77741 / 1000000) ∧
    -Real.log (77741 / 1000000) ≤ (638593123 / 250000000) := by
  have h := checkLog_sound (w := (47259 / 202741)) (n := 12)
    (lo := (118732737 / 250000000)) (hi := (474930949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 77741) = 1/(77741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-638593123 / 250000000) (-319296561 / 125000000) (Real.log (77741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (327013431 / 500000000) ≤ -Real.log (100000 / 192327) ∧
    -Real.log (100000 / 192327) ≤ (654026863 / 1000000000) := by
  have h := checkLog_sound (w := (92327 / 292327)) (n := 12)
    (lo := (327013431 / 500000000)) (hi := (654026863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192327 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192327 / 100000) = 1/(100000 / 192327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (327013431 / 500000000) (654026863 / 1000000000) (Real.log (192327 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (192327 / 100000) = -Real.log (100000 / 192327) := by
    rw [show ((192327 / 100000) : ℝ) = ((100000 / 192327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2567462511 / 1000000000) ≤ -Real.log (7673 / 100000) ∧
    -Real.log (7673 / 100000) ≤ (513492503 / 200000000) := by
  have h := checkLog_sound (w := (4827 / 20173)) (n := 12)
    (lo := (488020971 / 1000000000)) (hi := (122005243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7673) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7673) = 1/(7673 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-513492503 / 200000000) (-2567462511 / 1000000000) (Real.log (7673 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326110767 / 500000000) ≤ -Real.log (1000000 / 1919801) ∧
    -Real.log (1000000 / 1919801) ≤ (130444307 / 200000000) := by
  have h := checkLog_sound (w := (919801 / 2919801)) (n := 12)
    (lo := (326110767 / 500000000)) (hi := (130444307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1919801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1919801 / 1000000) = 1/(1000000 / 1919801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326110767 / 500000000) (130444307 / 200000000) (Real.log (1919801 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1919801 / 1000000) = -Real.log (1000000 / 1919801) := by
    rw [show ((1919801 / 1000000) : ℝ) = ((1000000 / 1919801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2523244231 / 1000000000) ≤ -Real.log (80199 / 1000000) ∧
    -Real.log (80199 / 1000000) ≤ (504648847 / 200000000) := by
  have h := checkLog_sound (w := (44801 / 205199)) (n := 12)
    (lo := (443802691 / 1000000000)) (hi := (110950673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80199) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 80199) = 1/(80199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-504648847 / 200000000) (-2523244231 / 1000000000) (Real.log (80199 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (652791223 / 1000000000) ≤ -Real.log (200000 / 384179) ∧
    -Real.log (200000 / 384179) ≤ (81598903 / 125000000) := by
  have h := checkLog_sound (w := (184179 / 584179)) (n := 12)
    (lo := (652791223 / 1000000000)) (hi := (81598903 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384179 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384179 / 200000) = 1/(200000 / 384179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (652791223 / 1000000000) (81598903 / 125000000) (Real.log (384179 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (384179 / 200000) = -Real.log (200000 / 384179) := by
    rw [show ((384179 / 200000) : ℝ) = ((200000 / 384179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2536979193 / 1000000000) ≤ -Real.log (15821 / 200000) ∧
    -Real.log (15821 / 200000) ≤ (2536979197 / 1000000000) := by
  have h := checkLog_sound (w := (9179 / 40821)) (n := 12)
    (lo := (457537653 / 1000000000)) (hi := (228768827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15821) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 15821) = 1/(15821 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2536979197 / 1000000000) (-2536979193 / 1000000000) (Real.log (15821 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (400984193 / 125000000) ≤ -Real.log (250000000000 / 6181612662559) ∧
    -Real.log (250000000000 / 6181612662559) ≤ (3207873549 / 1000000000) := by
  have h := checkLog_sound (w := (2181612662559 / 10181612662559)) (n := 12)
    (lo := (54410603 / 125000000)) (hi := (17411393 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6181612662559 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6181612662559 / 4000000000000) = 1/(250000000000 / 6181612662559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (400984193 / 125000000) (3207873549 / 1000000000) (Real.log (6181612662559 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6181612662559 / 250000000000) = -Real.log (250000000000 / 6181612662559) := by
    rw [show ((6181612662559 / 250000000000) : ℝ) = ((250000000000 / 6181612662559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (805372343 / 250000000) ≤ -Real.log (50000000000 / 1253271210739) ∧
    -Real.log (50000000000 / 1253271210739) ≤ (3221489377 / 1000000000) := by
  have h := checkLog_sound (w := (453271210739 / 2053271210739)) (n := 12)
    (lo := (112225163 / 250000000)) (hi := (448900653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253271210739 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1253271210739 / 800000000000) = 1/(50000000000 / 1253271210739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (805372343 / 250000000) (3221489377 / 1000000000) (Real.log (1253271210739 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1253271210739 / 50000000000) = -Real.log (50000000000 / 1253271210739) := by
    rw [show ((1253271210739 / 50000000000) : ℝ) = ((50000000000 / 1253271210739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (635093153 / 200000000) ≤ -Real.log (500000000000 / 11968983403783) ∧
    -Real.log (500000000000 / 11968983403783) ≤ (317546577 / 100000000) := by
  have h := checkLog_sound (w := (3968983403783 / 19968983403783)) (n := 12)
    (lo := (80575409 / 200000000)) (hi := (201438523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11968983403783 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11968983403783 / 8000000000000) = 1/(500000000000 / 11968983403783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (635093153 / 200000000) (317546577 / 100000000) (Real.log (11968983403783 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11968983403783 / 500000000000) = -Real.log (500000000000 / 11968983403783) := by
    rw [show ((11968983403783 / 500000000000) : ℝ) = ((500000000000 / 11968983403783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (199360651 / 62500000) ≤ -Real.log (31250000000 / 758839122053) ∧
    -Real.log (31250000000 / 758839122053) ≤ (3189770421 / 1000000000) := by
  have h := checkLog_sound (w := (258839122053 / 1258839122053)) (n := 12)
    (lo := (814808 / 1953125)) (hi := (417181697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758839122053 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(758839122053 / 500000000000) = 1/(31250000000 / 758839122053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (199360651 / 62500000) (3189770421 / 1000000000) (Real.log (758839122053 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (758839122053 / 31250000000) = -Real.log (31250000000 / 758839122053) := by
    rw [show ((758839122053 / 31250000000) : ℝ) = ((31250000000 / 758839122053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0165
