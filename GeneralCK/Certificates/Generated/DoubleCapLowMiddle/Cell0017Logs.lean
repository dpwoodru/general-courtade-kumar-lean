import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0017
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

theorem reflection_log_1_neg : (682159299 / 1000000000) ≤ -Real.log (51200 / 101281) ∧
    -Real.log (51200 / 101281) ≤ (6821593 / 10000000) := by
  have h := checkLog_sound (w := (50081 / 152481)) (n := 12)
    (lo := (682159299 / 1000000000)) (hi := (6821593 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101281 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101281 / 51200) = 1/(51200 / 101281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682159299 / 1000000000) (6821593 / 10000000) (Real.log (101281 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101281 / 51200) = -Real.log (51200 / 101281) := by
    rw [show ((101281 / 51200) : ℝ) = ((51200 / 101281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3823304099 / 1000000000) ≤ -Real.log (1119 / 51200) ∧
    -Real.log (1119 / 51200) ≤ (764660821 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1119) = 1/(1119 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-764660821 / 200000000) (-3823304099 / 1000000000) (Real.log (1119 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682065497 / 1000000000) ≤ -Real.log (102400 / 202543) ∧
    -Real.log (102400 / 202543) ≤ (341032749 / 500000000) := by
  have h := checkLog_sound (w := (100143 / 304943)) (n := 12)
    (lo := (682065497 / 1000000000)) (hi := (341032749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202543 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202543 / 102400) = 1/(102400 / 202543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682065497 / 1000000000) (341032749 / 500000000) (Real.log (202543 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202543 / 102400) = -Real.log (102400 / 202543) := by
    rw [show ((202543 / 102400) : ℝ) = ((102400 / 202543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3814850211 / 1000000000) ≤ -Real.log (2257 / 102400) ∧
    -Real.log (2257 / 102400) ≤ (3814850217 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2257) = 1/(2257 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3814850217 / 1000000000) (-3814850211 / 1000000000) (Real.log (2257 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671049343 / 1000000000) ≤ -Real.log (25600 / 50081) ∧
    -Real.log (25600 / 50081) ≤ (5242573 / 7812500) := by
  have h := checkLog_sound (w := (24481 / 75681)) (n := 12)
    (lo := (671049343 / 1000000000)) (hi := (5242573 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50081 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50081 / 25600) = 1/(25600 / 50081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671049343 / 1000000000) (5242573 / 7812500) (Real.log (50081 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50081 / 25600) = -Real.log (25600 / 50081) := by
    rw [show ((50081 / 25600) : ℝ) = ((25600 / 50081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3130156919 / 1000000000) ≤ -Real.log (1119 / 25600) ∧
    -Real.log (1119 / 25600) ≤ (782539231 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1119) = 1/(1119 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-782539231 / 250000000) (-3130156919 / 1000000000) (Real.log (1119 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41928727 / 62500000) ≤ -Real.log (51200 / 100143) ∧
    -Real.log (51200 / 100143) ≤ (670859633 / 1000000000) := by
  have h := checkLog_sound (w := (48943 / 151343)) (n := 12)
    (lo := (41928727 / 62500000)) (hi := (670859633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100143 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100143 / 51200) = 1/(51200 / 100143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41928727 / 62500000) (670859633 / 1000000000) (Real.log (100143 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100143 / 51200) = -Real.log (51200 / 100143) := by
    rw [show ((100143 / 51200) : ℝ) = ((51200 / 100143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3121703031 / 1000000000) ≤ -Real.log (2257 / 51200) ∧
    -Real.log (2257 / 51200) ≤ (780425759 / 250000000) := by
  have h := checkLog_sound (w := (943 / 5457)) (n := 12)
    (lo := (349114311 / 1000000000)) (hi := (43639289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2257) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2257) = 1/(2257 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-780425759 / 250000000) (-3121703031 / 1000000000) (Real.log (2257 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341882149 / 500000000) ≤ -Real.log (500000 / 990661) ∧
    -Real.log (500000 / 990661) ≤ (683764299 / 1000000000) := by
  have h := checkLog_sound (w := (490661 / 1490661)) (n := 12)
    (lo := (341882149 / 500000000)) (hi := (683764299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990661 / 500000) = 1/(500000 / 990661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341882149 / 500000000) (683764299 / 1000000000) (Real.log (990661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990661 / 500000) = -Real.log (500000 / 990661) := by
    rw [show ((990661 / 500000) : ℝ) = ((500000 / 990661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (796081783 / 200000000) ≤ -Real.log (9339 / 500000) ∧
    -Real.log (9339 / 500000) ≤ (3980408921 / 1000000000) := by
  have h := checkLog_sound (w := (3143 / 12482)) (n := 12)
    (lo := (102934603 / 200000000)) (hi := (64334127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9339) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9339) = 1/(9339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3980408921 / 1000000000) (-796081783 / 200000000) (Real.log (9339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170960253 / 250000000) ≤ -Real.log (500000 / 990737) ∧
    -Real.log (500000 / 990737) ≤ (683841013 / 1000000000) := by
  have h := checkLog_sound (w := (490737 / 1490737)) (n := 12)
    (lo := (170960253 / 250000000)) (hi := (683841013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990737 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990737 / 500000) = 1/(500000 / 990737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170960253 / 250000000) (683841013 / 1000000000) (Real.log (990737 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (990737 / 500000) = -Real.log (500000 / 990737) := by
    rw [show ((990737 / 500000) : ℝ) = ((500000 / 990737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31908641 / 8000000) ≤ -Real.log (9263 / 500000) ∧
    -Real.log (9263 / 500000) ≤ (3988580131 / 1000000000) := by
  have h := checkLog_sound (w := (3181 / 12444)) (n := 12)
    (lo := (20913769 / 40000000)) (hi := (261422113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9263) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9263) = 1/(9263 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3988580131 / 1000000000) (-31908641 / 8000000) (Real.log (9263 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683725939 / 1000000000) ≤ -Real.log (500000 / 990623) ∧
    -Real.log (500000 / 990623) ≤ (34186297 / 50000000) := by
  have h := checkLog_sound (w := (490623 / 1490623)) (n := 12)
    (lo := (683725939 / 1000000000)) (hi := (34186297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990623 / 500000) = 1/(500000 / 990623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683725939 / 1000000000) (34186297 / 50000000) (Real.log (990623 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990623 / 500000) = -Real.log (500000 / 990623) := by
    rw [show ((990623 / 500000) : ℝ) = ((500000 / 990623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3976348213 / 1000000000) ≤ -Real.log (9377 / 500000) ∧
    -Real.log (9377 / 500000) ≤ (3976348219 / 1000000000) := by
  have h := checkLog_sound (w := (3124 / 12501)) (n := 12)
    (lo := (510612313 / 1000000000)) (hi := (255306157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9377) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9377) = 1/(9377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3976348219 / 1000000000) (-3976348213 / 1000000000) (Real.log (9377 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (17095079 / 25000000) ≤ -Real.log (1000000 / 1981399) ∧
    -Real.log (1000000 / 1981399) ≤ (683803161 / 1000000000) := by
  have h := checkLog_sound (w := (981399 / 2981399)) (n := 12)
    (lo := (17095079 / 25000000)) (hi := (683803161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981399 / 1000000) = 1/(1000000 / 1981399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (17095079 / 25000000) (683803161 / 1000000000) (Real.log (1981399 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981399 / 1000000) = -Real.log (1000000 / 1981399) := by
    rw [show ((1981399 / 1000000) : ℝ) = ((1000000 / 1981399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3984539933 / 1000000000) ≤ -Real.log (18601 / 1000000) ∧
    -Real.log (18601 / 1000000) ≤ (3984539939 / 1000000000) := by
  have h := checkLog_sound (w := (12649 / 49851)) (n := 12)
    (lo := (518804033 / 1000000000)) (hi := (259402017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18601) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18601) = 1/(18601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3984539939 / 1000000000) (-3984539933 / 1000000000) (Real.log (18601 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4664173213 / 1000000000) ≤ -Real.log (500000000000 / 53038922796873) ∧
    -Real.log (500000000000 / 53038922796873) ≤ (233208661 / 50000000) := by
  have h := checkLog_sound (w := (21038922796873 / 85038922796873)) (n := 12)
    (lo := (505290133 / 1000000000)) (hi := (252645067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53038922796873 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53038922796873 / 32000000000000) = 1/(500000000000 / 53038922796873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4664173213 / 1000000000) (233208661 / 50000000) (Real.log (53038922796873 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (53038922796873 / 500000000000) = -Real.log (500000000000 / 53038922796873) := by
    rw [show ((53038922796873 / 500000000000) : ℝ) = ((500000000000 / 53038922796873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292026321 / 62500000) ≤ -Real.log (100000000000 / 10695638562021) ∧
    -Real.log (100000000000 / 10695638562021) ≤ (4672421143 / 1000000000) := by
  have h := checkLog_sound (w := (4295638562021 / 17095638562021)) (n := 12)
    (lo := (64192257 / 125000000)) (hi := (513538057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10695638562021 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10695638562021 / 6400000000000) = 1/(100000000000 / 10695638562021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292026321 / 62500000) (4672421143 / 1000000000) (Real.log (10695638562021 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10695638562021 / 100000000000) = -Real.log (100000000000 / 10695638562021) := by
    rw [show ((10695638562021 / 100000000000) : ℝ) = ((100000000000 / 10695638562021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (582509269 / 125000000) ≤ -Real.log (500000000000 / 52821957982297) ∧
    -Real.log (500000000000 / 52821957982297) ≤ (4660074159 / 1000000000) := by
  have h := checkLog_sound (w := (20821957982297 / 84821957982297)) (n := 12)
    (lo := (15662221 / 31250000)) (hi := (501191073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52821957982297 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52821957982297 / 32000000000000) = 1/(500000000000 / 52821957982297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (582509269 / 125000000) (4660074159 / 1000000000) (Real.log (52821957982297 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52821957982297 / 500000000000) = -Real.log (500000000000 / 52821957982297) := by
    rw [show ((52821957982297 / 500000000000) : ℝ) = ((500000000000 / 52821957982297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4668343093 / 1000000000) ≤ -Real.log (250000000000 / 26630275254019) ∧
    -Real.log (250000000000 / 26630275254019) ≤ (46683431 / 10000000) := by
  have h := checkLog_sound (w := (10630275254019 / 42630275254019)) (n := 12)
    (lo := (509460013 / 1000000000)) (hi := (254730007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26630275254019 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(26630275254019 / 16000000000000) = 1/(250000000000 / 26630275254019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4668343093 / 1000000000) (46683431 / 10000000) (Real.log (26630275254019 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (26630275254019 / 250000000000) = -Real.log (250000000000 / 26630275254019) := by
    rw [show ((26630275254019 / 250000000000) : ℝ) = ((250000000000 / 26630275254019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0017
