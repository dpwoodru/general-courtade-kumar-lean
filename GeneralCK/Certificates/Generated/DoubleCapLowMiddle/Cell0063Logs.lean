import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063
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

theorem reflection_log_1_neg : (169458809 / 250000000) ≤ -Real.log (12800 / 25211) ∧
    -Real.log (12800 / 25211) ≤ (677835237 / 1000000000) := by
  have h := checkLog_sound (w := (12411 / 38011)) (n := 12)
    (lo := (169458809 / 250000000)) (hi := (677835237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25211 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25211 / 12800) = 1/(12800 / 25211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169458809 / 250000000) (677835237 / 1000000000) (Real.log (25211 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25211 / 12800) = -Real.log (12800 / 25211) := by
    rw [show ((25211 / 12800) : ℝ) = ((12800 / 25211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3493621103 / 1000000000) ≤ -Real.log (389 / 12800) ∧
    -Real.log (389 / 12800) ≤ (3493621109 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 389) = 1/(389 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3493621109 / 1000000000) (-3493621103 / 1000000000) (Real.log (389 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (338870513 / 500000000) ≤ -Real.log (102400 / 201669) ∧
    -Real.log (102400 / 201669) ≤ (677741027 / 1000000000) := by
  have h := checkLog_sound (w := (99269 / 304069)) (n := 12)
    (lo := (338870513 / 500000000)) (hi := (677741027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201669 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201669 / 102400) = 1/(102400 / 201669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (338870513 / 500000000) (677741027 / 1000000000) (Real.log (201669 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201669 / 102400) = -Real.log (102400 / 201669) := by
    rw [show ((201669 / 102400) : ℝ) = ((102400 / 201669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3487534267 / 1000000000) ≤ -Real.log (3131 / 102400) ∧
    -Real.log (3131 / 102400) ≤ (3487534273 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3131) = 1/(3131 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3487534273 / 1000000000) (-3487534267 / 1000000000) (Real.log (3131 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132457037 / 200000000) ≤ -Real.log (6400 / 12411) ∧
    -Real.log (6400 / 12411) ≤ (331142593 / 500000000) := by
  have h := checkLog_sound (w := (6011 / 18811)) (n := 12)
    (lo := (132457037 / 200000000)) (hi := (331142593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 6400) = 1/(6400 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132457037 / 200000000) (331142593 / 500000000) (Real.log (12411 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12411 / 6400) = -Real.log (6400 / 12411) := by
    rw [show ((12411 / 6400) : ℝ) = ((6400 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2800473923 / 1000000000) ≤ -Real.log (389 / 6400) ∧
    -Real.log (389 / 6400) ≤ (350059241 / 125000000) := by
  have h := checkLog_sound (w := (11 / 789)) (n := 12)
    (lo := (27885203 / 1000000000)) (hi := (6971301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 389) = 1/(389 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-350059241 / 125000000) (-2800473923 / 1000000000) (Real.log (389 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165523451 / 250000000) ≤ -Real.log (51200 / 99269) ∧
    -Real.log (51200 / 99269) ≤ (132418761 / 200000000) := by
  have h := checkLog_sound (w := (48069 / 150469)) (n := 12)
    (lo := (165523451 / 250000000)) (hi := (132418761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99269 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99269 / 51200) = 1/(51200 / 99269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165523451 / 250000000) (132418761 / 200000000) (Real.log (99269 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99269 / 51200) = -Real.log (51200 / 99269) := by
    rw [show ((99269 / 51200) : ℝ) = ((51200 / 99269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2794387087 / 1000000000) ≤ -Real.log (3131 / 51200) ∧
    -Real.log (3131 / 51200) ≤ (698596773 / 250000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3131) = 1/(3131 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-698596773 / 250000000) (-2794387087 / 1000000000) (Real.log (3131 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680295449 / 1000000000) ≤ -Real.log (1000000 / 1974461) ∧
    -Real.log (1000000 / 1974461) ≤ (13605909 / 20000000) := by
  have h := checkLog_sound (w := (974461 / 2974461)) (n := 12)
    (lo := (680295449 / 1000000000)) (hi := (13605909 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974461 / 1000000) = 1/(1000000 / 1974461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680295449 / 1000000000) (13605909 / 20000000) (Real.log (1974461 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974461 / 1000000) = -Real.log (1000000 / 1974461) := by
    rw [show ((1974461 / 1000000) : ℝ) = ((1000000 / 1974461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (183377429 / 50000000) ≤ -Real.log (25539 / 1000000) ∧
    -Real.log (25539 / 1000000) ≤ (1833774293 / 500000000) := by
  have h := checkLog_sound (w := (5711 / 56789)) (n := 12)
    (lo := (5045317 / 25000000)) (hi := (201812681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25539) = 1/(25539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1833774293 / 500000000) (-183377429 / 50000000) (Real.log (25539 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68037091 / 100000000) ≤ -Real.log (100000 / 197461) ∧
    -Real.log (100000 / 197461) ≤ (680370911 / 1000000000) := by
  have h := checkLog_sound (w := (97461 / 297461)) (n := 12)
    (lo := (68037091 / 100000000)) (hi := (680370911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197461 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197461 / 100000) = 1/(100000 / 197461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68037091 / 100000000) (680370911 / 1000000000) (Real.log (197461 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (197461 / 100000) = -Real.log (100000 / 197461) := by
    rw [show ((197461 / 100000) : ℝ) = ((100000 / 197461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (91834997 / 25000000) ≤ -Real.log (2539 / 100000) ∧
    -Real.log (2539 / 100000) ≤ (1836699943 / 500000000) := by
  have h := checkLog_sound (w := (293 / 2832)) (n := 12)
    (lo := (10383199 / 50000000)) (hi := (207663981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2539) = 1/(2539 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1836699943 / 500000000) (-91834997 / 25000000) (Real.log (2539 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5314183 / 7812500) ≤ -Real.log (1000000 / 1974303) ∧
    -Real.log (1000000 / 1974303) ≤ (27208617 / 40000000) := by
  have h := checkLog_sound (w := (974303 / 2974303)) (n := 12)
    (lo := (5314183 / 7812500)) (hi := (27208617 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974303 / 1000000) = 1/(1000000 / 1974303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5314183 / 7812500) (27208617 / 40000000) (Real.log (1974303 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974303 / 1000000) = -Real.log (1000000 / 1974303) := by
    rw [show ((1974303 / 1000000) : ℝ) = ((1000000 / 1974303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1830690511 / 500000000) ≤ -Real.log (25697 / 1000000) ∧
    -Real.log (25697 / 1000000) ≤ (915345257 / 250000000) := by
  have h := checkLog_sound (w := (5553 / 56947)) (n := 12)
    (lo := (97822561 / 500000000)) (hi := (195645123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25697) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25697) = 1/(25697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-915345257 / 250000000) (-1830690511 / 500000000) (Real.log (25697 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10629561 / 15625000) ≤ -Real.log (500000 / 987227) ∧
    -Real.log (500000 / 987227) ≤ (136058381 / 200000000) := by
  have h := checkLog_sound (w := (487227 / 1487227)) (n := 12)
    (lo := (10629561 / 15625000)) (hi := (136058381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987227 / 500000) = 1/(500000 / 987227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10629561 / 15625000) (136058381 / 200000000) (Real.log (987227 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (987227 / 500000) = -Real.log (500000 / 987227) := by
    rw [show ((987227 / 500000) : ℝ) = ((500000 / 987227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3667274527 / 1000000000) ≤ -Real.log (12773 / 500000) ∧
    -Real.log (12773 / 500000) ≤ (3667274533 / 1000000000) := by
  have h := checkLog_sound (w := (1426 / 14199)) (n := 12)
    (lo := (201538627 / 1000000000)) (hi := (50384657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12773) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12773) = 1/(12773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3667274533 / 1000000000) (-3667274527 / 1000000000) (Real.log (12773 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4347844029 / 1000000000) ≤ -Real.log (125000000000 / 9663950232977) ∧
    -Real.log (125000000000 / 9663950232977) ≤ (1086961009 / 250000000) := by
  have h := checkLog_sound (w := (1663950232977 / 17663950232977)) (n := 12)
    (lo := (188960949 / 1000000000)) (hi := (3779219 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9663950232977 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9663950232977 / 8000000000000) = 1/(125000000000 / 9663950232977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4347844029 / 1000000000) (1086961009 / 250000000) (Real.log (9663950232977 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9663950232977 / 125000000000) = -Real.log (125000000000 / 9663950232977) := by
    rw [show ((9663950232977 / 125000000000) : ℝ) = ((125000000000 / 9663950232977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (435377079 / 100000000) ≤ -Real.log (15625000000 / 1215174527373) ∧
    -Real.log (15625000000 / 1215174527373) ≤ (4353770797 / 1000000000) := by
  have h := checkLog_sound (w := (215174527373 / 2215174527373)) (n := 12)
    (lo := (19488771 / 100000000)) (hi := (194887711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215174527373 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1215174527373 / 1000000000000) = 1/(15625000000 / 1215174527373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (435377079 / 100000000) (4353770797 / 1000000000) (Real.log (1215174527373 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1215174527373 / 15625000000) = -Real.log (15625000000 / 1215174527373) := by
    rw [show ((1215174527373 / 15625000000) : ℝ) = ((15625000000 / 1215174527373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2170798223 / 500000000) ≤ -Real.log (100000000000 / 7683009689847) ∧
    -Real.log (100000000000 / 7683009689847) ≤ (4341596453 / 1000000000) := by
  have h := checkLog_sound (w := (1283009689847 / 14083009689847)) (n := 12)
    (lo := (91356683 / 500000000)) (hi := (182713367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7683009689847 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7683009689847 / 6400000000000) = 1/(100000000000 / 7683009689847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2170798223 / 500000000) (4341596453 / 1000000000) (Real.log (7683009689847 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7683009689847 / 100000000000) = -Real.log (100000000000 / 7683009689847) := by
    rw [show ((7683009689847 / 100000000000) : ℝ) = ((100000000000 / 7683009689847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4347566431 / 1000000000) ≤ -Real.log (250000000000 / 19322535817741) ∧
    -Real.log (250000000000 / 19322535817741) ≤ (2173783219 / 500000000) := by
  have h := checkLog_sound (w := (3322535817741 / 35322535817741)) (n := 12)
    (lo := (188683351 / 1000000000)) (hi := (23585419 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19322535817741 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19322535817741 / 16000000000000) = 1/(250000000000 / 19322535817741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4347566431 / 1000000000) (2173783219 / 500000000) (Real.log (19322535817741 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19322535817741 / 250000000000) = -Real.log (250000000000 / 19322535817741) := by
    rw [show ((19322535817741 / 250000000000) : ℝ) = ((250000000000 / 19322535817741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063
