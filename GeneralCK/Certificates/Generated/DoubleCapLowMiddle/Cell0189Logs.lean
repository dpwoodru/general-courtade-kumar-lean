import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0189
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

theorem reflection_log_1_neg : (122326407 / 200000000) ≤ -Real.log (3200 / 5899) ∧
    -Real.log (3200 / 5899) ≤ (152908009 / 250000000) := by
  have h := checkLog_sound (w := (2699 / 9099)) (n := 12)
    (lo := (122326407 / 200000000)) (hi := (152908009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 3200) = 1/(3200 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (122326407 / 200000000) (152908009 / 250000000) (Real.log (5899 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5899 / 3200) = -Real.log (3200 / 5899) := by
    rw [show ((5899 / 3200) : ℝ) = ((3200 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (927149993 / 500000000) ≤ -Real.log (501 / 3200) ∧
    -Real.log (501 / 3200) ≤ (1854299989 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 501) = 1/(501 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1854299989 / 1000000000) (-927149993 / 500000000) (Real.log (501 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (305010147 / 500000000) ≤ -Real.log (6400 / 11779) ∧
    -Real.log (6400 / 11779) ≤ (122004059 / 200000000) := by
  have h := checkLog_sound (w := (5379 / 18179)) (n := 12)
    (lo := (305010147 / 500000000)) (hi := (122004059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 6400) = 1/(6400 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (305010147 / 500000000) (122004059 / 200000000) (Real.log (11779 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11779 / 6400) = -Real.log (6400 / 11779) := by
    rw [show ((11779 / 6400) : ℝ) = ((6400 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36710309 / 20000000) ≤ -Real.log (1021 / 6400) ∧
    -Real.log (1021 / 6400) ≤ (1835515453 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1021) = 1/(1021 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1835515453 / 1000000000) (-36710309 / 20000000) (Real.log (1021 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (65359713 / 125000000) ≤ -Real.log (1600 / 2699) ∧
    -Real.log (1600 / 2699) ≤ (104575541 / 200000000) := by
  have h := checkLog_sound (w := (1099 / 4299)) (n := 12)
    (lo := (65359713 / 125000000)) (hi := (104575541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2699 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2699 / 1600) = 1/(1600 / 2699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (65359713 / 125000000) (104575541 / 200000000) (Real.log (2699 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2699 / 1600) = -Real.log (1600 / 2699) := by
    rw [show ((2699 / 1600) : ℝ) = ((1600 / 2699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (580576403 / 500000000) ≤ -Real.log (501 / 1600) ∧
    -Real.log (501 / 1600) ≤ (145144101 / 125000000) := by
  have h := checkLog_sound (w := (299 / 1301)) (n := 12)
    (lo := (234002813 / 500000000)) (hi := (468005627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 501) = 1/(501 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145144101 / 125000000) (-580576403 / 500000000) (Real.log (501 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (519351673 / 1000000000) ≤ -Real.log (3200 / 5379) ∧
    -Real.log (3200 / 5379) ≤ (259675837 / 500000000) := by
  have h := checkLog_sound (w := (2179 / 8579)) (n := 12)
    (lo := (519351673 / 1000000000)) (hi := (259675837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5379 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5379 / 3200) = 1/(3200 / 5379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (519351673 / 1000000000) (259675837 / 500000000) (Real.log (5379 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5379 / 3200) = -Real.log (3200 / 5379) := by
    rw [show ((5379 / 3200) : ℝ) = ((3200 / 5379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114236827 / 100000000) ≤ -Real.log (1021 / 3200) ∧
    -Real.log (1021 / 3200) ≤ (71398017 / 62500000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1021) = 1/(1021 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71398017 / 62500000) (-114236827 / 100000000) (Real.log (1021 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (634150077 / 1000000000) ≤ -Real.log (1000000 / 1885419) ∧
    -Real.log (1000000 / 1885419) ≤ (317075039 / 500000000) := by
  have h := checkLog_sound (w := (885419 / 2885419)) (n := 12)
    (lo := (634150077 / 1000000000)) (hi := (317075039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1885419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1885419 / 1000000) = 1/(1000000 / 1885419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (634150077 / 1000000000) (317075039 / 500000000) (Real.log (1885419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1885419 / 1000000) = -Real.log (1000000 / 1885419) := by
    rw [show ((1885419 / 1000000) : ℝ) = ((1000000 / 1885419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6770229 / 3125000) ≤ -Real.log (114581 / 1000000) ∧
    -Real.log (114581 / 1000000) ≤ (541618321 / 250000000) := by
  have h := checkLog_sound (w := (10419 / 239581)) (n := 12)
    (lo := (4351587 / 50000000)) (hi := (87031741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114581) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 114581) = 1/(114581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-541618321 / 250000000) (-6770229 / 3125000) (Real.log (114581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63508789 / 100000000) ≤ -Real.log (250000 / 471797) ∧
    -Real.log (250000 / 471797) ≤ (635087891 / 1000000000) := by
  have h := checkLog_sound (w := (221797 / 721797)) (n := 12)
    (lo := (63508789 / 100000000)) (hi := (635087891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471797 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471797 / 250000) = 1/(250000 / 471797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63508789 / 100000000) (635087891 / 1000000000) (Real.log (471797 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (471797 / 250000) = -Real.log (250000 / 471797) := by
    rw [show ((471797 / 250000) : ℝ) = ((250000 / 471797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27275407 / 12500000) ≤ -Real.log (28203 / 250000) ∧
    -Real.log (28203 / 250000) ≤ (545508141 / 250000000) := by
  have h := checkLog_sound (w := (3047 / 59453)) (n := 12)
    (lo := (5129551 / 50000000)) (hi := (102591021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28203) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 28203) = 1/(28203 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-545508141 / 250000000) (-27275407 / 12500000) (Real.log (28203 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315179563 / 500000000) ≤ -Real.log (200000 / 375657) ∧
    -Real.log (200000 / 375657) ≤ (630359127 / 1000000000) := by
  have h := checkLog_sound (w := (175657 / 575657)) (n := 12)
    (lo := (315179563 / 500000000)) (hi := (630359127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375657 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375657 / 200000) = 1/(200000 / 375657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315179563 / 500000000) (630359127 / 1000000000) (Real.log (375657 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (375657 / 200000) = -Real.log (200000 / 375657) := by
    rw [show ((375657 / 200000) : ℝ) = ((200000 / 375657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2106073031 / 1000000000) ≤ -Real.log (24343 / 200000) ∧
    -Real.log (24343 / 200000) ≤ (421214607 / 200000000) := by
  have h := checkLog_sound (w := (657 / 49343)) (n := 12)
    (lo := (26631491 / 1000000000)) (hi := (6657873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24343) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 24343) = 1/(24343 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-421214607 / 200000000) (-2106073031 / 1000000000) (Real.log (24343 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63146697 / 100000000) ≤ -Real.log (1000000 / 1880367) ∧
    -Real.log (1000000 / 1880367) ≤ (631466971 / 1000000000) := by
  have h := checkLog_sound (w := (880367 / 2880367)) (n := 12)
    (lo := (63146697 / 100000000)) (hi := (631466971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1880367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1880367 / 1000000) = 1/(1000000 / 1880367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63146697 / 100000000) (631466971 / 1000000000) (Real.log (1880367 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1880367 / 1000000) = -Real.log (1000000 / 1880367) := by
    rw [show ((1880367 / 1000000) : ℝ) = ((1000000 / 1880367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1061663277 / 500000000) ≤ -Real.log (119633 / 1000000) ∧
    -Real.log (119633 / 1000000) ≤ (1061663279 / 500000000) := by
  have h := checkLog_sound (w := (5367 / 244633)) (n := 12)
    (lo := (21942507 / 500000000)) (hi := (8777003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 119633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 119633) = 1/(119633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1061663279 / 500000000) (-1061663277 / 500000000) (Real.log (119633 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2800623357 / 1000000000) ≤ -Real.log (5000000000 / 82274504499) ∧
    -Real.log (5000000000 / 82274504499) ≤ (1400311681 / 500000000) := by
  have h := checkLog_sound (w := (2274504499 / 162274504499)) (n := 12)
    (lo := (28034637 / 1000000000)) (hi := (14017319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82274504499 / 80000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(82274504499 / 80000000000) = 1/(5000000000 / 82274504499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2800623357 / 1000000000) (1400311681 / 500000000) (Real.log (82274504499 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82274504499 / 5000000000) = -Real.log (5000000000 / 82274504499) := by
    rw [show ((82274504499 / 5000000000) : ℝ) = ((5000000000 / 82274504499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (56342409 / 20000000) ≤ -Real.log (250000000000 / 4182152607879) ∧
    -Real.log (250000000000 / 4182152607879) ≤ (563424091 / 200000000) := by
  have h := checkLog_sound (w := (182152607879 / 8182152607879)) (n := 12)
    (lo := (4453173 / 100000000)) (hi := (44531731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4182152607879 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4182152607879 / 4000000000000) = 1/(250000000000 / 4182152607879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (56342409 / 20000000) (563424091 / 200000000) (Real.log (4182152607879 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4182152607879 / 250000000000) = -Real.log (250000000000 / 4182152607879) := by
    rw [show ((4182152607879 / 250000000000) : ℝ) = ((250000000000 / 4182152607879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2736432157 / 1000000000) ≤ -Real.log (100000000000 / 1543182845171) ∧
    -Real.log (100000000000 / 1543182845171) ≤ (2736432161 / 1000000000) := by
  have h := checkLog_sound (w := (743182845171 / 2343182845171)) (n := 12)
    (lo := (656990617 / 1000000000)) (hi := (328495309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1543182845171 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1543182845171 / 800000000000) = 1/(100000000000 / 1543182845171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2736432157 / 1000000000) (2736432161 / 1000000000) (Real.log (1543182845171 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1543182845171 / 100000000000) = -Real.log (100000000000 / 1543182845171) := by
    rw [show ((1543182845171 / 100000000000) : ℝ) = ((100000000000 / 1543182845171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (688698381 / 250000000) ≤ -Real.log (500000000000 / 7858897628581) ∧
    -Real.log (500000000000 / 7858897628581) ≤ (344349191 / 125000000) := by
  have h := checkLog_sound (w := (3858897628581 / 11858897628581)) (n := 12)
    (lo := (42209499 / 62500000)) (hi := (135070397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7858897628581 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7858897628581 / 4000000000000) = 1/(500000000000 / 7858897628581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (688698381 / 250000000) (344349191 / 125000000) (Real.log (7858897628581 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7858897628581 / 500000000000) = -Real.log (500000000000 / 7858897628581) := by
    rw [show ((7858897628581 / 500000000000) : ℝ) = ((500000000000 / 7858897628581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0189
