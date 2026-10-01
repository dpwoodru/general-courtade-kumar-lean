import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0162
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

theorem reflection_log_1_neg : (128822569 / 200000000) ≤ -Real.log (512 / 975) ∧
    -Real.log (512 / 975) ≤ (322056423 / 500000000) := by
  have h := checkLog_sound (w := (463 / 1487)) (n := 12)
    (lo := (128822569 / 200000000)) (hi := (322056423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975 / 512) = 1/(512 / 975) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128822569 / 200000000) (322056423 / 500000000) (Real.log (975 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (975 / 512) = -Real.log (512 / 975) := by
    rw [show ((975 / 512) : ℝ) = ((512 / 975) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (93860173 / 40000000) ≤ -Real.log (49 / 512) ∧
    -Real.log (49 / 512) ≤ (2346504329 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 49) = 1/(49 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2346504329 / 1000000000) (-93860173 / 40000000) (Real.log (49 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (321666527 / 500000000) ≤ -Real.log (3200 / 6089) ∧
    -Real.log (3200 / 6089) ≤ (128666611 / 200000000) := by
  have h := checkLog_sound (w := (2889 / 9289)) (n := 12)
    (lo := (321666527 / 500000000)) (hi := (128666611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089 / 3200) = 1/(3200 / 6089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (321666527 / 500000000) (128666611 / 200000000) (Real.log (6089 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6089 / 3200) = -Real.log (3200 / 6089) := by
    rw [show ((6089 / 3200) : ℝ) = ((3200 / 6089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1165556587 / 500000000) ≤ -Real.log (311 / 3200) ∧
    -Real.log (311 / 3200) ≤ (1165556589 / 500000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 311) = 1/(311 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1165556589 / 500000000) (-1165556587 / 500000000) (Real.log (311 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (592549609 / 1000000000) ≤ -Real.log (256 / 463) ∧
    -Real.log (256 / 463) ≤ (59254961 / 100000000) := by
  have h := checkLog_sound (w := (207 / 719)) (n := 12)
    (lo := (592549609 / 1000000000)) (hi := (59254961 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 256) = 1/(256 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (592549609 / 1000000000) (59254961 / 100000000) (Real.log (463 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (463 / 256) = -Real.log (256 / 463) := by
    rw [show ((463 / 256) : ℝ) = ((256 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (330671429 / 200000000) ≤ -Real.log (49 / 256) ∧
    -Real.log (49 / 256) ≤ (413339287 / 250000000) := by
  have h := checkLog_sound (w := (15 / 113)) (n := 12)
    (lo := (53412557 / 200000000)) (hi := (133531393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 49) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 49) = 1/(49 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-413339287 / 250000000) (-330671429 / 200000000) (Real.log (49 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73863349 / 125000000) ≤ -Real.log (1600 / 2889) ∧
    -Real.log (1600 / 2889) ≤ (590906793 / 1000000000) := by
  have h := checkLog_sound (w := (1289 / 4489)) (n := 12)
    (lo := (73863349 / 125000000)) (hi := (590906793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 1600) = 1/(1600 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73863349 / 125000000) (590906793 / 1000000000) (Real.log (2889 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2889 / 1600) = -Real.log (1600 / 2889) := by
    rw [show ((2889 / 1600) : ℝ) = ((1600 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (818982997 / 500000000) ≤ -Real.log (311 / 1600) ∧
    -Real.log (311 / 1600) ≤ (1637965997 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 311) = 1/(311 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1637965997 / 1000000000) (-818982997 / 500000000) (Real.log (311 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2047129 / 3125000) ≤ -Real.log (1000000 / 1925299) ∧
    -Real.log (1000000 / 1925299) ≤ (655081281 / 1000000000) := by
  have h := checkLog_sound (w := (925299 / 2925299)) (n := 12)
    (lo := (2047129 / 3125000)) (hi := (655081281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1925299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1925299 / 1000000) = 1/(1000000 / 1925299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2047129 / 3125000) (655081281 / 1000000000) (Real.log (1925299 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1925299 / 1000000) = -Real.log (1000000 / 1925299) := by
    rw [show ((1925299 / 1000000) : ℝ) = ((1000000 / 1925299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1297130899 / 500000000) ≤ -Real.log (74701 / 1000000) ∧
    -Real.log (74701 / 1000000) ≤ (1297130901 / 500000000) := by
  have h := checkLog_sound (w := (50299 / 199701)) (n := 12)
    (lo := (257410129 / 500000000)) (hi := (514820259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74701) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 74701) = 1/(74701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1297130901 / 500000000) (-1297130899 / 500000000) (Real.log (74701 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (655611447 / 1000000000) ≤ -Real.log (12500 / 24079) ∧
    -Real.log (12500 / 24079) ≤ (81951431 / 125000000) := by
  have h := checkLog_sound (w := (11579 / 36579)) (n := 12)
    (lo := (655611447 / 1000000000)) (hi := (81951431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24079 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24079 / 12500) = 1/(12500 / 24079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (655611447 / 1000000000) (81951431 / 125000000) (Real.log (24079 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24079 / 12500) = -Real.log (12500 / 24079) := by
    rw [show ((24079 / 12500) : ℝ) = ((12500 / 24079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (521604777 / 200000000) ≤ -Real.log (921 / 12500) ∧
    -Real.log (921 / 12500) ≤ (2608023889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 4967)) (n := 12)
    (lo := (105716469 / 200000000)) (hi := (264291173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1842) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 1842) = 1/(921 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2608023889 / 1000000000) (-521604777 / 200000000) (Real.log (921 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653930667 / 1000000000) ≤ -Real.log (200000 / 384617) ∧
    -Real.log (200000 / 384617) ≤ (163482667 / 250000000) := by
  have h := checkLog_sound (w := (184617 / 584617)) (n := 12)
    (lo := (653930667 / 1000000000)) (hi := (163482667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384617 / 200000) = 1/(200000 / 384617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653930667 / 1000000000) (163482667 / 250000000) (Real.log (384617 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (384617 / 200000) = -Real.log (200000 / 384617) := by
    rw [show ((384617 / 200000) : ℝ) = ((200000 / 384617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2565054361 / 1000000000) ≤ -Real.log (15383 / 200000) ∧
    -Real.log (15383 / 200000) ≤ (513010873 / 200000000) := by
  have h := checkLog_sound (w := (9617 / 40383)) (n := 12)
    (lo := (485612821 / 1000000000)) (hi := (242806411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15383) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 15383) = 1/(15383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-513010873 / 200000000) (-2565054361 / 1000000000) (Real.log (15383 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (654501981 / 1000000000) ≤ -Real.log (125000 / 240523) ∧
    -Real.log (125000 / 240523) ≤ (327250991 / 500000000) := by
  have h := checkLog_sound (w := (115523 / 365523)) (n := 12)
    (lo := (654501981 / 1000000000)) (hi := (327250991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240523 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240523 / 125000) = 1/(125000 / 240523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (654501981 / 1000000000) (327250991 / 500000000) (Real.log (240523 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (240523 / 125000) = -Real.log (125000 / 240523) := by
    rw [show ((240523 / 125000) : ℝ) = ((125000 / 240523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103177837 / 40000000) ≤ -Real.log (9477 / 125000) ∧
    -Real.log (9477 / 125000) ≤ (2579445929 / 1000000000) := by
  have h := checkLog_sound (w := (3074 / 12551)) (n := 12)
    (lo := (100000877 / 200000000)) (hi := (250002193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9477) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9477) = 1/(9477 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2579445929 / 1000000000) (-103177837 / 40000000) (Real.log (9477 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1624671539 / 500000000) ≤ -Real.log (25000000000 / 644335082529) ∧
    -Real.log (25000000000 / 644335082529) ≤ (3249343083 / 1000000000) := by
  have h := checkLog_sound (w := (244335082529 / 1044335082529)) (n := 12)
    (lo := (238377179 / 500000000)) (hi := (476754359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644335082529 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(644335082529 / 400000000000) = 1/(25000000000 / 644335082529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1624671539 / 500000000) (3249343083 / 1000000000) (Real.log (644335082529 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (644335082529 / 25000000000) = -Real.log (25000000000 / 644335082529) := by
    rw [show ((644335082529 / 25000000000) : ℝ) = ((25000000000 / 644335082529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3263635331 / 1000000000) ≤ -Real.log (500000000000 / 13072204125951) ∧
    -Real.log (500000000000 / 13072204125951) ≤ (407954417 / 125000000) := by
  have h := checkLog_sound (w := (5072204125951 / 21072204125951)) (n := 12)
    (lo := (491046611 / 1000000000)) (hi := (122761653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13072204125951 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13072204125951 / 8000000000000) = 1/(500000000000 / 13072204125951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3263635331 / 1000000000) (407954417 / 125000000) (Real.log (13072204125951 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13072204125951 / 500000000000) = -Real.log (500000000000 / 13072204125951) := by
    rw [show ((13072204125951 / 500000000000) : ℝ) = ((500000000000 / 13072204125951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (804746257 / 250000000) ≤ -Real.log (25000000000 / 625068257167) ∧
    -Real.log (25000000000 / 625068257167) ≤ (3218985033 / 1000000000) := by
  have h := checkLog_sound (w := (225068257167 / 1025068257167)) (n := 12)
    (lo := (111599077 / 250000000)) (hi := (446396309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625068257167 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625068257167 / 400000000000) = 1/(25000000000 / 625068257167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (804746257 / 250000000) (3218985033 / 1000000000) (Real.log (625068257167 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (625068257167 / 25000000000) = -Real.log (25000000000 / 625068257167) := by
    rw [show ((625068257167 / 25000000000) : ℝ) = ((25000000000 / 625068257167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1616973953 / 500000000) ≤ -Real.log (500000000000 / 12689828004643) ∧
    -Real.log (500000000000 / 12689828004643) ≤ (3233947911 / 1000000000) := by
  have h := checkLog_sound (w := (4689828004643 / 20689828004643)) (n := 12)
    (lo := (230679593 / 500000000)) (hi := (461359187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12689828004643 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12689828004643 / 8000000000000) = 1/(500000000000 / 12689828004643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1616973953 / 500000000) (3233947911 / 1000000000) (Real.log (12689828004643 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12689828004643 / 500000000000) = -Real.log (500000000000 / 12689828004643) := by
    rw [show ((12689828004643 / 500000000000) : ℝ) = ((500000000000 / 12689828004643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0162
