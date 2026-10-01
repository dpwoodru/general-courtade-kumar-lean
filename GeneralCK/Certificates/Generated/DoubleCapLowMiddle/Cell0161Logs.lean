import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0161
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

theorem reflection_log_1_neg : (644892029 / 1000000000) ≤ -Real.log (6400 / 12197) ∧
    -Real.log (6400 / 12197) ≤ (64489203 / 100000000) := by
  have h := checkLog_sound (w := (5797 / 18597)) (n := 12)
    (lo := (644892029 / 1000000000)) (hi := (64489203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12197 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12197 / 6400) = 1/(6400 / 12197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (644892029 / 1000000000) (64489203 / 100000000) (Real.log (12197 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12197 / 6400) = -Real.log (6400 / 12197) := by
    rw [show ((12197 / 6400) : ℝ) = ((6400 / 12197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (236213607 / 100000000) ≤ -Real.log (603 / 6400) ∧
    -Real.log (603 / 6400) ≤ (1181068037 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 603) = 1/(603 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1181068037 / 500000000) (-236213607 / 100000000) (Real.log (603 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128822569 / 200000000) ≤ -Real.log (512 / 975) ∧
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


theorem reflection_log_3 : Bounds (128822569 / 200000000) (322056423 / 500000000) (Real.log (975 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (975 / 512) = -Real.log (512 / 975) := by
    rw [show ((975 / 512) : ℝ) = ((512 / 975) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (93860173 / 40000000) ≤ -Real.log (49 / 512) ∧
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


theorem reflection_log_4 : Bounds (-2346504329 / 1000000000) (-93860173 / 40000000) (Real.log (49 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (148547433 / 250000000) ≤ -Real.log (3200 / 5797) ∧
    -Real.log (3200 / 5797) ≤ (594189733 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 8997)) (n := 12)
    (lo := (148547433 / 250000000)) (hi := (594189733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 3200) = 1/(3200 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (148547433 / 250000000) (594189733 / 1000000000) (Real.log (5797 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5797 / 3200) = -Real.log (3200 / 5797) := by
    rw [show ((5797 / 3200) : ℝ) = ((3200 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166898889 / 100000000) ≤ -Real.log (603 / 3200) ∧
    -Real.log (603 / 3200) ≤ (1668988893 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 603) = 1/(603 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1668988893 / 1000000000) (-166898889 / 100000000) (Real.log (603 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (592549609 / 1000000000) ≤ -Real.log (256 / 463) ∧
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


theorem reflection_log_7 : Bounds (592549609 / 1000000000) (59254961 / 100000000) (Real.log (463 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (463 / 256) = -Real.log (256 / 463) := by
    rw [show ((463 / 256) : ℝ) = ((256 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (330671429 / 200000000) ≤ -Real.log (49 / 256) ∧
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


theorem reflection_log_8 : Bounds (-413339287 / 250000000) (-330671429 / 200000000) (Real.log (49 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (655610927 / 1000000000) ≤ -Real.log (1000000 / 1926319) ∧
    -Real.log (1000000 / 1926319) ≤ (40975683 / 62500000) := by
  have h := checkLog_sound (w := (926319 / 2926319)) (n := 12)
    (lo := (655610927 / 1000000000)) (hi := (40975683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1926319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1926319 / 1000000) = 1/(1000000 / 1926319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (655610927 / 1000000000) (40975683 / 62500000) (Real.log (1926319 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1926319 / 1000000) = -Real.log (1000000 / 1926319) := by
    rw [show ((1926319 / 1000000) : ℝ) = ((1000000 / 1926319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2608010313 / 1000000000) ≤ -Real.log (73681 / 1000000) ∧
    -Real.log (73681 / 1000000) ≤ (2608010317 / 1000000000) := by
  have h := checkLog_sound (w := (51319 / 198681)) (n := 12)
    (lo := (528568773 / 1000000000)) (hi := (264284387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 73681) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 73681) = 1/(73681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2608010317 / 1000000000) (-2608010313 / 1000000000) (Real.log (73681 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65614237 / 100000000) ≤ -Real.log (1000000 / 1927343) ∧
    -Real.log (1000000 / 1927343) ≤ (656142371 / 1000000000) := by
  have h := checkLog_sound (w := (927343 / 2927343)) (n := 12)
    (lo := (65614237 / 100000000)) (hi := (656142371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927343 / 1000000) = 1/(1000000 / 1927343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65614237 / 100000000) (656142371 / 1000000000) (Real.log (1927343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1927343 / 1000000) = -Real.log (1000000 / 1927343) := by
    rw [show ((1927343 / 1000000) : ℝ) = ((1000000 / 1927343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2622005539 / 1000000000) ≤ -Real.log (72657 / 1000000) ∧
    -Real.log (72657 / 1000000) ≤ (2622005543 / 1000000000) := by
  have h := checkLog_sound (w := (52343 / 197657)) (n := 12)
    (lo := (542563999 / 1000000000)) (hi := (135641 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72657) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 72657) = 1/(72657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2622005543 / 1000000000) (-2622005539 / 1000000000) (Real.log (72657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (327250731 / 500000000) ≤ -Real.log (1000000 / 1924183) ∧
    -Real.log (1000000 / 1924183) ≤ (654501463 / 1000000000) := by
  have h := checkLog_sound (w := (924183 / 2924183)) (n := 12)
    (lo := (327250731 / 500000000)) (hi := (654501463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1924183 / 1000000) = 1/(1000000 / 1924183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (327250731 / 500000000) (654501463 / 1000000000) (Real.log (1924183 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1924183 / 1000000) = -Real.log (1000000 / 1924183) := by
    rw [show ((1924183 / 1000000) : ℝ) = ((1000000 / 1924183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (515886547 / 200000000) ≤ -Real.log (75817 / 1000000) ∧
    -Real.log (75817 / 1000000) ≤ (2579432739 / 1000000000) := by
  have h := checkLog_sound (w := (49183 / 200817)) (n := 12)
    (lo := (99998239 / 200000000)) (hi := (124997799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75817) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 75817) = 1/(75817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2579432739 / 1000000000) (-515886547 / 200000000) (Real.log (75817 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (655073489 / 1000000000) ≤ -Real.log (250000 / 481321) ∧
    -Real.log (250000 / 481321) ≤ (65507349 / 100000000) := by
  have h := checkLog_sound (w := (231321 / 731321)) (n := 12)
    (lo := (655073489 / 1000000000)) (hi := (65507349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481321 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481321 / 250000) = 1/(250000 / 481321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (655073489 / 1000000000) (65507349 / 100000000) (Real.log (481321 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (481321 / 250000) = -Real.log (250000 / 481321) := by
    rw [show ((481321 / 250000) : ℝ) = ((250000 / 481321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1297030509 / 500000000) ≤ -Real.log (18679 / 250000) ∧
    -Real.log (18679 / 250000) ≤ (1297030511 / 500000000) := by
  have h := checkLog_sound (w := (12571 / 49929)) (n := 12)
    (lo := (257309739 / 500000000)) (hi := (514619479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 18679) = 1/(18679 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1297030511 / 500000000) (-1297030509 / 500000000) (Real.log (18679 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (81590531 / 25000000) ≤ -Real.log (20000000000 / 522880796949) ∧
    -Real.log (20000000000 / 522880796949) ≤ (652724249 / 200000000) := by
  have h := checkLog_sound (w := (202880796949 / 842880796949)) (n := 12)
    (lo := (12275813 / 25000000)) (hi := (491032521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((522880796949 / 320000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(522880796949 / 320000000000) = 1/(20000000000 / 522880796949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81590531 / 25000000) (652724249 / 200000000) (Real.log (522880796949 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (522880796949 / 20000000000) = -Real.log (20000000000 / 522880796949) := by
    rw [show ((522880796949 / 20000000000) : ℝ) = ((20000000000 / 522880796949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3278147909 / 1000000000) ≤ -Real.log (250000000000 / 6631649393727) ∧
    -Real.log (250000000000 / 6631649393727) ≤ (1639073957 / 500000000) := by
  have h := checkLog_sound (w := (2631649393727 / 10631649393727)) (n := 12)
    (lo := (505559189 / 1000000000)) (hi := (50555919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631649393727 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6631649393727 / 4000000000000) = 1/(250000000000 / 6631649393727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3278147909 / 1000000000) (1639073957 / 500000000) (Real.log (6631649393727 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (6631649393727 / 250000000000) = -Real.log (250000000000 / 6631649393727) := by
    rw [show ((6631649393727 / 250000000000) : ℝ) = ((250000000000 / 6631649393727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (808483549 / 250000000) ≤ -Real.log (250000000000 / 6344827017687) ∧
    -Real.log (250000000000 / 6344827017687) ≤ (3233934201 / 1000000000) := by
  have h := checkLog_sound (w := (2344827017687 / 10344827017687)) (n := 12)
    (lo := (115336369 / 250000000)) (hi := (461345477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6344827017687 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6344827017687 / 4000000000000) = 1/(250000000000 / 6344827017687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (808483549 / 250000000) (3233934201 / 1000000000) (Real.log (6344827017687 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6344827017687 / 250000000000) = -Real.log (250000000000 / 6344827017687) := by
    rw [show ((6344827017687 / 250000000000) : ℝ) = ((250000000000 / 6344827017687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1624567253 / 500000000) ≤ -Real.log (500000000000 / 12884014133519) ∧
    -Real.log (500000000000 / 12884014133519) ≤ (3249134511 / 1000000000) := by
  have h := checkLog_sound (w := (4884014133519 / 20884014133519)) (n := 12)
    (lo := (238272893 / 500000000)) (hi := (476545787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12884014133519 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12884014133519 / 8000000000000) = 1/(500000000000 / 12884014133519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1624567253 / 500000000) (3249134511 / 1000000000) (Real.log (12884014133519 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12884014133519 / 500000000000) = -Real.log (500000000000 / 12884014133519) := by
    rw [show ((12884014133519 / 500000000000) : ℝ) = ((500000000000 / 12884014133519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0161
