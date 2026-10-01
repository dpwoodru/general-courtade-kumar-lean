import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066
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

theorem reflection_log_1_neg : (677552581 / 1000000000) ≤ -Real.log (102400 / 201631) ∧
    -Real.log (102400 / 201631) ≤ (338776291 / 500000000) := by
  have h := checkLog_sound (w := (99231 / 304031)) (n := 12)
    (lo := (677552581 / 1000000000)) (hi := (338776291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201631 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201631 / 102400) = 1/(102400 / 201631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (677552581 / 1000000000) (338776291 / 500000000) (Real.log (201631 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201631 / 102400) = -Real.log (102400 / 201631) := by
    rw [show ((201631 / 102400) : ℝ) = ((102400 / 201631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3475470629 / 1000000000) ≤ -Real.log (3169 / 102400) ∧
    -Real.log (3169 / 102400) ≤ (695094127 / 200000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3169) = 1/(3169 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) (Real.log (3169 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135491669 / 200000000) ≤ -Real.log (25600 / 50403) ∧
    -Real.log (25600 / 50403) ≤ (338729173 / 500000000) := by
  have h := checkLog_sound (w := (24803 / 76003)) (n := 12)
    (lo := (135491669 / 200000000)) (hi := (338729173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50403 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50403 / 25600) = 1/(25600 / 50403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (135491669 / 200000000) (338729173 / 500000000) (Real.log (50403 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50403 / 25600) = -Real.log (25600 / 50403) := by
    rw [show ((50403 / 25600) : ℝ) = ((25600 / 50403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (867373237 / 250000000) ≤ -Real.log (797 / 25600) ∧
    -Real.log (797 / 25600) ≤ (1734746477 / 500000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 797) = 1/(797 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) (Real.log (797 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661710933 / 1000000000) ≤ -Real.log (51200 / 99231) ∧
    -Real.log (51200 / 99231) ≤ (330855467 / 500000000) := by
  have h := checkLog_sound (w := (48031 / 150431)) (n := 12)
    (lo := (661710933 / 1000000000)) (hi := (330855467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99231 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99231 / 51200) = 1/(51200 / 99231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661710933 / 1000000000) (330855467 / 500000000) (Real.log (99231 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99231 / 51200) = -Real.log (51200 / 99231) := by
    rw [show ((99231 / 51200) : ℝ) = ((51200 / 99231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2782323449 / 1000000000) ≤ -Real.log (3169 / 51200) ∧
    -Real.log (3169 / 51200) ≤ (1391161727 / 500000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3169) = 1/(3169 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) (Real.log (3169 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (330759721 / 500000000) ≤ -Real.log (12800 / 24803) ∧
    -Real.log (12800 / 24803) ≤ (661519443 / 1000000000) := by
  have h := checkLog_sound (w := (12003 / 37603)) (n := 12)
    (lo := (330759721 / 500000000)) (hi := (661519443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24803 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24803 / 12800) = 1/(12800 / 24803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (330759721 / 500000000) (661519443 / 1000000000) (Real.log (24803 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24803 / 12800) = -Real.log (12800 / 24803) := by
    rw [show ((24803 / 12800) : ℝ) = ((12800 / 24803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (347043221 / 125000000) ≤ -Real.log (797 / 12800) ∧
    -Real.log (797 / 12800) ≤ (2776345773 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 797) = 1/(797 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) (Real.log (797 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340035783 / 500000000) ≤ -Real.log (1000000 / 1974019) ∧
    -Real.log (1000000 / 1974019) ≤ (680071567 / 1000000000) := by
  have h := checkLog_sound (w := (974019 / 2974019)) (n := 12)
    (lo := (340035783 / 500000000)) (hi := (680071567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974019 / 1000000) = 1/(1000000 / 1974019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340035783 / 500000000) (680071567 / 1000000000) (Real.log (1974019 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1974019 / 1000000) = -Real.log (1000000 / 1974019) := by
    rw [show ((1974019 / 1000000) : ℝ) = ((1000000 / 1974019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1825194887 / 500000000) ≤ -Real.log (25981 / 1000000) ∧
    -Real.log (25981 / 1000000) ≤ (182519489 / 50000000) := by
  have h := checkLog_sound (w := (5269 / 57231)) (n := 12)
    (lo := (92326937 / 500000000)) (hi := (1477231 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25981) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25981) = 1/(25981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-182519489 / 50000000) (-1825194887 / 500000000) (Real.log (25981 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680146537 / 1000000000) ≤ -Real.log (1000000 / 1974167) ∧
    -Real.log (1000000 / 1974167) ≤ (340073269 / 500000000) := by
  have h := checkLog_sound (w := (974167 / 2974167)) (n := 12)
    (lo := (680146537 / 1000000000)) (hi := (340073269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974167 / 1000000) = 1/(1000000 / 1974167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680146537 / 1000000000) (340073269 / 500000000) (Real.log (1974167 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1974167 / 1000000) = -Real.log (1000000 / 1974167) := by
    rw [show ((1974167 / 1000000) : ℝ) = ((1000000 / 1974167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3656102531 / 1000000000) ≤ -Real.log (25833 / 1000000) ∧
    -Real.log (25833 / 1000000) ≤ (3656102537 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 57083)) (n := 12)
    (lo := (190366631 / 1000000000)) (hi := (23795829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25833) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25833) = 1/(25833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3656102537 / 1000000000) (-3656102531 / 1000000000) (Real.log (25833 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84998497 / 125000000) ≤ -Real.log (500000 / 986927) ∧
    -Real.log (500000 / 986927) ≤ (679987977 / 1000000000) := by
  have h := checkLog_sound (w := (486927 / 1486927)) (n := 12)
    (lo := (84998497 / 125000000)) (hi := (679987977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986927 / 500000) = 1/(500000 / 986927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84998497 / 125000000) (679987977 / 1000000000) (Real.log (986927 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (986927 / 500000) = -Real.log (500000 / 986927) := by
    rw [show ((986927 / 500000) : ℝ) = ((500000 / 986927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3644059061 / 1000000000) ≤ -Real.log (13073 / 500000) ∧
    -Real.log (13073 / 500000) ≤ (3644059067 / 1000000000) := by
  have h := checkLog_sound (w := (1276 / 14349)) (n := 12)
    (lo := (178323161 / 1000000000)) (hi := (89161581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13073) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13073) = 1/(13073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3644059067 / 1000000000) (-3644059061 / 1000000000) (Real.log (13073 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680064473 / 1000000000) ≤ -Real.log (200000 / 394801) ∧
    -Real.log (200000 / 394801) ≤ (340032237 / 500000000) := by
  have h := checkLog_sound (w := (194801 / 594801)) (n := 12)
    (lo := (680064473 / 1000000000)) (hi := (340032237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394801 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394801 / 200000) = 1/(200000 / 394801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680064473 / 1000000000) (340032237 / 500000000) (Real.log (394801 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394801 / 200000) = -Real.log (200000 / 394801) := by
    rw [show ((394801 / 200000) : ℝ) = ((200000 / 394801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (456231383 / 125000000) ≤ -Real.log (5199 / 200000) ∧
    -Real.log (5199 / 200000) ≤ (364985107 / 100000000) := by
  have h := checkLog_sound (w := (1051 / 11449)) (n := 12)
    (lo := (46028791 / 250000000)) (hi := (36823033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5199) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5199) = 1/(5199 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-364985107 / 100000000) (-456231383 / 125000000) (Real.log (5199 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (216523067 / 50000000) ≤ -Real.log (250000000000 / 18994832762403) ∧
    -Real.log (250000000000 / 18994832762403) ≤ (4330461347 / 1000000000) := by
  have h := checkLog_sound (w := (2994832762403 / 34994832762403)) (n := 12)
    (lo := (8578913 / 50000000)) (hi := (171578261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18994832762403 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18994832762403 / 16000000000000) = 1/(250000000000 / 18994832762403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (216523067 / 50000000) (4330461347 / 1000000000) (Real.log (18994832762403 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18994832762403 / 250000000000) = -Real.log (250000000000 / 18994832762403) := by
    rw [show ((18994832762403 / 250000000000) : ℝ) = ((250000000000 / 18994832762403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1084062267 / 250000000) ≤ -Real.log (500000000000 / 38210176905509) ∧
    -Real.log (500000000000 / 38210176905509) ≤ (173449963 / 40000000) := by
  have h := checkLog_sound (w := (6210176905509 / 70210176905509)) (n := 12)
    (lo := (44341497 / 250000000)) (hi := (177365989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38210176905509 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38210176905509 / 32000000000000) = 1/(500000000000 / 38210176905509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1084062267 / 250000000) (173449963 / 40000000) (Real.log (38210176905509 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (38210176905509 / 500000000000) = -Real.log (500000000000 / 38210176905509) := by
    rw [show ((38210176905509 / 500000000000) : ℝ) = ((500000000000 / 38210176905509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4324047037 / 1000000000) ≤ -Real.log (500000000000 / 37746768148091) ∧
    -Real.log (500000000000 / 37746768148091) ≤ (1081011761 / 250000000) := by
  have h := checkLog_sound (w := (5746768148091 / 69746768148091)) (n := 12)
    (lo := (165163957 / 1000000000)) (hi := (82581979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37746768148091 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37746768148091 / 32000000000000) = 1/(500000000000 / 37746768148091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4324047037 / 1000000000) (1081011761 / 250000000) (Real.log (37746768148091 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37746768148091 / 500000000000) = -Real.log (500000000000 / 37746768148091) := by
    rw [show ((37746768148091 / 500000000000) : ℝ) = ((500000000000 / 37746768148091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4329915537 / 1000000000) ≤ -Real.log (500000000000 / 37968936333911) ∧
    -Real.log (500000000000 / 37968936333911) ≤ (541239443 / 125000000) := by
  have h := checkLog_sound (w := (5968936333911 / 69968936333911)) (n := 12)
    (lo := (171032457 / 1000000000)) (hi := (85516229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37968936333911 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37968936333911 / 32000000000000) = 1/(500000000000 / 37968936333911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4329915537 / 1000000000) (541239443 / 125000000) (Real.log (37968936333911 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (37968936333911 / 500000000000) = -Real.log (500000000000 / 37968936333911) := by
    rw [show ((37968936333911 / 500000000000) : ℝ) = ((500000000000 / 37968936333911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066
