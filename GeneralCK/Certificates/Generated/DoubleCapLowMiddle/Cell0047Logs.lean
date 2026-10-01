import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047
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

theorem reflection_log_1_neg : (33967069 / 50000000) ≤ -Real.log (12800 / 25249) ∧
    -Real.log (12800 / 25249) ≤ (679341381 / 1000000000) := by
  have h := checkLog_sound (w := (12449 / 38049)) (n := 12)
    (lo := (33967069 / 50000000)) (hi := (679341381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25249 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25249 / 12800) = 1/(12800 / 25249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33967069 / 50000000) (679341381 / 1000000000) (Real.log (25249 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25249 / 12800) = -Real.log (12800 / 25249) := by
    rw [show ((25249 / 12800) : ℝ) = ((12800 / 25249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3596414223 / 1000000000) ≤ -Real.log (351 / 12800) ∧
    -Real.log (351 / 12800) ≤ (3596414229 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 351) = 1/(351 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3596414229 / 1000000000) (-3596414223 / 1000000000) (Real.log (351 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42452957 / 62500000) ≤ -Real.log (102400 / 201973) ∧
    -Real.log (102400 / 201973) ≤ (679247313 / 1000000000) := by
  have h := checkLog_sound (w := (99573 / 304373)) (n := 12)
    (lo := (42452957 / 62500000)) (hi := (679247313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201973 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201973 / 102400) = 1/(102400 / 201973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42452957 / 62500000) (679247313 / 1000000000) (Real.log (201973 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201973 / 102400) = -Real.log (102400 / 201973) := by
    rw [show ((201973 / 102400) : ℝ) = ((102400 / 201973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3589670631 / 1000000000) ≤ -Real.log (2827 / 102400) ∧
    -Real.log (2827 / 102400) ≤ (3589670637 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2827) = 1/(2827 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3589670637 / 1000000000) (-3589670631 / 1000000000) (Real.log (2827 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166335577 / 250000000) ≤ -Real.log (6400 / 12449) ∧
    -Real.log (6400 / 12449) ≤ (665342309 / 1000000000) := by
  have h := checkLog_sound (w := (6049 / 18849)) (n := 12)
    (lo := (166335577 / 250000000)) (hi := (665342309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12449 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12449 / 6400) = 1/(6400 / 12449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166335577 / 250000000) (665342309 / 1000000000) (Real.log (12449 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12449 / 6400) = -Real.log (6400 / 12449) := by
    rw [show ((12449 / 6400) : ℝ) = ((6400 / 12449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2903267043 / 1000000000) ≤ -Real.log (351 / 6400) ∧
    -Real.log (351 / 6400) ≤ (362908381 / 125000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 351) = 1/(351 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-362908381 / 125000000) (-2903267043 / 1000000000) (Real.log (351 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (665151511 / 1000000000) ≤ -Real.log (51200 / 99573) ∧
    -Real.log (51200 / 99573) ≤ (83143939 / 125000000) := by
  have h := checkLog_sound (w := (48373 / 150773)) (n := 12)
    (lo := (665151511 / 1000000000)) (hi := (83143939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99573 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99573 / 51200) = 1/(51200 / 99573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (665151511 / 1000000000) (83143939 / 125000000) (Real.log (99573 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99573 / 51200) = -Real.log (51200 / 99573) := by
    rw [show ((99573 / 51200) : ℝ) = ((51200 / 99573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2896523451 / 1000000000) ≤ -Real.log (2827 / 51200) ∧
    -Real.log (2827 / 51200) ≤ (45258179 / 15625000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2827) = 1/(2827 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-45258179 / 15625000) (-2896523451 / 1000000000) (Real.log (2827 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681494551 / 1000000000) ≤ -Real.log (100000 / 197683) ∧
    -Real.log (100000 / 197683) ≤ (85186819 / 125000000) := by
  have h := checkLog_sound (w := (97683 / 297683)) (n := 12)
    (lo := (681494551 / 1000000000)) (hi := (85186819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197683 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197683 / 100000) = 1/(100000 / 197683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681494551 / 1000000000) (85186819 / 125000000) (Real.log (197683 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197683 / 100000) = -Real.log (100000 / 197683) := by
    rw [show ((197683 / 100000) : ℝ) = ((100000 / 197683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3764896937 / 1000000000) ≤ -Real.log (2317 / 100000) ∧
    -Real.log (2317 / 100000) ≤ (3764896943 / 1000000000) := by
  have h := checkLog_sound (w := (404 / 2721)) (n := 12)
    (lo := (299161037 / 1000000000)) (hi := (149580519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2317) = 1/(2317 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3764896943 / 1000000000) (-3764896937 / 1000000000) (Real.log (2317 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681570427 / 1000000000) ≤ -Real.log (50000 / 98849) ∧
    -Real.log (50000 / 98849) ≤ (170392607 / 250000000) := by
  have h := checkLog_sound (w := (48849 / 148849)) (n := 12)
    (lo := (681570427 / 1000000000)) (hi := (170392607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98849 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98849 / 50000) = 1/(50000 / 98849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681570427 / 1000000000) (170392607 / 250000000) (Real.log (98849 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98849 / 50000) = -Real.log (50000 / 98849) := by
    rw [show ((98849 / 50000) : ℝ) = ((50000 / 98849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (29463999 / 7812500) ≤ -Real.log (1151 / 50000) ∧
    -Real.log (1151 / 50000) ≤ (1885695939 / 500000000) := by
  have h := checkLog_sound (w := (823 / 5427)) (n := 12)
    (lo := (76413993 / 250000000)) (hi := (305655973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2302) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2302) = 1/(1151 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1885695939 / 500000000) (-29463999 / 7812500) (Real.log (1151 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681430811 / 1000000000) ≤ -Real.log (15625 / 30886) ∧
    -Real.log (15625 / 30886) ≤ (170357703 / 250000000) := by
  have h := checkLog_sound (w := (15261 / 46511)) (n := 12)
    (lo := (681430811 / 1000000000)) (hi := (170357703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30886 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30886 / 15625) = 1/(15625 / 30886) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681430811 / 1000000000) (170357703 / 250000000) (Real.log (30886 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30886 / 15625) = -Real.log (15625 / 30886) := by
    rw [show ((30886 / 15625) : ℝ) = ((15625 / 30886) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (939868401 / 250000000) ≤ -Real.log (364 / 15625) ∧
    -Real.log (364 / 15625) ≤ (375947361 / 100000000) := by
  have h := checkLog_sound (w := (3977 / 27273)) (n := 12)
    (lo := (36717213 / 125000000)) (hi := (58747541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11648) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11648) = 1/(364 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-375947361 / 100000000) (-939868401 / 250000000) (Real.log (364 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681507703 / 1000000000) ≤ -Real.log (125000 / 247107) ∧
    -Real.log (125000 / 247107) ≤ (85188463 / 125000000) := by
  have h := checkLog_sound (w := (122107 / 372107)) (n := 12)
    (lo := (681507703 / 1000000000)) (hi := (85188463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247107 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247107 / 125000) = 1/(125000 / 247107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681507703 / 1000000000) (85188463 / 125000000) (Real.log (247107 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247107 / 125000) = -Real.log (125000 / 247107) := by
    rw [show ((247107 / 125000) : ℝ) = ((125000 / 247107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (941504927 / 250000000) ≤ -Real.log (2893 / 125000) ∧
    -Real.log (2893 / 125000) ≤ (1883009857 / 500000000) := by
  have h := checkLog_sound (w := (4053 / 27197)) (n := 12)
    (lo := (9383869 / 31250000)) (hi := (300283809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11572) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11572) = 1/(2893 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1883009857 / 500000000) (-941504927 / 250000000) (Real.log (2893 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (69474867 / 15625000) ≤ -Real.log (15625000000 / 1333101801899) ∧
    -Real.log (15625000000 / 1333101801899) ≤ (889278299 / 200000000) := by
  have h := checkLog_sound (w := (333101801899 / 2333101801899)) (n := 12)
    (lo := (35938551 / 125000000)) (hi := (287508409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333101801899 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1333101801899 / 1000000000000) = 1/(15625000000 / 1333101801899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (69474867 / 15625000) (889278299 / 200000000) (Real.log (1333101801899 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1333101801899 / 15625000000) = -Real.log (15625000000 / 1333101801899) := by
    rw [show ((1333101801899 / 15625000000) : ℝ) = ((15625000000 / 1333101801899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (44529623 / 10000000) ≤ -Real.log (10000000000 / 858809730669) ∧
    -Real.log (10000000000 / 858809730669) ≤ (4452962307 / 1000000000) := by
  have h := checkLog_sound (w := (218809730669 / 1498809730669)) (n := 12)
    (lo := (14703961 / 50000000)) (hi := (294079221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858809730669 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(858809730669 / 640000000000) = 1/(10000000000 / 858809730669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (44529623 / 10000000) (4452962307 / 1000000000) (Real.log (858809730669 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (858809730669 / 10000000000) = -Real.log (10000000000 / 858809730669) := by
    rw [show ((858809730669 / 10000000000) : ℝ) = ((10000000000 / 858809730669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2220452207 / 500000000) ≤ -Real.log (31250000000 / 2651614010989) ∧
    -Real.log (31250000000 / 2651614010989) ≤ (4440904421 / 1000000000) := by
  have h := checkLog_sound (w := (651614010989 / 4651614010989)) (n := 12)
    (lo := (141010667 / 500000000)) (hi := (56404267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2651614010989 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2651614010989 / 2000000000000) = 1/(31250000000 / 2651614010989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2220452207 / 500000000) (4440904421 / 1000000000) (Real.log (2651614010989 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2651614010989 / 31250000000) = -Real.log (31250000000 / 2651614010989) := by
    rw [show ((2651614010989 / 31250000000) : ℝ) = ((31250000000 / 2651614010989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4447527411 / 1000000000) ≤ -Real.log (100000000000 / 8541548565503) ∧
    -Real.log (100000000000 / 8541548565503) ≤ (2223763709 / 500000000) := by
  have h := checkLog_sound (w := (2141548565503 / 14941548565503)) (n := 12)
    (lo := (288644331 / 1000000000)) (hi := (72161083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8541548565503 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8541548565503 / 6400000000000) = 1/(100000000000 / 8541548565503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4447527411 / 1000000000) (2223763709 / 500000000) (Real.log (8541548565503 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8541548565503 / 100000000000) = -Real.log (100000000000 / 8541548565503) := by
    rw [show ((8541548565503 / 100000000000) : ℝ) = ((100000000000 / 8541548565503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047
