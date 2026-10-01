import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0239
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

theorem reflection_log_1_neg : (247988591 / 1000000000) ≤ -Real.log (5120 / 6561) ∧
    -Real.log (5120 / 6561) ≤ (15499287 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 11681)) (n := 12)
    (lo := (247988591 / 1000000000)) (hi := (15499287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6561 / 5120) = 1/(5120 / 6561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247988591 / 1000000000) (15499287 / 62500000) (Real.log (6561 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6561 / 5120) = -Real.log (5120 / 6561) := by
    rw [show ((6561 / 5120) : ℝ) = ((5120 / 6561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165256731 / 500000000) ≤ -Real.log (3679 / 5120) ∧
    -Real.log (3679 / 5120) ≤ (330513463 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 8799)) (n := 12)
    (lo := (165256731 / 500000000)) (hi := (330513463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3679) = 1/(3679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-330513463 / 1000000000) (-165256731 / 500000000) (Real.log (3679 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247531239 / 1000000000) ≤ -Real.log (2560 / 3279) ∧
    -Real.log (2560 / 3279) ≤ (6188281 / 25000000) := by
  have h := checkLog_sound (w := (719 / 5839)) (n := 12)
    (lo := (247531239 / 1000000000)) (hi := (6188281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3279 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3279 / 2560) = 1/(2560 / 3279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247531239 / 1000000000) (6188281 / 25000000) (Real.log (3279 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3279 / 2560) = -Real.log (2560 / 3279) := by
    rw [show ((3279 / 2560) : ℝ) = ((2560 / 3279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82424589 / 250000000) ≤ -Real.log (1841 / 2560) ∧
    -Real.log (1841 / 2560) ≤ (329698357 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 4401)) (n := 12)
    (lo := (82424589 / 250000000)) (hi := (329698357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1841) = 1/(1841 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-329698357 / 1000000000) (-82424589 / 250000000) (Real.log (1841 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (446537071 / 1000000000) ≤ -Real.log (2560 / 4001) ∧
    -Real.log (2560 / 4001) ≤ (27908567 / 62500000) := by
  have h := checkLog_sound (w := (1441 / 6561)) (n := 12)
    (lo := (446537071 / 1000000000)) (hi := (27908567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4001 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4001 / 2560) = 1/(2560 / 4001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (446537071 / 1000000000) (27908567 / 62500000) (Real.log (4001 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4001 / 2560) = -Real.log (2560 / 4001) := by
    rw [show ((4001 / 2560) : ℝ) = ((2560 / 4001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (206892957 / 250000000) ≤ -Real.log (1119 / 2560) ∧
    -Real.log (1119 / 2560) ≤ (82757183 / 100000000) := by
  have h := checkLog_sound (w := (161 / 2399)) (n := 12)
    (lo := (16803081 / 125000000)) (hi := (134424649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1119) = 1/(1119 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-82757183 / 100000000) (-206892957 / 250000000) (Real.log (1119 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (445786977 / 1000000000) ≤ -Real.log (1280 / 1999) ∧
    -Real.log (1280 / 1999) ≤ (222893489 / 500000000) := by
  have h := checkLog_sound (w := (719 / 3279)) (n := 12)
    (lo := (445786977 / 1000000000)) (hi := (222893489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1999 / 1280) = 1/(1280 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (445786977 / 1000000000) (222893489 / 500000000) (Real.log (1999 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1999 / 1280) = -Real.log (1280 / 1999) := by
    rw [show ((1999 / 1280) : ℝ) = ((1280 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (16497889 / 20000000) ≤ -Real.log (561 / 1280) ∧
    -Real.log (561 / 1280) ≤ (206223613 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1201)) (n := 12)
    (lo := (13174727 / 100000000)) (hi := (131747271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 561) = 1/(561 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-206223613 / 250000000) (-16497889 / 20000000) (Real.log (561 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (84697031 / 250000000) ≤ -Real.log (500000 / 701623) ∧
    -Real.log (500000 / 701623) ≤ (542061 / 1600000) := by
  have h := checkLog_sound (w := (201623 / 1201623)) (n := 12)
    (lo := (84697031 / 250000000)) (hi := (542061 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701623 / 500000) = 1/(500000 / 701623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (84697031 / 250000000) (542061 / 1600000) (Real.log (701623 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (701623 / 500000) = -Real.log (500000 / 701623) := by
    rw [show ((701623 / 500000) : ℝ) = ((500000 / 701623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51625031 / 100000000) ≤ -Real.log (298377 / 500000) ∧
    -Real.log (298377 / 500000) ≤ (516250311 / 1000000000) := by
  have h := checkLog_sound (w := (201623 / 798377)) (n := 12)
    (lo := (51625031 / 100000000)) (hi := (516250311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 298377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 298377) = 1/(298377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-516250311 / 1000000000) (-51625031 / 100000000) (Real.log (298377 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339409347 / 1000000000) ≤ -Real.log (500000 / 702059) ∧
    -Real.log (500000 / 702059) ≤ (84852337 / 250000000) := by
  have h := checkLog_sound (w := (202059 / 1202059)) (n := 12)
    (lo := (339409347 / 1000000000)) (hi := (84852337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702059 / 500000) = 1/(500000 / 702059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339409347 / 1000000000) (84852337 / 250000000) (Real.log (702059 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (702059 / 500000) = -Real.log (500000 / 702059) := by
    rw [show ((702059 / 500000) : ℝ) = ((500000 / 702059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (258856309 / 500000000) ≤ -Real.log (297941 / 500000) ∧
    -Real.log (297941 / 500000) ≤ (517712619 / 1000000000) := by
  have h := checkLog_sound (w := (202059 / 797941)) (n := 12)
    (lo := (258856309 / 500000000)) (hi := (517712619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 297941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 297941) = 1/(297941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-517712619 / 1000000000) (-258856309 / 500000000) (Real.log (297941 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (130627209 / 500000000) ≤ -Real.log (500000 / 649279) ∧
    -Real.log (500000 / 649279) ≤ (261254419 / 1000000000) := by
  have h := checkLog_sound (w := (149279 / 1149279)) (n := 12)
    (lo := (130627209 / 500000000)) (hi := (261254419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649279 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649279 / 500000) = 1/(500000 / 649279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (130627209 / 500000000) (261254419 / 1000000000) (Real.log (649279 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (649279 / 500000) = -Real.log (500000 / 649279) := by
    rw [show ((649279 / 500000) : ℝ) = ((500000 / 649279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (177308531 / 500000000) ≤ -Real.log (350721 / 500000) ∧
    -Real.log (350721 / 500000) ≤ (354617063 / 1000000000) := by
  have h := checkLog_sound (w := (149279 / 850721)) (n := 12)
    (lo := (177308531 / 500000000)) (hi := (354617063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350721) = 1/(350721 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-354617063 / 1000000000) (-177308531 / 500000000) (Real.log (350721 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (261798719 / 1000000000) ≤ -Real.log (200000 / 259853) ∧
    -Real.log (200000 / 259853) ≤ (818121 / 3125000) := by
  have h := checkLog_sound (w := (59853 / 459853)) (n := 12)
    (lo := (261798719 / 1000000000)) (hi := (818121 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259853 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259853 / 200000) = 1/(200000 / 259853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (261798719 / 1000000000) (818121 / 3125000) (Real.log (259853 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (259853 / 200000) = -Real.log (200000 / 259853) := by
    rw [show ((259853 / 200000) : ℝ) = ((200000 / 259853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (177812747 / 500000000) ≤ -Real.log (140147 / 200000) ∧
    -Real.log (140147 / 200000) ≤ (71125099 / 200000000) := by
  have h := checkLog_sound (w := (59853 / 340147)) (n := 12)
    (lo := (177812747 / 500000000)) (hi := (71125099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 140147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 140147) = 1/(140147 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-71125099 / 200000000) (-177812747 / 500000000) (Real.log (140147 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (427519217 / 500000000) ≤ -Real.log (125000000000 / 293933094709) ∧
    -Real.log (125000000000 / 293933094709) ≤ (213759609 / 250000000) := by
  have h := checkLog_sound (w := (43933094709 / 543933094709)) (n := 12)
    (lo := (80945627 / 500000000)) (hi := (32378251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293933094709 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293933094709 / 250000000000) = 1/(125000000000 / 293933094709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (427519217 / 500000000) (213759609 / 250000000) (Real.log (293933094709 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (293933094709 / 125000000000) = -Real.log (125000000000 / 293933094709) := by
    rw [show ((293933094709 / 125000000000) : ℝ) = ((125000000000 / 293933094709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (171424393 / 200000000) ≤ -Real.log (25000000000 / 58909230351) ∧
    -Real.log (25000000000 / 58909230351) ≤ (857121967 / 1000000000) := by
  have h := checkLog_sound (w := (8909230351 / 108909230351)) (n := 12)
    (lo := (32794957 / 200000000)) (hi := (81987393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58909230351 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58909230351 / 50000000000) = 1/(25000000000 / 58909230351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (171424393 / 200000000) (857121967 / 1000000000) (Real.log (58909230351 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (58909230351 / 25000000000) = -Real.log (25000000000 / 58909230351) := by
    rw [show ((58909230351 / 25000000000) : ℝ) = ((25000000000 / 58909230351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15396787 / 25000000) ≤ -Real.log (500000000000 / 925634621251) ∧
    -Real.log (500000000000 / 925634621251) ≤ (615871481 / 1000000000) := by
  have h := checkLog_sound (w := (425634621251 / 1425634621251)) (n := 12)
    (lo := (15396787 / 25000000)) (hi := (615871481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925634621251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925634621251 / 500000000000) = 1/(500000000000 / 925634621251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15396787 / 25000000) (615871481 / 1000000000) (Real.log (925634621251 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (925634621251 / 500000000000) = -Real.log (500000000000 / 925634621251) := by
    rw [show ((925634621251 / 500000000000) : ℝ) = ((500000000000 / 925634621251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (308712107 / 500000000) ≤ -Real.log (1562500000 / 2897103131) ∧
    -Real.log (1562500000 / 2897103131) ≤ (123484843 / 200000000) := by
  have h := checkLog_sound (w := (1334603131 / 4459603131)) (n := 12)
    (lo := (308712107 / 500000000)) (hi := (123484843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2897103131 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2897103131 / 1562500000) = 1/(1562500000 / 2897103131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (308712107 / 500000000) (123484843 / 200000000) (Real.log (2897103131 / 1562500000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2897103131 / 1562500000) = -Real.log (1562500000 / 2897103131) := by
    rw [show ((2897103131 / 1562500000) : ℝ) = ((1562500000 / 2897103131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0239
