import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0082
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

theorem reflection_log_1_neg : (348398601 / 1000000000) ≤ -Real.log (2560 / 3627) ∧
    -Real.log (2560 / 3627) ≤ (174199301 / 500000000) := by
  have h := checkLog_sound (w := (1067 / 6187)) (n := 12)
    (lo := (348398601 / 1000000000)) (hi := (174199301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3627 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3627 / 2560) = 1/(2560 / 3627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (348398601 / 1000000000) (174199301 / 500000000) (Real.log (3627 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3627 / 2560) = -Real.log (2560 / 3627) := by
    rw [show ((3627 / 2560) : ℝ) = ((2560 / 3627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (539219739 / 1000000000) ≤ -Real.log (1493 / 2560) ∧
    -Real.log (1493 / 2560) ≤ (26960987 / 50000000) := by
  have h := checkLog_sound (w := (1067 / 4053)) (n := 12)
    (lo := (539219739 / 1000000000)) (hi := (26960987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1493) = 1/(1493 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-26960987 / 50000000) (-539219739 / 1000000000) (Real.log (1493 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (347571129 / 1000000000) ≤ -Real.log (320 / 453) ∧
    -Real.log (320 / 453) ≤ (34757113 / 100000000) := by
  have h := checkLog_sound (w := (133 / 773)) (n := 12)
    (lo := (347571129 / 1000000000)) (hi := (34757113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453 / 320) = 1/(320 / 453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (347571129 / 1000000000) (34757113 / 100000000) (Real.log (453 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (453 / 320) = -Real.log (320 / 453) := by
    rw [show ((453 / 320) : ℝ) = ((320 / 453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (268606189 / 500000000) ≤ -Real.log (187 / 320) ∧
    -Real.log (187 / 320) ≤ (537212379 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 507)) (n := 12)
    (lo := (268606189 / 500000000)) (hi := (537212379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 187) = 1/(187 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-537212379 / 1000000000) (-268606189 / 500000000) (Real.log (187 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (303138919 / 500000000) ≤ -Real.log (1280 / 2347) ∧
    -Real.log (1280 / 2347) ≤ (606277839 / 1000000000) := by
  have h := checkLog_sound (w := (1067 / 3627)) (n := 12)
    (lo := (303138919 / 500000000)) (hi := (606277839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2347 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2347 / 1280) = 1/(1280 / 2347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (303138919 / 500000000) (606277839 / 1000000000) (Real.log (2347 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2347 / 1280) = -Real.log (1280 / 2347) := by
    rw [show ((2347 / 1280) : ℝ) = ((1280 / 2347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (179332319 / 100000000) ≤ -Real.log (213 / 1280) ∧
    -Real.log (213 / 1280) ≤ (1793323193 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 213) = 1/(213 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1793323193 / 1000000000) (-179332319 / 100000000) (Real.log (213 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (604998793 / 1000000000) ≤ -Real.log (160 / 293) ∧
    -Real.log (160 / 293) ≤ (302499397 / 500000000) := by
  have h := checkLog_sound (w := (133 / 453)) (n := 12)
    (lo := (604998793 / 1000000000)) (hi := (302499397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 160) = 1/(160 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (604998793 / 1000000000) (302499397 / 500000000) (Real.log (293 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (293 / 160) = -Real.log (160 / 293) := by
    rw [show ((293 / 160) : ℝ) = ((160 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (444834237 / 250000000) ≤ -Real.log (27 / 160) ∧
    -Real.log (27 / 160) ≤ (1779336951 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 27) = 1/(27 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1779336951 / 1000000000) (-444834237 / 250000000) (Real.log (27 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (478114397 / 1000000000) ≤ -Real.log (100000 / 161303) ∧
    -Real.log (100000 / 161303) ≤ (239057199 / 500000000) := by
  have h := checkLog_sound (w := (61303 / 261303)) (n := 12)
    (lo := (478114397 / 1000000000)) (hi := (239057199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161303 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161303 / 100000) = 1/(100000 / 161303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (478114397 / 1000000000) (239057199 / 500000000) (Real.log (161303 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (161303 / 100000) = -Real.log (100000 / 161303) := by
    rw [show ((161303 / 100000) : ℝ) = ((100000 / 161303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (949408107 / 1000000000) ≤ -Real.log (38697 / 100000) ∧
    -Real.log (38697 / 100000) ≤ (949408109 / 1000000000) := by
  have h := checkLog_sound (w := (11303 / 88697)) (n := 12)
    (lo := (256260927 / 1000000000)) (hi := (4004077 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38697) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38697) = 1/(38697 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-949408109 / 1000000000) (-949408107 / 1000000000) (Real.log (38697 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119832191 / 250000000) ≤ -Real.log (100000 / 161499) ∧
    -Real.log (100000 / 161499) ≤ (95865753 / 200000000) := by
  have h := checkLog_sound (w := (61499 / 261499)) (n := 12)
    (lo := (119832191 / 250000000)) (hi := (95865753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161499 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161499 / 100000) = 1/(100000 / 161499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119832191 / 250000000) (95865753 / 200000000) (Real.log (161499 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161499 / 100000) = -Real.log (100000 / 161499) := by
    rw [show ((161499 / 100000) : ℝ) = ((100000 / 161499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95448597 / 100000000) ≤ -Real.log (38501 / 100000) ∧
    -Real.log (38501 / 100000) ≤ (238621493 / 250000000) := by
  have h := checkLog_sound (w := (11499 / 88501)) (n := 12)
    (lo := (26133879 / 100000000)) (hi := (261338791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38501) = 1/(38501 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-238621493 / 250000000) (-95448597 / 100000000) (Real.log (38501 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (98577109 / 250000000) ≤ -Real.log (500000 / 741679) ∧
    -Real.log (500000 / 741679) ≤ (394308437 / 1000000000) := by
  have h := checkLog_sound (w := (241679 / 1241679)) (n := 12)
    (lo := (98577109 / 250000000)) (hi := (394308437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741679 / 500000) = 1/(500000 / 741679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (98577109 / 250000000) (394308437 / 1000000000) (Real.log (741679 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (741679 / 500000) = -Real.log (500000 / 741679) := by
    rw [show ((741679 / 500000) : ℝ) = ((500000 / 741679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6604051 / 10000000) ≤ -Real.log (258321 / 500000) ∧
    -Real.log (258321 / 500000) ≤ (660405101 / 1000000000) := by
  have h := checkLog_sound (w := (241679 / 758321)) (n := 12)
    (lo := (6604051 / 10000000)) (hi := (660405101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 258321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 258321) = 1/(258321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-660405101 / 1000000000) (-6604051 / 10000000) (Real.log (258321 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (395587147 / 1000000000) ≤ -Real.log (125000 / 185657) ∧
    -Real.log (125000 / 185657) ≤ (98896787 / 250000000) := by
  have h := checkLog_sound (w := (60657 / 310657)) (n := 12)
    (lo := (395587147 / 1000000000)) (hi := (98896787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185657 / 125000) = 1/(125000 / 185657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (395587147 / 1000000000) (98896787 / 250000000) (Real.log (185657 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (185657 / 125000) = -Real.log (125000 / 185657) := by
    rw [show ((185657 / 125000) : ℝ) = ((125000 / 185657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (664085589 / 1000000000) ≤ -Real.log (64343 / 125000) ∧
    -Real.log (64343 / 125000) ≤ (66408559 / 100000000) := by
  have h := checkLog_sound (w := (60657 / 189343)) (n := 12)
    (lo := (664085589 / 1000000000)) (hi := (66408559 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 64343) = 1/(64343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-66408559 / 100000000) (-664085589 / 1000000000) (Real.log (64343 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (285504501 / 200000000) ≤ -Real.log (500000000000 / 2084179652169) ∧
    -Real.log (500000000000 / 2084179652169) ≤ (356880627 / 250000000) := by
  have h := checkLog_sound (w := (84179652169 / 4084179652169)) (n := 12)
    (lo := (8245629 / 200000000)) (hi := (20614073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2084179652169 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2084179652169 / 2000000000000) = 1/(500000000000 / 2084179652169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (285504501 / 200000000) (356880627 / 250000000) (Real.log (2084179652169 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2084179652169 / 500000000000) = -Real.log (500000000000 / 2084179652169) := by
    rw [show ((2084179652169 / 500000000000) : ℝ) = ((500000000000 / 2084179652169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (716907367 / 500000000) ≤ -Real.log (500000000000 / 2097335134153) ∧
    -Real.log (500000000000 / 2097335134153) ≤ (1433814737 / 1000000000) := by
  have h := checkLog_sound (w := (97335134153 / 4097335134153)) (n := 12)
    (lo := (23760187 / 500000000)) (hi := (380163 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2097335134153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2097335134153 / 2000000000000) = 1/(500000000000 / 2097335134153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (716907367 / 500000000) (1433814737 / 1000000000) (Real.log (2097335134153 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2097335134153 / 500000000000) = -Real.log (500000000000 / 2097335134153) := by
    rw [show ((2097335134153 / 500000000000) : ℝ) = ((500000000000 / 2097335134153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16479899 / 15625000) ≤ -Real.log (4000000000 / 11484610233) ∧
    -Real.log (4000000000 / 11484610233) ≤ (527356769 / 500000000) := by
  have h := checkLog_sound (w := (3484610233 / 19484610233)) (n := 12)
    (lo := (90391589 / 250000000)) (hi := (361566357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11484610233 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11484610233 / 8000000000) = 1/(4000000000 / 11484610233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16479899 / 15625000) (527356769 / 500000000) (Real.log (11484610233 / 4000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11484610233 / 4000000000) = -Real.log (4000000000 / 11484610233) := by
    rw [show ((11484610233 / 4000000000) : ℝ) = ((4000000000 / 11484610233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (33114773 / 31250000) ≤ -Real.log (500000000000 / 1442713271063) ∧
    -Real.log (500000000000 / 1442713271063) ≤ (529836369 / 500000000) := by
  have h := checkLog_sound (w := (442713271063 / 2442713271063)) (n := 12)
    (lo := (91631389 / 250000000)) (hi := (366525557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442713271063 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1442713271063 / 1000000000000) = 1/(500000000000 / 1442713271063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (33114773 / 31250000) (529836369 / 500000000) (Real.log (1442713271063 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1442713271063 / 500000000000) = -Real.log (500000000000 / 1442713271063) := by
    rw [show ((1442713271063 / 500000000000) : ℝ) = ((500000000000 / 1442713271063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0082
