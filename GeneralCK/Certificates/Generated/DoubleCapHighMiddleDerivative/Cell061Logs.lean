import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell061
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (1967123 / 7812500) ≤ -Real.log (2560 / 3293) ∧
    -Real.log (2560 / 3293) ≤ (50358349 / 200000000) := by
  have h := checkLog_sound (w := (733 / 5853)) (n := 12)
    (lo := (1967123 / 7812500)) (hi := (50358349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3293 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3293 / 2560) = 1/(2560 / 3293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1967123 / 7812500) (50358349 / 200000000) (Real.log (3293 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3293 / 2560) = -Real.log (2560 / 3293) := by
    rw [show ((3293 / 2560) : ℝ) = ((2560 / 3293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (337331981 / 1000000000) ≤ -Real.log (1827 / 2560) ∧
    -Real.log (1827 / 2560) ≤ (168665991 / 500000000) := by
  have h := checkLog_sound (w := (733 / 4387)) (n := 12)
    (lo := (337331981 / 1000000000)) (hi := (168665991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1827) = 1/(1827 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-168665991 / 500000000) (-337331981 / 1000000000) (Real.log (1827 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (251336129 / 1000000000) ≤ -Real.log (5120 / 6583) ∧
    -Real.log (5120 / 6583) ≤ (25133613 / 100000000) := by
  have h := checkLog_sound (w := (1463 / 11703)) (n := 12)
    (lo := (251336129 / 1000000000)) (hi := (25133613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6583 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6583 / 5120) = 1/(5120 / 6583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (251336129 / 1000000000) (25133613 / 100000000) (Real.log (6583 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6583 / 5120) = -Real.log (5120 / 6583) := by
    rw [show ((6583 / 5120) : ℝ) = ((5120 / 6583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (336511299 / 1000000000) ≤ -Real.log (3657 / 5120) ∧
    -Real.log (3657 / 5120) ≤ (3365113 / 10000000) := by
  have h := checkLog_sound (w := (1463 / 8777)) (n := 12)
    (lo := (336511299 / 1000000000)) (hi := (3365113 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3657) = 1/(3657 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3365113 / 10000000) (-336511299 / 1000000000) (Real.log (3657 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184619747 / 1000000000) ≤ -Real.log (1000000 / 1202761) ∧
    -Real.log (1000000 / 1202761) ≤ (46154937 / 250000000) := by
  have h := checkLog_sound (w := (202761 / 2202761)) (n := 12)
    (lo := (184619747 / 1000000000)) (hi := (46154937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202761 / 1000000) = 1/(1000000 / 1202761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184619747 / 1000000000) (46154937 / 250000000) (Real.log (1202761 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1202761 / 1000000) = -Real.log (1000000 / 1202761) := by
    rw [show ((1202761 / 1000000) : ℝ) = ((1000000 / 1202761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22660077 / 100000000) ≤ -Real.log (797239 / 1000000) ∧
    -Real.log (797239 / 1000000) ≤ (226600771 / 1000000000) := by
  have h := checkLog_sound (w := (202761 / 1797239)) (n := 12)
    (lo := (22660077 / 100000000)) (hi := (226600771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797239) = 1/(797239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-226600771 / 1000000000) (-22660077 / 100000000) (Real.log (797239 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92484441 / 500000000) ≤ -Real.log (1000000 / 1203181) ∧
    -Real.log (1000000 / 1203181) ≤ (184968883 / 1000000000) := by
  have h := checkLog_sound (w := (203181 / 2203181)) (n := 12)
    (lo := (92484441 / 500000000)) (hi := (184968883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203181 / 1000000) = 1/(1000000 / 1203181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92484441 / 500000000) (184968883 / 1000000000) (Real.log (1203181 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1203181 / 1000000) = -Real.log (1000000 / 1203181) := by
    rw [show ((1203181 / 1000000) : ℝ) = ((1000000 / 1203181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (227127727 / 1000000000) ≤ -Real.log (796819 / 1000000) ∧
    -Real.log (796819 / 1000000) ≤ (14195483 / 62500000) := by
  have h := checkLog_sound (w := (203181 / 1796819)) (n := 12)
    (lo := (227127727 / 1000000000)) (hi := (14195483 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796819) = 1/(796819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-14195483 / 62500000) (-227127727 / 1000000000) (Real.log (796819 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8464209 / 62500000) ≤ -Real.log (500000 / 572513) ∧
    -Real.log (500000 / 572513) ≤ (27085469 / 200000000) := by
  have h := checkLog_sound (w := (72513 / 1072513)) (n := 12)
    (lo := (8464209 / 62500000)) (hi := (27085469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572513 / 500000) = 1/(500000 / 572513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8464209 / 62500000) (27085469 / 200000000) (Real.log (572513 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (572513 / 500000) = -Real.log (500000 / 572513) := by
    rw [show ((572513 / 500000) : ℝ) = ((500000 / 572513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (156684219 / 1000000000) ≤ -Real.log (427487 / 500000) ∧
    -Real.log (427487 / 500000) ≤ (7834211 / 50000000) := by
  have h := checkLog_sound (w := (72513 / 927487)) (n := 12)
    (lo := (156684219 / 1000000000)) (hi := (7834211 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427487) = 1/(427487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7834211 / 50000000) (-156684219 / 1000000000) (Real.log (427487 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135696297 / 1000000000) ≤ -Real.log (500000 / 572667) ∧
    -Real.log (500000 / 572667) ≤ (67848149 / 500000000) := by
  have h := checkLog_sound (w := (72667 / 1072667)) (n := 12)
    (lo := (135696297 / 1000000000)) (hi := (67848149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572667 / 500000) = 1/(500000 / 572667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135696297 / 1000000000) (67848149 / 500000000) (Real.log (572667 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (572667 / 500000) = -Real.log (500000 / 572667) := by
    rw [show ((572667 / 500000) : ℝ) = ((500000 / 572667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (157044529 / 1000000000) ≤ -Real.log (427333 / 500000) ∧
    -Real.log (427333 / 500000) ≤ (15704453 / 100000000) := by
  have h := checkLog_sound (w := (72667 / 927333)) (n := 12)
    (lo := (157044529 / 1000000000)) (hi := (15704453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427333) = 1/(427333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15704453 / 100000000) (-157044529 / 1000000000) (Real.log (427333 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (587847429 / 1000000000) ≤ -Real.log (125000000000 / 225013672409) ∧
    -Real.log (125000000000 / 225013672409) ≤ (58784743 / 100000000) := by
  have h := checkLog_sound (w := (100013672409 / 350013672409)) (n := 12)
    (lo := (587847429 / 1000000000)) (hi := (58784743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225013672409 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225013672409 / 125000000000) = 1/(125000000000 / 225013672409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (587847429 / 1000000000) (58784743 / 100000000) (Real.log (225013672409 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (225013672409 / 125000000000) = -Real.log (125000000000 / 225013672409) := by
    rw [show ((225013672409 / 125000000000) : ℝ) = ((125000000000 / 225013672409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23564949 / 40000000) ≤ -Real.log (20000000000 / 36048166393) ∧
    -Real.log (20000000000 / 36048166393) ≤ (294561863 / 500000000) := by
  have h := checkLog_sound (w := (16048166393 / 56048166393)) (n := 12)
    (lo := (23564949 / 40000000)) (hi := (294561863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36048166393 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36048166393 / 20000000000) = 1/(20000000000 / 36048166393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (23564949 / 40000000) (294561863 / 500000000) (Real.log (36048166393 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (36048166393 / 20000000000) = -Real.log (20000000000 / 36048166393) := by
    rw [show ((36048166393 / 20000000000) : ℝ) = ((20000000000 / 36048166393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (411220517 / 1000000000) ≤ -Real.log (500000000000 / 754329002971) ∧
    -Real.log (500000000000 / 754329002971) ≤ (205610259 / 500000000) := by
  have h := checkLog_sound (w := (254329002971 / 1254329002971)) (n := 12)
    (lo := (411220517 / 1000000000)) (hi := (205610259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754329002971 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754329002971 / 500000000000) = 1/(500000000000 / 754329002971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (411220517 / 1000000000) (205610259 / 500000000) (Real.log (754329002971 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754329002971 / 500000000000) = -Real.log (500000000000 / 754329002971) := by
    rw [show ((754329002971 / 500000000000) : ℝ) = ((500000000000 / 754329002971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41209661 / 100000000) ≤ -Real.log (500000000000 / 754990154603) ∧
    -Real.log (500000000000 / 754990154603) ≤ (412096611 / 1000000000) := by
  have h := checkLog_sound (w := (254990154603 / 1254990154603)) (n := 12)
    (lo := (41209661 / 100000000)) (hi := (412096611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754990154603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754990154603 / 500000000000) = 1/(500000000000 / 754990154603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (41209661 / 100000000) (412096611 / 1000000000) (Real.log (754990154603 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (754990154603 / 500000000000) = -Real.log (500000000000 / 754990154603) := by
    rw [show ((754990154603 / 500000000000) : ℝ) = ((500000000000 / 754990154603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (73027891 / 250000000) ≤ -Real.log (100000000000 / 133925242171) ∧
    -Real.log (100000000000 / 133925242171) ≤ (58422313 / 200000000) := by
  have h := checkLog_sound (w := (33925242171 / 233925242171)) (n := 12)
    (lo := (73027891 / 250000000)) (hi := (58422313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133925242171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133925242171 / 100000000000) = 1/(100000000000 / 133925242171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (73027891 / 250000000) (58422313 / 200000000) (Real.log (133925242171 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (133925242171 / 100000000000) = -Real.log (100000000000 / 133925242171) := by
    rw [show ((133925242171 / 100000000000) : ℝ) = ((100000000000 / 133925242171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292740827 / 1000000000) ≤ -Real.log (250000000000 / 335023857273) ∧
    -Real.log (250000000000 / 335023857273) ≤ (73185207 / 250000000) := by
  have h := checkLog_sound (w := (85023857273 / 585023857273)) (n := 12)
    (lo := (292740827 / 1000000000)) (hi := (73185207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335023857273 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335023857273 / 250000000000) = 1/(250000000000 / 335023857273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292740827 / 1000000000) (73185207 / 250000000) (Real.log (335023857273 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335023857273 / 250000000000) = -Real.log (250000000000 / 335023857273) := by
    rw [show ((335023857273 / 250000000000) : ℝ) = ((250000000000 / 335023857273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2668529 / 125000000) ≤ -Real.log (244719507111 / 250000000000) ∧
    -Real.log (244719507111 / 250000000000) ≤ (21348233 / 1000000000) := by
  have h := checkLog_sound (w := (5280492889 / 494719507111)) (n := 12)
    (lo := (2668529 / 125000000)) (hi := (21348233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244719507111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244719507111) = 1/(244719507111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21348233 / 1000000000) (-2668529 / 125000000) (Real.log (244719507111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34011 / 1600000) ≤ -Real.log (244741864831 / 250000000000) ∧
    -Real.log (244741864831 / 250000000000) ≤ (5314219 / 250000000) := by
  have h := checkLog_sound (w := (5258135169 / 494741864831)) (n := 12)
    (lo := (34011 / 1600000)) (hi := (5314219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244741864831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244741864831) = 1/(244741864831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5314219 / 250000000) (-34011 / 1600000) (Real.log (244741864831 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell061
