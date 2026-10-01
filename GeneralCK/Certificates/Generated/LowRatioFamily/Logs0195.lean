import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12480_neg : (529011369 / 1000000000) ≤ -Real.log (625000000 / 1060783451) ∧
    -Real.log (625000000 / 1060783451) ≤ (52901137 / 100000000) := by
  have h := checkLog_sound (w := (435783451 / 1685783451)) (n := 12)
    (lo := (529011369 / 1000000000)) (hi := (52901137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060783451 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1060783451 / 625000000) = 1/(625000000 / 1060783451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12480 : Bounds (529011369 / 1000000000) (52901137 / 100000000) (Real.log (1060783451 / 625000000)) := by
  have h := reflection_log_12480_neg
  have he : Real.log (1060783451 / 625000000) = -Real.log (625000000 / 1060783451) := by
    rw [show ((1060783451 / 625000000) : ℝ) = ((625000000 / 1060783451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12481_neg : (531251683 / 1000000000) ≤ -Real.log (250000000000 / 425265041529) ∧
    -Real.log (250000000000 / 425265041529) ≤ (132812921 / 250000000) := by
  have h := checkLog_sound (w := (175265041529 / 675265041529)) (n := 12)
    (lo := (531251683 / 1000000000)) (hi := (132812921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425265041529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425265041529 / 250000000000) = 1/(250000000000 / 425265041529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12481 : Bounds (531251683 / 1000000000) (132812921 / 250000000) (Real.log (425265041529 / 250000000000)) := by
  have h := reflection_log_12481_neg
  have he : Real.log (425265041529 / 250000000000) = -Real.log (250000000000 / 425265041529) := by
    rw [show ((425265041529 / 250000000000) : ℝ) = ((250000000000 / 425265041529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12482_neg : (216535139 / 200000000) ≤ -Real.log (25000000000 / 73814229249) ∧
    -Real.log (25000000000 / 73814229249) ≤ (1082675697 / 1000000000) := by
  have h := checkLog_sound (w := (23814229249 / 123814229249)) (n := 12)
    (lo := (77905703 / 200000000)) (hi := (97382129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73814229249 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73814229249 / 50000000000) = 1/(25000000000 / 73814229249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12482 : Bounds (216535139 / 200000000) (1082675697 / 1000000000) (Real.log (73814229249 / 25000000000)) := by
  have h := reflection_log_12482_neg
  have he : Real.log (73814229249 / 25000000000) = -Real.log (25000000000 / 73814229249) := by
    rw [show ((73814229249 / 25000000000) : ℝ) = ((25000000000 / 73814229249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12483_neg : (217064611 / 200000000) ≤ -Real.log (250000000000 / 740099009901) ∧
    -Real.log (250000000000 / 740099009901) ≤ (1085323057 / 1000000000) := by
  have h := checkLog_sound (w := (240099009901 / 1240099009901)) (n := 12)
    (lo := (3137407 / 8000000)) (hi := (98043969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740099009901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(740099009901 / 500000000000) = 1/(250000000000 / 740099009901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12483 : Bounds (217064611 / 200000000) (1085323057 / 1000000000) (Real.log (740099009901 / 250000000000)) := by
  have h := reflection_log_12483_neg
  have he : Real.log (740099009901 / 250000000000) = -Real.log (250000000000 / 740099009901) := by
    rw [show ((740099009901 / 250000000000) : ℝ) = ((250000000000 / 740099009901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12484_neg : (402794879 / 1000000000) ≤ -Real.log (125 / 187) ∧
    -Real.log (125 / 187) ≤ (629367 / 1562500) := by
  have h := checkLog_sound (w := (31 / 156)) (n := 12)
    (lo := (402794879 / 1000000000)) (hi := (629367 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187 / 125) = 1/(125 / 187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12484 : Bounds (402794879 / 1000000000) (629367 / 1562500) (Real.log (187 / 125)) := by
  have h := reflection_log_12484_neg
  have he : Real.log (187 / 125) = -Real.log (125 / 187) := by
    rw [show ((187 / 125) : ℝ) = ((125 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12485_neg : (68517901 / 100000000) ≤ -Real.log (63 / 125) ∧
    -Real.log (63 / 125) ≤ (685179011 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 94)) (n := 12)
    (lo := (68517901 / 100000000)) (hi := (685179011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 63) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 63) = 1/(63 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12485 : Bounds (-685179011 / 1000000000) (-68517901 / 100000000) (Real.log (63 / 125)) := by
  have h := reflection_log_12485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12486_neg : (495877 / 1000000000) ≤ -Real.log (62500 / 62531) ∧
    -Real.log (62500 / 62531) ≤ (247939 / 500000000) := by
  have h := checkLog_sound (w := (31 / 125031)) (n := 12)
    (lo := (495877 / 1000000000)) (hi := (247939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62531 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62531 / 62500) = 1/(62500 / 62531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12486 : Bounds (495877 / 1000000000) (247939 / 500000000) (Real.log (62531 / 62500)) := by
  have h := reflection_log_12486_neg
  have he : Real.log (62531 / 62500) = -Real.log (62500 / 62531) := by
    rw [show ((62531 / 62500) : ℝ) = ((62500 / 62531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12487_neg : (496123 / 1000000000) ≤ -Real.log (62469 / 62500) ∧
    -Real.log (62469 / 62500) ≤ (124031 / 250000000) := by
  have h := checkLog_sound (w := (31 / 124969)) (n := 12)
    (lo := (496123 / 1000000000)) (hi := (124031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62469) = 1/(62469 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12487 : Bounds (-124031 / 250000000) (-496123 / 1000000000) (Real.log (62469 / 62500)) := by
  have h := reflection_log_12487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12488_neg : (46076259 / 200000000) ≤ -Real.log (25000 / 31477) ∧
    -Real.log (25000 / 31477) ≤ (14398831 / 62500000) := by
  have h := checkLog_sound (w := (6477 / 56477)) (n := 12)
    (lo := (46076259 / 200000000)) (hi := (14398831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31477 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31477 / 25000) = 1/(25000 / 31477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12488 : Bounds (46076259 / 200000000) (14398831 / 62500000) (Real.log (31477 / 25000)) := by
  have h := reflection_log_12488_neg
  have he : Real.log (31477 / 25000) = -Real.log (25000 / 31477) := by
    rw [show ((31477 / 25000) : ℝ) = ((25000 / 31477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12489_neg : (299862621 / 1000000000) ≤ -Real.log (18523 / 25000) ∧
    -Real.log (18523 / 25000) ≤ (149931311 / 500000000) := by
  have h := checkLog_sound (w := (6477 / 43523)) (n := 12)
    (lo := (299862621 / 1000000000)) (hi := (149931311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 18523) = 1/(18523 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12489 : Bounds (-149931311 / 500000000) (-299862621 / 1000000000) (Real.log (18523 / 25000)) := by
  have h := reflection_log_12489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12490_neg : (46242343 / 200000000) ≤ -Real.log (500000 / 630063) ∧
    -Real.log (500000 / 630063) ≤ (57802929 / 250000000) := by
  have h := checkLog_sound (w := (130063 / 1130063)) (n := 12)
    (lo := (46242343 / 200000000)) (hi := (57802929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630063 / 500000) = 1/(500000 / 630063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12490 : Bounds (46242343 / 200000000) (57802929 / 250000000) (Real.log (630063 / 500000)) := by
  have h := reflection_log_12490_neg
  have he : Real.log (630063 / 500000) = -Real.log (500000 / 630063) := by
    rw [show ((630063 / 500000) : ℝ) = ((500000 / 630063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12491_neg : (301275377 / 1000000000) ≤ -Real.log (369937 / 500000) ∧
    -Real.log (369937 / 500000) ≤ (150637689 / 500000000) := by
  have h := checkLog_sound (w := (130063 / 869937)) (n := 12)
    (lo := (301275377 / 1000000000)) (hi := (150637689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369937) = 1/(369937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12491 : Bounds (-150637689 / 500000000) (-301275377 / 1000000000) (Real.log (369937 / 500000)) := by
  have h := reflection_log_12491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12492_neg : (70063661 / 1000000000) ≤ -Real.log (233083616031 / 250000000000) ∧
    -Real.log (233083616031 / 250000000000) ≤ (35031831 / 500000000) := by
  have h := checkLog_sound (w := (16916383969 / 483083616031)) (n := 12)
    (lo := (70063661 / 1000000000)) (hi := (35031831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233083616031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233083616031) = 1/(233083616031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12492 : Bounds (-35031831 / 500000000) (-70063661 / 1000000000) (Real.log (233083616031 / 250000000000)) := by
  have h := reflection_log_12492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12493_neg : (34740663 / 500000000) ≤ -Real.log (583048471 / 625000000) ∧
    -Real.log (583048471 / 625000000) ≤ (69481327 / 1000000000) := by
  have h := checkLog_sound (w := (41951529 / 1208048471)) (n := 12)
    (lo := (34740663 / 500000000)) (hi := (69481327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 583048471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 583048471) = 1/(583048471 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12493 : Bounds (-69481327 / 1000000000) (-34740663 / 500000000) (Real.log (583048471 / 625000000)) := by
  have h := reflection_log_12493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12494_neg : (530243917 / 1000000000) ≤ -Real.log (250000000000 / 424836689521) ∧
    -Real.log (250000000000 / 424836689521) ≤ (265121959 / 500000000) := by
  have h := checkLog_sound (w := (174836689521 / 674836689521)) (n := 12)
    (lo := (530243917 / 1000000000)) (hi := (265121959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424836689521 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424836689521 / 250000000000) = 1/(250000000000 / 424836689521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12494 : Bounds (530243917 / 1000000000) (265121959 / 500000000) (Real.log (424836689521 / 250000000000)) := by
  have h := reflection_log_12494_neg
  have he : Real.log (424836689521 / 250000000000) = -Real.log (250000000000 / 424836689521) := by
    rw [show ((424836689521 / 250000000000) : ℝ) = ((250000000000 / 424836689521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12495_neg : (532487093 / 1000000000) ≤ -Real.log (500000000000 / 851581485497) ∧
    -Real.log (500000000000 / 851581485497) ≤ (266243547 / 500000000) := by
  have h := checkLog_sound (w := (351581485497 / 1351581485497)) (n := 12)
    (lo := (532487093 / 1000000000)) (hi := (266243547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851581485497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851581485497 / 500000000000) = 1/(500000000000 / 851581485497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12495 : Bounds (532487093 / 1000000000) (266243547 / 500000000) (Real.log (851581485497 / 500000000000)) := by
  have h := reflection_log_12495_neg
  have he : Real.log (851581485497 / 500000000000) = -Real.log (500000000000 / 851581485497) := by
    rw [show ((851581485497 / 500000000000) : ℝ) = ((500000000000 / 851581485497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12496_neg : (217064611 / 200000000) ≤ -Real.log (500000000000 / 1480198019801) ∧
    -Real.log (500000000000 / 1480198019801) ≤ (1085323057 / 1000000000) := by
  have h := checkLog_sound (w := (480198019801 / 2480198019801)) (n := 12)
    (lo := (3137407 / 8000000)) (hi := (98043969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1480198019801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1480198019801 / 1000000000000) = 1/(500000000000 / 1480198019801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12496 : Bounds (217064611 / 200000000) (1085323057 / 1000000000) (Real.log (1480198019801 / 500000000000)) := by
  have h := reflection_log_12496_neg
  have he : Real.log (1480198019801 / 500000000000) = -Real.log (500000000000 / 1480198019801) := by
    rw [show ((1480198019801 / 500000000000) : ℝ) = ((500000000000 / 1480198019801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12497_neg : (1087973889 / 1000000000) ≤ -Real.log (500000000000 / 1484126984127) ∧
    -Real.log (500000000000 / 1484126984127) ≤ (1087973891 / 1000000000) := by
  have h := checkLog_sound (w := (484126984127 / 2484126984127)) (n := 12)
    (lo := (394826709 / 1000000000)) (hi := (39482671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1484126984127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1484126984127 / 1000000000000) = 1/(500000000000 / 1484126984127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12497 : Bounds (1087973889 / 1000000000) (1087973891 / 1000000000) (Real.log (1484126984127 / 500000000000)) := by
  have h := reflection_log_12497_neg
  have he : Real.log (1484126984127 / 500000000000) = -Real.log (500000000000 / 1484126984127) := by
    rw [show ((1484126984127 / 500000000000) : ℝ) = ((500000000000 / 1484126984127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12498_neg : (80692621 / 200000000) ≤ -Real.log (1000 / 1497) ∧
    -Real.log (1000 / 1497) ≤ (201731553 / 500000000) := by
  have h := checkLog_sound (w := (497 / 2497)) (n := 12)
    (lo := (80692621 / 200000000)) (hi := (201731553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1497 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1497 / 1000) = 1/(1000 / 1497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12498 : Bounds (80692621 / 200000000) (201731553 / 500000000) (Real.log (1497 / 1000)) := by
  have h := reflection_log_12498_neg
  have he : Real.log (1497 / 1000) = -Real.log (1000 / 1497) := by
    rw [show ((1497 / 1000) : ℝ) = ((1000 / 1497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12499_neg : (171791277 / 250000000) ≤ -Real.log (503 / 1000) ∧
    -Real.log (503 / 1000) ≤ (687165109 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 1503)) (n := 12)
    (lo := (171791277 / 250000000)) (hi := (687165109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 503) = 1/(503 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12499 : Bounds (-687165109 / 1000000000) (-171791277 / 250000000) (Real.log (503 / 1000)) := by
  have h := reflection_log_12499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12500_neg : (124219 / 250000000) ≤ -Real.log (1000000 / 1000497) ∧
    -Real.log (1000000 / 1000497) ≤ (496877 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2000497)) (n := 12)
    (lo := (124219 / 250000000)) (hi := (496877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000497 / 1000000) = 1/(1000000 / 1000497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12500 : Bounds (124219 / 250000000) (496877 / 1000000000) (Real.log (1000497 / 1000000)) := by
  have h := reflection_log_12500_neg
  have he : Real.log (1000497 / 1000000) = -Real.log (1000000 / 1000497) := by
    rw [show ((1000497 / 1000000) : ℝ) = ((1000000 / 1000497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12501_neg : (497123 / 1000000000) ≤ -Real.log (999503 / 1000000) ∧
    -Real.log (999503 / 1000000) ≤ (124281 / 250000000) := by
  have h := checkLog_sound (w := (497 / 1999503)) (n := 12)
    (lo := (497123 / 1000000000)) (hi := (124281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999503) = 1/(999503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12501 : Bounds (-124281 / 250000000) (-497123 / 1000000000) (Real.log (999503 / 1000000)) := by
  have h := reflection_log_12501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12502_neg : (230837873 / 1000000000) ≤ -Real.log (200000 / 251931) ∧
    -Real.log (200000 / 251931) ≤ (115418937 / 500000000) := by
  have h := checkLog_sound (w := (51931 / 451931)) (n := 12)
    (lo := (230837873 / 1000000000)) (hi := (115418937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251931 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251931 / 200000) = 1/(200000 / 251931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12502 : Bounds (230837873 / 1000000000) (115418937 / 500000000) (Real.log (251931 / 200000)) := by
  have h := reflection_log_12502_neg
  have he : Real.log (251931 / 200000) = -Real.log (200000 / 251931) := by
    rw [show ((251931 / 200000) : ℝ) = ((200000 / 251931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12503_neg : (60127797 / 200000000) ≤ -Real.log (148069 / 200000) ∧
    -Real.log (148069 / 200000) ≤ (150319493 / 500000000) := by
  have h := checkLog_sound (w := (51931 / 348069)) (n := 12)
    (lo := (60127797 / 200000000)) (hi := (150319493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148069) = 1/(148069 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12503 : Bounds (-150319493 / 500000000) (-60127797 / 200000000) (Real.log (148069 / 200000)) := by
  have h := reflection_log_12503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12504_neg : (231669501 / 1000000000) ≤ -Real.log (1000000 / 1260703) ∧
    -Real.log (1000000 / 1260703) ≤ (115834751 / 500000000) := by
  have h := checkLog_sound (w := (260703 / 2260703)) (n := 12)
    (lo := (231669501 / 1000000000)) (hi := (115834751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260703 / 1000000) = 1/(1000000 / 1260703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12504 : Bounds (231669501 / 1000000000) (115834751 / 500000000) (Real.log (1260703 / 1000000)) := by
  have h := reflection_log_12504_neg
  have he : Real.log (1260703 / 1000000) = -Real.log (1000000 / 1260703) := by
    rw [show ((1260703 / 1000000) : ℝ) = ((1000000 / 1260703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12505_neg : (37756943 / 125000000) ≤ -Real.log (739297 / 1000000) ∧
    -Real.log (739297 / 1000000) ≤ (60411109 / 200000000) := by
  have h := checkLog_sound (w := (260703 / 1739297)) (n := 12)
    (lo := (37756943 / 125000000)) (hi := (60411109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739297) = 1/(739297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12505 : Bounds (-60411109 / 200000000) (-37756943 / 125000000) (Real.log (739297 / 1000000)) := by
  have h := reflection_log_12505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12506_neg : (35193021 / 500000000) ≤ -Real.log (932033945791 / 1000000000000) ∧
    -Real.log (932033945791 / 1000000000000) ≤ (70386043 / 1000000000) := by
  have h := checkLog_sound (w := (67966054209 / 1932033945791)) (n := 12)
    (lo := (35193021 / 500000000)) (hi := (70386043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 932033945791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 932033945791) = 1/(932033945791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12506 : Bounds (-70386043 / 1000000000) (-35193021 / 500000000) (Real.log (932033945791 / 1000000000000)) := by
  have h := reflection_log_12506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12507_neg : (69801111 / 1000000000) ≤ -Real.log (37303171239 / 40000000000) ∧
    -Real.log (37303171239 / 40000000000) ≤ (8725139 / 125000000) := by
  have h := checkLog_sound (w := (2696828761 / 77303171239)) (n := 12)
    (lo := (69801111 / 1000000000)) (hi := (8725139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37303171239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37303171239) = 1/(37303171239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12507 : Bounds (-8725139 / 125000000) (-69801111 / 1000000000) (Real.log (37303171239 / 40000000000)) := by
  have h := reflection_log_12507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12508_neg : (531476859 / 1000000000) ≤ -Real.log (500000000000 / 850721623027) ∧
    -Real.log (500000000000 / 850721623027) ≤ (26573843 / 50000000) := by
  have h := checkLog_sound (w := (350721623027 / 1350721623027)) (n := 12)
    (lo := (531476859 / 1000000000)) (hi := (26573843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850721623027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850721623027 / 500000000000) = 1/(500000000000 / 850721623027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12508 : Bounds (531476859 / 1000000000) (26573843 / 50000000) (Real.log (850721623027 / 500000000000)) := by
  have h := reflection_log_12508_neg
  have he : Real.log (850721623027 / 500000000000) = -Real.log (500000000000 / 850721623027) := by
    rw [show ((850721623027 / 500000000000) : ℝ) = ((500000000000 / 850721623027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12509_neg : (266862523 / 500000000) ≤ -Real.log (50000000000 / 85263635589) ∧
    -Real.log (50000000000 / 85263635589) ≤ (533725047 / 1000000000) := by
  have h := checkLog_sound (w := (35263635589 / 135263635589)) (n := 12)
    (lo := (266862523 / 500000000)) (hi := (533725047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85263635589 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85263635589 / 50000000000) = 1/(50000000000 / 85263635589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12509 : Bounds (266862523 / 500000000) (533725047 / 1000000000) (Real.log (85263635589 / 50000000000)) := by
  have h := reflection_log_12509_neg
  have he : Real.log (85263635589 / 50000000000) = -Real.log (50000000000 / 85263635589) := by
    rw [show ((85263635589 / 50000000000) : ℝ) = ((50000000000 / 85263635589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12510_neg : (1087973889 / 1000000000) ≤ -Real.log (250000000000 / 742063492063) ∧
    -Real.log (250000000000 / 742063492063) ≤ (1087973891 / 1000000000) := by
  have h := checkLog_sound (w := (242063492063 / 1242063492063)) (n := 12)
    (lo := (394826709 / 1000000000)) (hi := (39482671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742063492063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(742063492063 / 500000000000) = 1/(250000000000 / 742063492063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12510 : Bounds (1087973889 / 1000000000) (1087973891 / 1000000000) (Real.log (742063492063 / 250000000000)) := by
  have h := reflection_log_12510_neg
  have he : Real.log (742063492063 / 250000000000) = -Real.log (250000000000 / 742063492063) := by
    rw [show ((742063492063 / 250000000000) : ℝ) = ((250000000000 / 742063492063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12511_neg : (1090628213 / 1000000000) ≤ -Real.log (500000000000 / 1488071570577) ∧
    -Real.log (500000000000 / 1488071570577) ≤ (218125643 / 200000000) := by
  have h := checkLog_sound (w := (488071570577 / 2488071570577)) (n := 12)
    (lo := (397481033 / 1000000000)) (hi := (198740517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1488071570577 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1488071570577 / 1000000000000) = 1/(500000000000 / 1488071570577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12511 : Bounds (1090628213 / 1000000000) (218125643 / 200000000) (Real.log (1488071570577 / 500000000000)) := by
  have h := reflection_log_12511_neg
  have he : Real.log (1488071570577 / 500000000000) = -Real.log (500000000000 / 1488071570577) := by
    rw [show ((1488071570577 / 500000000000) : ℝ) = ((500000000000 / 1488071570577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12512_neg : (80826177 / 200000000) ≤ -Real.log (500 / 749) ∧
    -Real.log (500 / 749) ≤ (202065443 / 500000000) := by
  have h := checkLog_sound (w := (249 / 1249)) (n := 12)
    (lo := (80826177 / 200000000)) (hi := (202065443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749 / 500) = 1/(500 / 749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12512 : Bounds (80826177 / 200000000) (202065443 / 500000000) (Real.log (749 / 500)) := by
  have h := reflection_log_12512_neg
  have he : Real.log (749 / 500) = -Real.log (500 / 749) := by
    rw [show ((749 / 500) : ℝ) = ((500 / 749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12513_neg : (689155159 / 1000000000) ≤ -Real.log (251 / 500) ∧
    -Real.log (251 / 500) ≤ (17228879 / 25000000) := by
  have h := checkLog_sound (w := (249 / 751)) (n := 12)
    (lo := (689155159 / 1000000000)) (hi := (17228879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 251) = 1/(251 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12513 : Bounds (-17228879 / 25000000) (-689155159 / 1000000000) (Real.log (251 / 500)) := by
  have h := reflection_log_12513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12514_neg : (124469 / 250000000) ≤ -Real.log (500000 / 500249) ∧
    -Real.log (500000 / 500249) ≤ (497877 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1000249)) (n := 12)
    (lo := (124469 / 250000000)) (hi := (497877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500249 / 500000) = 1/(500000 / 500249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12514 : Bounds (124469 / 250000000) (497877 / 1000000000) (Real.log (500249 / 500000)) := by
  have h := reflection_log_12514_neg
  have he : Real.log (500249 / 500000) = -Real.log (500000 / 500249) := by
    rw [show ((500249 / 500000) : ℝ) = ((500000 / 500249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12515_neg : (124531 / 250000000) ≤ -Real.log (499751 / 500000) ∧
    -Real.log (499751 / 500000) ≤ (797 / 1600000) := by
  have h := checkLog_sound (w := (249 / 999751)) (n := 12)
    (lo := (124531 / 250000000)) (hi := (797 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499751) = 1/(499751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12515 : Bounds (-797 / 1600000) (-124531 / 250000000) (Real.log (499751 / 500000)) := by
  have h := reflection_log_12515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12516_neg : (231295037 / 1000000000) ≤ -Real.log (1000000 / 1260231) ∧
    -Real.log (1000000 / 1260231) ≤ (115647519 / 500000000) := by
  have h := checkLog_sound (w := (260231 / 2260231)) (n := 12)
    (lo := (231295037 / 1000000000)) (hi := (115647519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260231 / 1000000) = 1/(1000000 / 1260231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12516 : Bounds (231295037 / 1000000000) (115647519 / 500000000) (Real.log (1260231 / 1000000)) := by
  have h := reflection_log_12516_neg
  have he : Real.log (1260231 / 1000000) = -Real.log (1000000 / 1260231) := by
    rw [show ((1260231 / 1000000) : ℝ) = ((1000000 / 1260231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12517_neg : (301417303 / 1000000000) ≤ -Real.log (739769 / 1000000) ∧
    -Real.log (739769 / 1000000) ≤ (37677163 / 125000000) := by
  have h := checkLog_sound (w := (260231 / 1739769)) (n := 12)
    (lo := (301417303 / 1000000000)) (hi := (37677163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739769) = 1/(739769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12517 : Bounds (-37677163 / 125000000) (-301417303 / 1000000000) (Real.log (739769 / 1000000)) := by
  have h := reflection_log_12517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12518_neg : (116063539 / 500000000) ≤ -Real.log (6250 / 7883) ∧
    -Real.log (6250 / 7883) ≤ (232127079 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 14133)) (n := 12)
    (lo := (116063539 / 500000000)) (hi := (232127079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7883 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7883 / 6250) = 1/(6250 / 7883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12518 : Bounds (116063539 / 500000000) (232127079 / 1000000000) (Real.log (7883 / 6250)) := by
  have h := reflection_log_12518_neg
  have he : Real.log (7883 / 6250) = -Real.log (6250 / 7883) := by
    rw [show ((7883 / 6250) : ℝ) = ((6250 / 7883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12519_neg : (1892727 / 6250000) ≤ -Real.log (4617 / 6250) ∧
    -Real.log (4617 / 6250) ≤ (302836321 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 10867)) (n := 12)
    (lo := (1892727 / 6250000)) (hi := (302836321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4617) = 1/(4617 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12519 : Bounds (-302836321 / 1000000000) (-1892727 / 6250000) (Real.log (4617 / 6250)) := by
  have h := reflection_log_12519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12520_neg : (70709241 / 1000000000) ≤ -Real.log (36395811 / 39062500) ∧
    -Real.log (36395811 / 39062500) ≤ (35354621 / 500000000) := by
  have h := checkLog_sound (w := (2666689 / 75458311)) (n := 12)
    (lo := (70709241 / 1000000000)) (hi := (35354621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 36395811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 36395811) = 1/(36395811 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12520 : Bounds (-35354621 / 500000000) (-70709241 / 1000000000) (Real.log (36395811 / 39062500)) := by
  have h := reflection_log_12520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12521_neg : (35061133 / 500000000) ≤ -Real.log (932279826639 / 1000000000000) ∧
    -Real.log (932279826639 / 1000000000000) ≤ (70122267 / 1000000000) := by
  have h := checkLog_sound (w := (67720173361 / 1932279826639)) (n := 12)
    (lo := (35061133 / 500000000)) (hi := (70122267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 932279826639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 932279826639) = 1/(932279826639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12521 : Bounds (-70122267 / 1000000000) (-35061133 / 500000000) (Real.log (932279826639 / 1000000000000)) := by
  have h := reflection_log_12521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12522_neg : (532712341 / 1000000000) ≤ -Real.log (250000000000 / 425886661917) ∧
    -Real.log (250000000000 / 425886661917) ≤ (266356171 / 500000000) := by
  have h := checkLog_sound (w := (175886661917 / 675886661917)) (n := 12)
    (lo := (532712341 / 1000000000)) (hi := (266356171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425886661917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425886661917 / 250000000000) = 1/(250000000000 / 425886661917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12522 : Bounds (532712341 / 1000000000) (266356171 / 500000000) (Real.log (425886661917 / 250000000000)) := by
  have h := reflection_log_12522_neg
  have he : Real.log (425886661917 / 250000000000) = -Real.log (250000000000 / 425886661917) := by
    rw [show ((425886661917 / 250000000000) : ℝ) = ((250000000000 / 425886661917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12523_neg : (267481699 / 500000000) ≤ -Real.log (500000000000 / 853692874161) ∧
    -Real.log (500000000000 / 853692874161) ≤ (534963399 / 1000000000) := by
  have h := checkLog_sound (w := (353692874161 / 1353692874161)) (n := 12)
    (lo := (267481699 / 500000000)) (hi := (534963399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853692874161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853692874161 / 500000000000) = 1/(500000000000 / 853692874161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12523 : Bounds (267481699 / 500000000) (534963399 / 1000000000) (Real.log (853692874161 / 500000000000)) := by
  have h := reflection_log_12523_neg
  have he : Real.log (853692874161 / 500000000000) = -Real.log (500000000000 / 853692874161) := by
    rw [show ((853692874161 / 500000000000) : ℝ) = ((500000000000 / 853692874161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12524_neg : (1090628213 / 1000000000) ≤ -Real.log (31250000000 / 93004473161) ∧
    -Real.log (31250000000 / 93004473161) ≤ (218125643 / 200000000) := by
  have h := checkLog_sound (w := (30504473161 / 155504473161)) (n := 12)
    (lo := (397481033 / 1000000000)) (hi := (198740517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93004473161 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(93004473161 / 62500000000) = 1/(31250000000 / 93004473161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12524 : Bounds (1090628213 / 1000000000) (218125643 / 200000000) (Real.log (93004473161 / 31250000000)) := by
  have h := reflection_log_12524_neg
  have he : Real.log (93004473161 / 31250000000) = -Real.log (31250000000 / 93004473161) := by
    rw [show ((93004473161 / 31250000000) : ℝ) = ((31250000000 / 93004473161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12525_neg : (1093286043 / 1000000000) ≤ -Real.log (50000000000 / 149203187251) ∧
    -Real.log (50000000000 / 149203187251) ≤ (218657209 / 200000000) := by
  have h := checkLog_sound (w := (49203187251 / 249203187251)) (n := 12)
    (lo := (400138863 / 1000000000)) (hi := (25008679 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149203187251 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(149203187251 / 100000000000) = 1/(50000000000 / 149203187251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12525 : Bounds (1093286043 / 1000000000) (218657209 / 200000000) (Real.log (149203187251 / 50000000000)) := by
  have h := reflection_log_12525_neg
  have he : Real.log (149203187251 / 50000000000) = -Real.log (50000000000 / 149203187251) := by
    rw [show ((149203187251 / 50000000000) : ℝ) = ((50000000000 / 149203187251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12526_neg : (404798219 / 1000000000) ≤ -Real.log (1000 / 1499) ∧
    -Real.log (1000 / 1499) ≤ (20239911 / 50000000) := by
  have h := checkLog_sound (w := (499 / 2499)) (n := 12)
    (lo := (404798219 / 1000000000)) (hi := (20239911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1000) = 1/(1000 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12526 : Bounds (404798219 / 1000000000) (20239911 / 50000000) (Real.log (1499 / 1000)) := by
  have h := reflection_log_12526_neg
  have he : Real.log (1499 / 1000) = -Real.log (1000 / 1499) := by
    rw [show ((1499 / 1000) : ℝ) = ((1000 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12527_neg : (691149177 / 1000000000) ≤ -Real.log (501 / 1000) ∧
    -Real.log (501 / 1000) ≤ (345574589 / 500000000) := by
  have h := checkLog_sound (w := (499 / 1501)) (n := 12)
    (lo := (691149177 / 1000000000)) (hi := (345574589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 501) = 1/(501 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12527 : Bounds (-345574589 / 500000000) (-691149177 / 1000000000) (Real.log (501 / 1000)) := by
  have h := reflection_log_12527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12528_neg : (3991 / 8000000) ≤ -Real.log (1000000 / 1000499) ∧
    -Real.log (1000000 / 1000499) ≤ (124719 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2000499)) (n := 12)
    (lo := (3991 / 8000000)) (hi := (124719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000499 / 1000000) = 1/(1000000 / 1000499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12528 : Bounds (3991 / 8000000) (124719 / 250000000) (Real.log (1000499 / 1000000)) := by
  have h := reflection_log_12528_neg
  have he : Real.log (1000499 / 1000000) = -Real.log (1000000 / 1000499) := by
    rw [show ((1000499 / 1000000) : ℝ) = ((1000000 / 1000499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12529_neg : (124781 / 250000000) ≤ -Real.log (999501 / 1000000) ∧
    -Real.log (999501 / 1000000) ≤ (3993 / 8000000) := by
  have h := checkLog_sound (w := (499 / 1999501)) (n := 12)
    (lo := (124781 / 250000000)) (hi := (3993 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999501) = 1/(999501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12529 : Bounds (-3993 / 8000000) (-124781 / 250000000) (Real.log (999501 / 1000000)) := by
  have h := reflection_log_12529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12530_neg : (28968999 / 125000000) ≤ -Real.log (1000000 / 1260807) ∧
    -Real.log (1000000 / 1260807) ≤ (231751993 / 1000000000) := by
  have h := checkLog_sound (w := (260807 / 2260807)) (n := 12)
    (lo := (28968999 / 125000000)) (hi := (231751993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260807 / 1000000) = 1/(1000000 / 1260807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12530 : Bounds (28968999 / 125000000) (231751993 / 1000000000) (Real.log (1260807 / 1000000)) := by
  have h := reflection_log_12530_neg
  have he : Real.log (1260807 / 1000000) = -Real.log (1000000 / 1260807) := by
    rw [show ((1260807 / 1000000) : ℝ) = ((1000000 / 1260807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12531_neg : (75549057 / 250000000) ≤ -Real.log (739193 / 1000000) ∧
    -Real.log (739193 / 1000000) ≤ (302196229 / 1000000000) := by
  have h := checkLog_sound (w := (260807 / 1739193)) (n := 12)
    (lo := (75549057 / 250000000)) (hi := (302196229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739193) = 1/(739193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12531 : Bounds (-302196229 / 1000000000) (-75549057 / 250000000) (Real.log (739193 / 1000000)) := by
  have h := reflection_log_12531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12532_neg : (46516889 / 200000000) ≤ -Real.log (1000000 / 1261857) ∧
    -Real.log (1000000 / 1261857) ≤ (116292223 / 500000000) := by
  have h := checkLog_sound (w := (261857 / 2261857)) (n := 12)
    (lo := (46516889 / 200000000)) (hi := (116292223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261857 / 1000000) = 1/(1000000 / 1261857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12532 : Bounds (46516889 / 200000000) (116292223 / 500000000) (Real.log (1261857 / 1000000)) := by
  have h := reflection_log_12532_neg
  have he : Real.log (1261857 / 1000000) = -Real.log (1000000 / 1261857) := by
    rw [show ((1261857 / 1000000) : ℝ) = ((1000000 / 1261857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12533_neg : (151808853 / 500000000) ≤ -Real.log (738143 / 1000000) ∧
    -Real.log (738143 / 1000000) ≤ (303617707 / 1000000000) := by
  have h := checkLog_sound (w := (261857 / 1738143)) (n := 12)
    (lo := (151808853 / 500000000)) (hi := (303617707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738143) = 1/(738143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12533 : Bounds (-303617707 / 1000000000) (-151808853 / 500000000) (Real.log (738143 / 1000000)) := by
  have h := reflection_log_12533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12534_neg : (3551663 / 50000000) ≤ -Real.log (931430911551 / 1000000000000) ∧
    -Real.log (931430911551 / 1000000000000) ≤ (71033261 / 1000000000) := by
  have h := checkLog_sound (w := (68569088449 / 1931430911551)) (n := 12)
    (lo := (3551663 / 50000000)) (hi := (71033261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931430911551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931430911551) = 1/(931430911551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12534 : Bounds (-71033261 / 1000000000) (-3551663 / 50000000) (Real.log (931430911551 / 1000000000000)) := by
  have h := reflection_log_12534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12535_neg : (17611059 / 250000000) ≤ -Real.log (931979708751 / 1000000000000) ∧
    -Real.log (931979708751 / 1000000000000) ≤ (70444237 / 1000000000) := by
  have h := checkLog_sound (w := (68020291249 / 1931979708751)) (n := 12)
    (lo := (17611059 / 250000000)) (hi := (70444237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 931979708751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 931979708751) = 1/(931979708751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12535 : Bounds (-70444237 / 1000000000) (-17611059 / 250000000) (Real.log (931979708751 / 1000000000000)) := by
  have h := reflection_log_12535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12536_neg : (26697411 / 50000000) ≤ -Real.log (62500000000 / 106603332959) ∧
    -Real.log (62500000000 / 106603332959) ≤ (533948221 / 1000000000) := by
  have h := checkLog_sound (w := (44103332959 / 169103332959)) (n := 12)
    (lo := (26697411 / 50000000)) (hi := (533948221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106603332959 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106603332959 / 62500000000) = 1/(62500000000 / 106603332959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12536 : Bounds (26697411 / 50000000) (533948221 / 1000000000) (Real.log (106603332959 / 62500000000)) := by
  have h := reflection_log_12536_neg
  have he : Real.log (106603332959 / 62500000000) = -Real.log (62500000000 / 106603332959) := by
    rw [show ((106603332959 / 62500000000) : ℝ) = ((62500000000 / 106603332959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12537_neg : (536202151 / 1000000000) ≤ -Real.log (20000000000 / 34190041767) ∧
    -Real.log (20000000000 / 34190041767) ≤ (67025269 / 125000000) := by
  have h := checkLog_sound (w := (14190041767 / 54190041767)) (n := 12)
    (lo := (536202151 / 1000000000)) (hi := (67025269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34190041767 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34190041767 / 20000000000) = 1/(20000000000 / 34190041767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12537 : Bounds (536202151 / 1000000000) (67025269 / 125000000) (Real.log (34190041767 / 20000000000)) := by
  have h := reflection_log_12537_neg
  have he : Real.log (34190041767 / 20000000000) = -Real.log (20000000000 / 34190041767) := by
    rw [show ((34190041767 / 20000000000) : ℝ) = ((20000000000 / 34190041767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12538_neg : (1093286043 / 1000000000) ≤ -Real.log (500000000000 / 1492031872509) ∧
    -Real.log (500000000000 / 1492031872509) ≤ (218657209 / 200000000) := by
  have h := checkLog_sound (w := (492031872509 / 2492031872509)) (n := 12)
    (lo := (400138863 / 1000000000)) (hi := (25008679 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1492031872509 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1492031872509 / 1000000000000) = 1/(500000000000 / 1492031872509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12538 : Bounds (1093286043 / 1000000000) (218657209 / 200000000) (Real.log (1492031872509 / 500000000000)) := by
  have h := reflection_log_12538_neg
  have he : Real.log (1492031872509 / 500000000000) = -Real.log (500000000000 / 1492031872509) := by
    rw [show ((1492031872509 / 500000000000) : ℝ) = ((500000000000 / 1492031872509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12539_neg : (273986849 / 250000000) ≤ -Real.log (15625000000 / 46750249501) ∧
    -Real.log (15625000000 / 46750249501) ≤ (547973699 / 500000000) := by
  have h := checkLog_sound (w := (15500249501 / 78000249501)) (n := 12)
    (lo := (50350027 / 125000000)) (hi := (402800217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46750249501 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(46750249501 / 31250000000) = 1/(15625000000 / 46750249501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12539 : Bounds (273986849 / 250000000) (547973699 / 500000000) (Real.log (46750249501 / 15625000000)) := by
  have h := reflection_log_12539_neg
  have he : Real.log (46750249501 / 15625000000) = -Real.log (15625000000 / 46750249501) := by
    rw [show ((46750249501 / 15625000000) : ℝ) = ((15625000000 / 46750249501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12540_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
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


theorem reflection_log_12540 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_12540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12541_neg : (3999 / 8000000) ≤ -Real.log (2000 / 2001) ∧
    -Real.log (2000 / 2001) ≤ (124969 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4001)) (n := 12)
    (lo := (3999 / 8000000)) (hi := (124969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2001 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2001 / 2000) = 1/(2000 / 2001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12541 : Bounds (3999 / 8000000) (124969 / 250000000) (Real.log (2001 / 2000)) := by
  have h := reflection_log_12541_neg
  have he : Real.log (2001 / 2000) = -Real.log (2000 / 2001) := by
    rw [show ((2001 / 2000) : ℝ) = ((2000 / 2001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12542_neg : (4001 / 8000000) ≤ -Real.log (1999 / 2000) ∧
    -Real.log (1999 / 2000) ≤ (250063 / 500000000) := by
  have h := checkLog_sound (w := (1 / 3999)) (n := 12)
    (lo := (4001 / 8000000)) (hi := (250063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1999) = 1/(1999 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12542 : Bounds (-250063 / 500000000) (-4001 / 8000000) (Real.log (1999 / 2000)) := by
  have h := reflection_log_12542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12543_neg : (116104369 / 500000000) ≤ -Real.log (1000000 / 1261383) ∧
    -Real.log (1000000 / 1261383) ≤ (232208739 / 1000000000) := by
  have h := checkLog_sound (w := (261383 / 2261383)) (n := 12)
    (lo := (116104369 / 500000000)) (hi := (232208739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261383 / 1000000) = 1/(1000000 / 1261383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12543 : Bounds (116104369 / 500000000) (232208739 / 1000000000) (Real.log (1261383 / 1000000)) := by
  have h := reflection_log_12543_neg
  have he : Real.log (1261383 / 1000000) = -Real.log (1000000 / 1261383) := by
    rw [show ((1261383 / 1000000) : ℝ) = ((1000000 / 1261383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
