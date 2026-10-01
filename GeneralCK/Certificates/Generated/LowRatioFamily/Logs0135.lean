import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8640_neg : (140675709 / 1000000000) ≤ -Real.log (868771 / 1000000) ∧
    -Real.log (868771 / 1000000) ≤ (14067571 / 100000000) := by
  have h := checkLog_sound (w := (131229 / 1868771)) (n := 12)
    (lo := (140675709 / 1000000000)) (hi := (14067571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868771) = 1/(868771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8640 : Bounds (-14067571 / 100000000) (-140675709 / 1000000000) (Real.log (868771 / 1000000)) := by
  have h := reflection_log_8640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8641_neg : (30940393 / 250000000) ≤ -Real.log (500000 / 565873) ∧
    -Real.log (500000 / 565873) ≤ (123761573 / 1000000000) := by
  have h := checkLog_sound (w := (65873 / 1065873)) (n := 12)
    (lo := (30940393 / 250000000)) (hi := (123761573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565873 / 500000) = 1/(500000 / 565873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8641 : Bounds (30940393 / 250000000) (123761573 / 1000000000) (Real.log (565873 / 500000)) := by
  have h := reflection_log_8641_neg
  have he : Real.log (565873 / 500000) = -Real.log (500000 / 565873) := by
    rw [show ((565873 / 500000) : ℝ) = ((500000 / 565873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8642_neg : (7063549 / 50000000) ≤ -Real.log (434127 / 500000) ∧
    -Real.log (434127 / 500000) ≤ (141270981 / 1000000000) := by
  have h := checkLog_sound (w := (65873 / 934127)) (n := 12)
    (lo := (7063549 / 50000000)) (hi := (141270981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434127) = 1/(434127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8642 : Bounds (-141270981 / 1000000000) (-7063549 / 50000000) (Real.log (434127 / 500000)) := by
  have h := reflection_log_8642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8643_neg : (17509407 / 1000000000) ≤ -Real.log (245660747871 / 250000000000) ∧
    -Real.log (245660747871 / 250000000000) ≤ (547169 / 31250000) := by
  have h := checkLog_sound (w := (4339252129 / 495660747871)) (n := 12)
    (lo := (17509407 / 1000000000)) (hi := (547169 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245660747871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245660747871) = 1/(245660747871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8643 : Bounds (-547169 / 31250000) (-17509407 / 1000000000) (Real.log (245660747871 / 250000000000)) := by
  have h := reflection_log_8643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8644_neg : (17371057 / 1000000000) ≤ -Real.log (982778949559 / 1000000000000) ∧
    -Real.log (982778949559 / 1000000000000) ≤ (8685529 / 500000000) := by
  have h := checkLog_sound (w := (17221050441 / 1982778949559)) (n := 12)
    (lo := (17371057 / 1000000000)) (hi := (8685529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982778949559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982778949559) = 1/(982778949559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8644 : Bounds (-8685529 / 500000000) (-17371057 / 1000000000) (Real.log (982778949559 / 1000000000000)) := by
  have h := reflection_log_8644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8645_neg : (131990181 / 500000000) ≤ -Real.log (125000000000 / 162762828179) ∧
    -Real.log (125000000000 / 162762828179) ≤ (263980363 / 1000000000) := by
  have h := checkLog_sound (w := (37762828179 / 287762828179)) (n := 12)
    (lo := (131990181 / 500000000)) (hi := (263980363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162762828179 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162762828179 / 125000000000) = 1/(125000000000 / 162762828179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8645 : Bounds (131990181 / 500000000) (263980363 / 1000000000) (Real.log (162762828179 / 125000000000)) := by
  have h := reflection_log_8645_neg
  have he : Real.log (162762828179 / 125000000000) = -Real.log (125000000000 / 162762828179) := by
    rw [show ((162762828179 / 125000000000) : ℝ) = ((125000000000 / 162762828179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8646_neg : (265032553 / 1000000000) ≤ -Real.log (15625000000 / 20366771993) ∧
    -Real.log (15625000000 / 20366771993) ≤ (132516277 / 500000000) := by
  have h := checkLog_sound (w := (4741771993 / 35991771993)) (n := 12)
    (lo := (265032553 / 1000000000)) (hi := (132516277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20366771993 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20366771993 / 15625000000) = 1/(15625000000 / 20366771993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8646 : Bounds (265032553 / 1000000000) (132516277 / 500000000) (Real.log (20366771993 / 15625000000)) := by
  have h := reflection_log_8646_neg
  have he : Real.log (20366771993 / 15625000000) = -Real.log (15625000000 / 20366771993) := by
    rw [show ((20366771993 / 15625000000) : ℝ) = ((15625000000 / 20366771993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8647_neg : (265572231 / 500000000) ≤ -Real.log (3125000000 / 5315243079) ∧
    -Real.log (3125000000 / 5315243079) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (2190243079 / 8440243079)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5315243079 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5315243079 / 3125000000) = 1/(3125000000 / 5315243079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8647 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (5315243079 / 3125000000)) := by
  have h := reflection_log_8647_neg
  have he : Real.log (5315243079 / 3125000000) = -Real.log (3125000000 / 5315243079) := by
    rw [show ((5315243079 / 3125000000) : ℝ) = ((3125000000 / 5315243079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8648_neg : (532216813 / 1000000000) ≤ -Real.log (62500000000 / 106418918919) ∧
    -Real.log (62500000000 / 106418918919) ≤ (266108407 / 500000000) := by
  have h := checkLog_sound (w := (43918918919 / 168918918919)) (n := 12)
    (lo := (532216813 / 1000000000)) (hi := (266108407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106418918919 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106418918919 / 62500000000) = 1/(62500000000 / 106418918919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8648 : Bounds (532216813 / 1000000000) (266108407 / 500000000) (Real.log (106418918919 / 62500000000)) := by
  have h := reflection_log_8648_neg
  have he : Real.log (106418918919 / 62500000000) = -Real.log (62500000000 / 106418918919) := by
    rw [show ((106418918919 / 62500000000) : ℝ) = ((62500000000 / 106418918919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8649_neg : (231508467 / 1000000000) ≤ -Real.log (2000 / 2521) ∧
    -Real.log (2000 / 2521) ≤ (57877117 / 250000000) := by
  have h := checkLog_sound (w := (521 / 4521)) (n := 12)
    (lo := (231508467 / 1000000000)) (hi := (57877117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 2000) = 1/(2000 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8649 : Bounds (231508467 / 1000000000) (57877117 / 250000000) (Real.log (2521 / 2000)) := by
  have h := reflection_log_8649_neg
  have he : Real.log (2521 / 2000) = -Real.log (2000 / 2521) := by
    rw [show ((2521 / 2000) : ℝ) = ((2000 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8650_neg : (75445249 / 250000000) ≤ -Real.log (1479 / 2000) ∧
    -Real.log (1479 / 2000) ≤ (301780997 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3479)) (n := 12)
    (lo := (75445249 / 250000000)) (hi := (301780997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1479) = 1/(1479 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8650 : Bounds (-301780997 / 1000000000) (-75445249 / 250000000) (Real.log (1479 / 2000)) := by
  have h := reflection_log_8650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8651_neg : (130233 / 500000000) ≤ -Real.log (2000000 / 2000521) ∧
    -Real.log (2000000 / 2000521) ≤ (260467 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4000521)) (n := 12)
    (lo := (130233 / 500000000)) (hi := (260467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000521 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000521 / 2000000) = 1/(2000000 / 2000521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8651 : Bounds (130233 / 500000000) (260467 / 1000000000) (Real.log (2000521 / 2000000)) := by
  have h := reflection_log_8651_neg
  have he : Real.log (2000521 / 2000000) = -Real.log (2000000 / 2000521) := by
    rw [show ((2000521 / 2000000) : ℝ) = ((2000000 / 2000521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8652_neg : (260533 / 1000000000) ≤ -Real.log (1999479 / 2000000) ∧
    -Real.log (1999479 / 2000000) ≤ (130267 / 500000000) := by
  have h := checkLog_sound (w := (521 / 3999479)) (n := 12)
    (lo := (260533 / 1000000000)) (hi := (130267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999479) = 1/(1999479 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8652 : Bounds (-130267 / 500000000) (-260533 / 1000000000) (Real.log (1999479 / 2000000)) := by
  have h := reflection_log_8652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8653_neg : (6176679 / 50000000) ≤ -Real.log (31250 / 35359) ∧
    -Real.log (31250 / 35359) ≤ (123533581 / 1000000000) := by
  have h := checkLog_sound (w := (4109 / 66609)) (n := 12)
    (lo := (6176679 / 50000000)) (hi := (123533581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35359 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35359 / 31250) = 1/(31250 / 35359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8653 : Bounds (6176679 / 50000000) (123533581 / 1000000000) (Real.log (35359 / 31250)) := by
  have h := reflection_log_8653_neg
  have he : Real.log (35359 / 31250) = -Real.log (31250 / 35359) := by
    rw [show ((35359 / 31250) : ℝ) = ((31250 / 35359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8654_neg : (35243469 / 250000000) ≤ -Real.log (27141 / 31250) ∧
    -Real.log (27141 / 31250) ≤ (140973877 / 1000000000) := by
  have h := checkLog_sound (w := (4109 / 58391)) (n := 12)
    (lo := (35243469 / 250000000)) (hi := (140973877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27141) = 1/(27141 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8654 : Bounds (-140973877 / 1000000000) (-35243469 / 250000000) (Real.log (27141 / 31250)) := by
  have h := reflection_log_8654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8655_neg : (1549891 / 12500000) ≤ -Real.log (500000 / 566003) ∧
    -Real.log (500000 / 566003) ≤ (123991281 / 1000000000) := by
  have h := checkLog_sound (w := (66003 / 1066003)) (n := 12)
    (lo := (1549891 / 12500000)) (hi := (123991281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566003 / 500000) = 1/(500000 / 566003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8655 : Bounds (1549891 / 12500000) (123991281 / 1000000000) (Real.log (566003 / 500000)) := by
  have h := reflection_log_8655_neg
  have he : Real.log (566003 / 500000) = -Real.log (500000 / 566003) := by
    rw [show ((566003 / 500000) : ℝ) = ((500000 / 566003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8656_neg : (35392619 / 250000000) ≤ -Real.log (433997 / 500000) ∧
    -Real.log (433997 / 500000) ≤ (141570477 / 1000000000) := by
  have h := checkLog_sound (w := (66003 / 933997)) (n := 12)
    (lo := (35392619 / 250000000)) (hi := (141570477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433997) = 1/(433997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8656 : Bounds (-141570477 / 1000000000) (-35392619 / 250000000) (Real.log (433997 / 500000)) := by
  have h := reflection_log_8656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8657_neg : (4394799 / 250000000) ≤ -Real.log (245643603991 / 250000000000) ∧
    -Real.log (245643603991 / 250000000000) ≤ (17579197 / 1000000000) := by
  have h := checkLog_sound (w := (4356396009 / 495643603991)) (n := 12)
    (lo := (4394799 / 250000000)) (hi := (17579197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245643603991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245643603991) = 1/(245643603991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8657 : Bounds (-17579197 / 1000000000) (-4394799 / 250000000) (Real.log (245643603991 / 250000000000)) := by
  have h := reflection_log_8657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8658_neg : (3488059 / 200000000) ≤ -Real.log (959678619 / 976562500) ∧
    -Real.log (959678619 / 976562500) ≤ (2180037 / 125000000) := by
  have h := checkLog_sound (w := (16883881 / 1936241119)) (n := 12)
    (lo := (3488059 / 200000000)) (hi := (2180037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 959678619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 959678619) = 1/(959678619 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8658 : Bounds (-2180037 / 125000000) (-3488059 / 200000000) (Real.log (959678619 / 976562500)) := by
  have h := reflection_log_8658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8659_neg : (264507457 / 1000000000) ≤ -Real.log (250000000000 / 325697284551) ∧
    -Real.log (250000000000 / 325697284551) ≤ (132253729 / 500000000) := by
  have h := checkLog_sound (w := (75697284551 / 575697284551)) (n := 12)
    (lo := (264507457 / 1000000000)) (hi := (132253729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325697284551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325697284551 / 250000000000) = 1/(250000000000 / 325697284551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8659 : Bounds (264507457 / 1000000000) (132253729 / 500000000) (Real.log (325697284551 / 250000000000)) := by
  have h := reflection_log_8659_neg
  have he : Real.log (325697284551 / 250000000000) = -Real.log (250000000000 / 325697284551) := by
    rw [show ((325697284551 / 250000000000) : ℝ) = ((250000000000 / 325697284551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8660_neg : (66390439 / 250000000) ≤ -Real.log (250000000000 / 326040848209) ∧
    -Real.log (250000000000 / 326040848209) ≤ (265561757 / 1000000000) := by
  have h := checkLog_sound (w := (76040848209 / 576040848209)) (n := 12)
    (lo := (66390439 / 250000000)) (hi := (265561757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326040848209 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326040848209 / 250000000000) = 1/(250000000000 / 326040848209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8660 : Bounds (66390439 / 250000000) (265561757 / 1000000000) (Real.log (326040848209 / 250000000000)) := by
  have h := reflection_log_8660_neg
  have he : Real.log (326040848209 / 250000000000) = -Real.log (250000000000 / 326040848209) := by
    rw [show ((326040848209 / 250000000000) : ℝ) = ((250000000000 / 326040848209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8661_neg : (532216813 / 1000000000) ≤ -Real.log (500000000000 / 851351351351) ∧
    -Real.log (500000000000 / 851351351351) ≤ (266108407 / 500000000) := by
  have h := checkLog_sound (w := (351351351351 / 1351351351351)) (n := 12)
    (lo := (532216813 / 1000000000)) (hi := (266108407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851351351351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851351351351 / 500000000000) = 1/(500000000000 / 851351351351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8661 : Bounds (532216813 / 1000000000) (266108407 / 500000000) (Real.log (851351351351 / 500000000000)) := by
  have h := reflection_log_8661_neg
  have he : Real.log (851351351351 / 500000000000) = -Real.log (500000000000 / 851351351351) := by
    rw [show ((851351351351 / 500000000000) : ℝ) = ((500000000000 / 851351351351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8662_neg : (66661183 / 125000000) ≤ -Real.log (500000000000 / 852265043949) ∧
    -Real.log (500000000000 / 852265043949) ≤ (106657893 / 200000000) := by
  have h := checkLog_sound (w := (352265043949 / 1352265043949)) (n := 12)
    (lo := (66661183 / 125000000)) (hi := (106657893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852265043949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852265043949 / 500000000000) = 1/(500000000000 / 852265043949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8662 : Bounds (66661183 / 125000000) (106657893 / 200000000) (Real.log (852265043949 / 500000000000)) := by
  have h := reflection_log_8662_neg
  have he : Real.log (852265043949 / 500000000000) = -Real.log (500000000000 / 852265043949) := by
    rw [show ((852265043949 / 500000000000) : ℝ) = ((500000000000 / 852265043949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8663_neg : (7247033 / 31250000) ≤ -Real.log (1000 / 1261) ∧
    -Real.log (1000 / 1261) ≤ (231905057 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 2261)) (n := 12)
    (lo := (7247033 / 31250000)) (hi := (231905057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261 / 1000) = 1/(1000 / 1261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8663 : Bounds (7247033 / 31250000) (231905057 / 1000000000) (Real.log (1261 / 1000)) := by
  have h := reflection_log_8663_neg
  have he : Real.log (1261 / 1000) = -Real.log (1000 / 1261) := by
    rw [show ((1261 / 1000) : ℝ) = ((1000 / 1261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8664_neg : (151228679 / 500000000) ≤ -Real.log (739 / 1000) ∧
    -Real.log (739 / 1000) ≤ (302457359 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1739)) (n := 12)
    (lo := (151228679 / 500000000)) (hi := (302457359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 739) = 1/(739 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8664 : Bounds (-302457359 / 1000000000) (-151228679 / 500000000) (Real.log (739 / 1000)) := by
  have h := reflection_log_8664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8665_neg : (52193 / 200000000) ≤ -Real.log (1000000 / 1000261) ∧
    -Real.log (1000000 / 1000261) ≤ (130483 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2000261)) (n := 12)
    (lo := (52193 / 200000000)) (hi := (130483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000261 / 1000000) = 1/(1000000 / 1000261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8665 : Bounds (52193 / 200000000) (130483 / 500000000) (Real.log (1000261 / 1000000)) := by
  have h := reflection_log_8665_neg
  have he : Real.log (1000261 / 1000000) = -Real.log (1000000 / 1000261) := by
    rw [show ((1000261 / 1000000) : ℝ) = ((1000000 / 1000261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8666_neg : (130517 / 500000000) ≤ -Real.log (999739 / 1000000) ∧
    -Real.log (999739 / 1000000) ≤ (52207 / 200000000) := by
  have h := checkLog_sound (w := (261 / 1999739)) (n := 12)
    (lo := (130517 / 500000000)) (hi := (52207 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999739) = 1/(999739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8666 : Bounds (-52207 / 200000000) (-130517 / 500000000) (Real.log (999739 / 1000000)) := by
  have h := reflection_log_8666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8667_neg : (15470307 / 125000000) ≤ -Real.log (1000000 / 1131747) ∧
    -Real.log (1000000 / 1131747) ≤ (123762457 / 1000000000) := by
  have h := checkLog_sound (w := (131747 / 2131747)) (n := 12)
    (lo := (15470307 / 125000000)) (hi := (123762457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131747 / 1000000) = 1/(1000000 / 1131747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8667 : Bounds (15470307 / 125000000) (123762457 / 1000000000) (Real.log (1131747 / 1000000)) := by
  have h := reflection_log_8667_neg
  have he : Real.log (1131747 / 1000000) = -Real.log (1000000 / 1131747) := by
    rw [show ((1131747 / 1000000) : ℝ) = ((1000000 / 1131747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8668_neg : (35318033 / 250000000) ≤ -Real.log (868253 / 1000000) ∧
    -Real.log (868253 / 1000000) ≤ (141272133 / 1000000000) := by
  have h := checkLog_sound (w := (131747 / 1868253)) (n := 12)
    (lo := (35318033 / 250000000)) (hi := (141272133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868253) = 1/(868253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8668 : Bounds (-141272133 / 1000000000) (-35318033 / 250000000) (Real.log (868253 / 1000000)) := by
  have h := reflection_log_8668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8669_neg : (124220051 / 1000000000) ≤ -Real.log (200000 / 226453) ∧
    -Real.log (200000 / 226453) ≤ (31055013 / 250000000) := by
  have h := checkLog_sound (w := (26453 / 426453)) (n := 12)
    (lo := (124220051 / 1000000000)) (hi := (31055013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226453 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226453 / 200000) = 1/(200000 / 226453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8669 : Bounds (124220051 / 1000000000) (31055013 / 250000000) (Real.log (226453 / 200000)) := by
  have h := reflection_log_8669_neg
  have he : Real.log (226453 / 200000) = -Real.log (200000 / 226453) := by
    rw [show ((226453 / 200000) : ℝ) = ((200000 / 226453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8670_neg : (14186891 / 100000000) ≤ -Real.log (173547 / 200000) ∧
    -Real.log (173547 / 200000) ≤ (141868911 / 1000000000) := by
  have h := checkLog_sound (w := (26453 / 373547)) (n := 12)
    (lo := (14186891 / 100000000)) (hi := (141868911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173547) = 1/(173547 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8670 : Bounds (-141868911 / 1000000000) (-14186891 / 100000000) (Real.log (173547 / 200000)) := by
  have h := reflection_log_8670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8671_neg : (17648859 / 1000000000) ≤ -Real.log (39300238791 / 40000000000) ∧
    -Real.log (39300238791 / 40000000000) ≤ (882443 / 50000000) := by
  have h := checkLog_sound (w := (699761209 / 79300238791)) (n := 12)
    (lo := (17648859 / 1000000000)) (hi := (882443 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39300238791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39300238791) = 1/(39300238791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8671 : Bounds (-882443 / 50000000) (-17648859 / 1000000000) (Real.log (39300238791 / 40000000000)) := by
  have h := reflection_log_8671_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8672_neg : (700387 / 40000000) ≤ -Real.log (982642727991 / 1000000000000) ∧
    -Real.log (982642727991 / 1000000000000) ≤ (4377419 / 250000000) := by
  have h := checkLog_sound (w := (17357272009 / 1982642727991)) (n := 12)
    (lo := (700387 / 40000000)) (hi := (4377419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982642727991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982642727991) = 1/(982642727991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8672 : Bounds (-4377419 / 250000000) (-700387 / 40000000) (Real.log (982642727991 / 1000000000000)) := by
  have h := reflection_log_8672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8673_neg : (66258647 / 250000000) ≤ -Real.log (250000000000 / 325869015137) ∧
    -Real.log (250000000000 / 325869015137) ≤ (265034589 / 1000000000) := by
  have h := checkLog_sound (w := (75869015137 / 575869015137)) (n := 12)
    (lo := (66258647 / 250000000)) (hi := (265034589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325869015137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325869015137 / 250000000000) = 1/(250000000000 / 325869015137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8673 : Bounds (66258647 / 250000000) (265034589 / 1000000000) (Real.log (325869015137 / 250000000000)) := by
  have h := reflection_log_8673_neg
  have he : Real.log (325869015137 / 250000000000) = -Real.log (250000000000 / 325869015137) := by
    rw [show ((325869015137 / 250000000000) : ℝ) = ((250000000000 / 325869015137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8674_neg : (266088961 / 1000000000) ≤ -Real.log (250000000000 / 326212783857) ∧
    -Real.log (250000000000 / 326212783857) ≤ (133044481 / 500000000) := by
  have h := checkLog_sound (w := (76212783857 / 576212783857)) (n := 12)
    (lo := (266088961 / 1000000000)) (hi := (133044481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326212783857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326212783857 / 250000000000) = 1/(250000000000 / 326212783857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8674 : Bounds (266088961 / 1000000000) (133044481 / 500000000) (Real.log (326212783857 / 250000000000)) := by
  have h := reflection_log_8674_neg
  have he : Real.log (326212783857 / 250000000000) = -Real.log (250000000000 / 326212783857) := by
    rw [show ((326212783857 / 250000000000) : ℝ) = ((250000000000 / 326212783857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8675_neg : (66661183 / 125000000) ≤ -Real.log (125000000000 / 213066260987) ∧
    -Real.log (125000000000 / 213066260987) ≤ (106657893 / 200000000) := by
  have h := checkLog_sound (w := (88066260987 / 338066260987)) (n := 12)
    (lo := (66661183 / 125000000)) (hi := (106657893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213066260987 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213066260987 / 125000000000) = 1/(125000000000 / 213066260987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8675 : Bounds (66661183 / 125000000) (106657893 / 200000000) (Real.log (213066260987 / 125000000000)) := by
  have h := reflection_log_8675_neg
  have he : Real.log (213066260987 / 125000000000) = -Real.log (125000000000 / 213066260987) := by
    rw [show ((213066260987 / 125000000000) : ℝ) = ((125000000000 / 213066260987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8676_neg : (106872483 / 200000000) ≤ -Real.log (500000000000 / 853179972937) ∧
    -Real.log (500000000000 / 853179972937) ≤ (33397651 / 62500000) := by
  have h := checkLog_sound (w := (353179972937 / 1353179972937)) (n := 12)
    (lo := (106872483 / 200000000)) (hi := (33397651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853179972937 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853179972937 / 500000000000) = 1/(500000000000 / 853179972937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8676 : Bounds (106872483 / 200000000) (33397651 / 62500000) (Real.log (853179972937 / 500000000000)) := by
  have h := reflection_log_8676_neg
  have he : Real.log (853179972937 / 500000000000) = -Real.log (500000000000 / 853179972937) := by
    rw [show ((853179972937 / 500000000000) : ℝ) = ((500000000000 / 853179972937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8677_neg : (232301489 / 1000000000) ≤ -Real.log (2000 / 2523) ∧
    -Real.log (2000 / 2523) ≤ (23230149 / 100000000) := by
  have h := checkLog_sound (w := (523 / 4523)) (n := 12)
    (lo := (232301489 / 1000000000)) (hi := (23230149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2000) = 1/(2000 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8677 : Bounds (232301489 / 1000000000) (23230149 / 100000000) (Real.log (2523 / 2000)) := by
  have h := reflection_log_8677_neg
  have he : Real.log (2523 / 2000) = -Real.log (2000 / 2523) := by
    rw [show ((2523 / 2000) : ℝ) = ((2000 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8678_neg : (303134177 / 1000000000) ≤ -Real.log (1477 / 2000) ∧
    -Real.log (1477 / 2000) ≤ (151567089 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3477)) (n := 12)
    (lo := (303134177 / 1000000000)) (hi := (151567089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1477) = 1/(1477 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8678 : Bounds (-151567089 / 500000000) (-303134177 / 1000000000) (Real.log (1477 / 2000)) := by
  have h := reflection_log_8678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8679_neg : (52293 / 200000000) ≤ -Real.log (2000000 / 2000523) ∧
    -Real.log (2000000 / 2000523) ≤ (130733 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4000523)) (n := 12)
    (lo := (52293 / 200000000)) (hi := (130733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000523 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000523 / 2000000) = 1/(2000000 / 2000523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8679 : Bounds (52293 / 200000000) (130733 / 500000000) (Real.log (2000523 / 2000000)) := by
  have h := reflection_log_8679_neg
  have he : Real.log (2000523 / 2000000) = -Real.log (2000000 / 2000523) := by
    rw [show ((2000523 / 2000000) : ℝ) = ((2000000 / 2000523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8680_neg : (130767 / 500000000) ≤ -Real.log (1999477 / 2000000) ∧
    -Real.log (1999477 / 2000000) ≤ (52307 / 200000000) := by
  have h := checkLog_sound (w := (523 / 3999477)) (n := 12)
    (lo := (130767 / 500000000)) (hi := (52307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999477) = 1/(1999477 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8680 : Bounds (-52307 / 200000000) (-130767 / 500000000) (Real.log (1999477 / 2000000)) := by
  have h := reflection_log_8680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8681_neg : (123992163 / 1000000000) ≤ -Real.log (1000000 / 1132007) ∧
    -Real.log (1000000 / 1132007) ≤ (30998041 / 250000000) := by
  have h := checkLog_sound (w := (132007 / 2132007)) (n := 12)
    (lo := (123992163 / 1000000000)) (hi := (30998041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1132007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1132007 / 1000000) = 1/(1000000 / 1132007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8681 : Bounds (123992163 / 1000000000) (30998041 / 250000000) (Real.log (1132007 / 1000000)) := by
  have h := reflection_log_8681_neg
  have he : Real.log (1132007 / 1000000) = -Real.log (1000000 / 1132007) := by
    rw [show ((1132007 / 1000000) : ℝ) = ((1000000 / 1132007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8682_neg : (35392907 / 250000000) ≤ -Real.log (867993 / 1000000) ∧
    -Real.log (867993 / 1000000) ≤ (141571629 / 1000000000) := by
  have h := checkLog_sound (w := (132007 / 1867993)) (n := 12)
    (lo := (35392907 / 250000000)) (hi := (141571629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 867993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 867993) = 1/(867993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8682 : Bounds (-141571629 / 1000000000) (-35392907 / 250000000) (Real.log (867993 / 1000000)) := by
  have h := reflection_log_8682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8683_neg : (124449653 / 1000000000) ≤ -Real.log (40000 / 45301) ∧
    -Real.log (40000 / 45301) ≤ (62224827 / 500000000) := by
  have h := checkLog_sound (w := (5301 / 85301)) (n := 12)
    (lo := (124449653 / 1000000000)) (hi := (62224827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45301 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45301 / 40000) = 1/(40000 / 45301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8683 : Bounds (124449653 / 1000000000) (62224827 / 500000000) (Real.log (45301 / 40000)) := by
  have h := reflection_log_8683_neg
  have he : Real.log (45301 / 40000) = -Real.log (40000 / 45301) := by
    rw [show ((45301 / 40000) : ℝ) = ((40000 / 45301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8684_neg : (71084293 / 500000000) ≤ -Real.log (34699 / 40000) ∧
    -Real.log (34699 / 40000) ≤ (142168587 / 1000000000) := by
  have h := checkLog_sound (w := (5301 / 74699)) (n := 12)
    (lo := (71084293 / 500000000)) (hi := (142168587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34699) = 1/(34699 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8684 : Bounds (-142168587 / 1000000000) (-71084293 / 500000000) (Real.log (34699 / 40000)) := by
  have h := reflection_log_8684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8685_neg : (4429733 / 250000000) ≤ -Real.log (1571899399 / 1600000000) ∧
    -Real.log (1571899399 / 1600000000) ≤ (17718933 / 1000000000) := by
  have h := checkLog_sound (w := (28100601 / 3171899399)) (n := 12)
    (lo := (4429733 / 250000000)) (hi := (17718933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1571899399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1571899399) = 1/(1571899399 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8685 : Bounds (-17718933 / 1000000000) (-4429733 / 250000000) (Real.log (1571899399 / 1600000000)) := by
  have h := reflection_log_8685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8686_neg : (3515893 / 200000000) ≤ -Real.log (982574151951 / 1000000000000) ∧
    -Real.log (982574151951 / 1000000000000) ≤ (8789733 / 500000000) := by
  have h := checkLog_sound (w := (17425848049 / 1982574151951)) (n := 12)
    (lo := (3515893 / 200000000)) (hi := (8789733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982574151951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982574151951) = 1/(982574151951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8686 : Bounds (-8789733 / 500000000) (-3515893 / 200000000) (Real.log (982574151951 / 1000000000000)) := by
  have h := reflection_log_8686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8687_neg : (16597737 / 62500000) ≤ -Real.log (500000000000 / 652083023711) ∧
    -Real.log (500000000000 / 652083023711) ≤ (265563793 / 1000000000) := by
  have h := checkLog_sound (w := (152083023711 / 1152083023711)) (n := 12)
    (lo := (16597737 / 62500000)) (hi := (265563793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652083023711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652083023711 / 500000000000) = 1/(500000000000 / 652083023711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8687 : Bounds (16597737 / 62500000) (265563793 / 1000000000) (Real.log (652083023711 / 500000000000)) := by
  have h := reflection_log_8687_neg
  have he : Real.log (652083023711 / 500000000000) = -Real.log (500000000000 / 652083023711) := by
    rw [show ((652083023711 / 500000000000) : ℝ) = ((500000000000 / 652083023711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8688_neg : (266618239 / 1000000000) ≤ -Real.log (500000000000 / 652770973227) ∧
    -Real.log (500000000000 / 652770973227) ≤ (416591 / 1562500) := by
  have h := checkLog_sound (w := (152770973227 / 1152770973227)) (n := 12)
    (lo := (266618239 / 1000000000)) (hi := (416591 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652770973227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652770973227 / 500000000000) = 1/(500000000000 / 652770973227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8688 : Bounds (266618239 / 1000000000) (416591 / 1562500) (Real.log (652770973227 / 500000000000)) := by
  have h := reflection_log_8688_neg
  have he : Real.log (652770973227 / 500000000000) = -Real.log (500000000000 / 652770973227) := by
    rw [show ((652770973227 / 500000000000) : ℝ) = ((500000000000 / 652770973227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8689_neg : (106872483 / 200000000) ≤ -Real.log (62500000000 / 106647496617) ∧
    -Real.log (62500000000 / 106647496617) ≤ (33397651 / 62500000) := by
  have h := checkLog_sound (w := (44147496617 / 169147496617)) (n := 12)
    (lo := (106872483 / 200000000)) (hi := (33397651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106647496617 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106647496617 / 62500000000) = 1/(62500000000 / 106647496617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8689 : Bounds (106872483 / 200000000) (33397651 / 62500000) (Real.log (106647496617 / 62500000000)) := by
  have h := reflection_log_8689_neg
  have he : Real.log (106647496617 / 62500000000) = -Real.log (62500000000 / 106647496617) := by
    rw [show ((106647496617 / 62500000000) : ℝ) = ((62500000000 / 106647496617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8690_neg : (267717833 / 500000000) ≤ -Real.log (250000000000 / 427048070413) ∧
    -Real.log (250000000000 / 427048070413) ≤ (535435667 / 1000000000) := by
  have h := checkLog_sound (w := (177048070413 / 677048070413)) (n := 12)
    (lo := (267717833 / 500000000)) (hi := (535435667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427048070413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427048070413 / 250000000000) = 1/(250000000000 / 427048070413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8690 : Bounds (267717833 / 500000000) (535435667 / 1000000000) (Real.log (427048070413 / 250000000000)) := by
  have h := reflection_log_8690_neg
  have he : Real.log (427048070413 / 250000000000) = -Real.log (250000000000 / 427048070413) := by
    rw [show ((427048070413 / 250000000000) : ℝ) = ((250000000000 / 427048070413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8691_neg : (58174441 / 250000000) ≤ -Real.log (500 / 631) ∧
    -Real.log (500 / 631) ≤ (46539553 / 200000000) := by
  have h := checkLog_sound (w := (131 / 1131)) (n := 12)
    (lo := (58174441 / 250000000)) (hi := (46539553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 500) = 1/(500 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8691 : Bounds (58174441 / 250000000) (46539553 / 200000000) (Real.log (631 / 500)) := by
  have h := reflection_log_8691_neg
  have he : Real.log (631 / 500) = -Real.log (500 / 631) := by
    rw [show ((631 / 500) : ℝ) = ((500 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8692_neg : (151905727 / 500000000) ≤ -Real.log (369 / 500) ∧
    -Real.log (369 / 500) ≤ (60762291 / 200000000) := by
  have h := checkLog_sound (w := (131 / 869)) (n := 12)
    (lo := (151905727 / 500000000)) (hi := (60762291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 369) = 1/(369 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8692 : Bounds (-60762291 / 200000000) (-151905727 / 500000000) (Real.log (369 / 500)) := by
  have h := reflection_log_8692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8693_neg : (52393 / 200000000) ≤ -Real.log (500000 / 500131) ∧
    -Real.log (500000 / 500131) ≤ (130983 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1000131)) (n := 12)
    (lo := (52393 / 200000000)) (hi := (130983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500131 / 500000) = 1/(500000 / 500131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8693 : Bounds (52393 / 200000000) (130983 / 500000000) (Real.log (500131 / 500000)) := by
  have h := reflection_log_8693_neg
  have he : Real.log (500131 / 500000) = -Real.log (500000 / 500131) := by
    rw [show ((500131 / 500000) : ℝ) = ((500000 / 500131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8694_neg : (131017 / 500000000) ≤ -Real.log (499869 / 500000) ∧
    -Real.log (499869 / 500000) ≤ (52407 / 200000000) := by
  have h := checkLog_sound (w := (131 / 999869)) (n := 12)
    (lo := (131017 / 500000000)) (hi := (52407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499869) = 1/(499869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8694 : Bounds (-52407 / 200000000) (-131017 / 500000000) (Real.log (499869 / 500000)) := by
  have h := reflection_log_8694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8695_neg : (62110467 / 500000000) ≤ -Real.log (500000 / 566133) ∧
    -Real.log (500000 / 566133) ≤ (24844187 / 200000000) := by
  have h := checkLog_sound (w := (66133 / 1066133)) (n := 12)
    (lo := (62110467 / 500000000)) (hi := (24844187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566133 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(566133 / 500000) = 1/(500000 / 566133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8695 : Bounds (62110467 / 500000000) (24844187 / 200000000) (Real.log (566133 / 500000)) := by
  have h := reflection_log_8695_neg
  have he : Real.log (566133 / 500000) = -Real.log (500000 / 566133) := by
    rw [show ((566133 / 500000) : ℝ) = ((500000 / 566133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8696_neg : (70935031 / 500000000) ≤ -Real.log (433867 / 500000) ∧
    -Real.log (433867 / 500000) ≤ (141870063 / 1000000000) := by
  have h := checkLog_sound (w := (66133 / 933867)) (n := 12)
    (lo := (70935031 / 500000000)) (hi := (141870063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 433867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 433867) = 1/(433867 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8696 : Bounds (-141870063 / 1000000000) (-70935031 / 500000000) (Real.log (433867 / 500000)) := by
  have h := reflection_log_8696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8697_neg : (62339601 / 500000000) ≤ -Real.log (200000 / 226557) ∧
    -Real.log (200000 / 226557) ≤ (124679203 / 1000000000) := by
  have h := checkLog_sound (w := (26557 / 426557)) (n := 12)
    (lo := (62339601 / 500000000)) (hi := (124679203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226557 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226557 / 200000) = 1/(200000 / 226557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8697 : Bounds (62339601 / 500000000) (124679203 / 1000000000) (Real.log (226557 / 200000)) := by
  have h := reflection_log_8697_neg
  have he : Real.log (226557 / 200000) = -Real.log (200000 / 226557) := by
    rw [show ((226557 / 200000) : ℝ) = ((200000 / 226557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8698_neg : (142468351 / 1000000000) ≤ -Real.log (173443 / 200000) ∧
    -Real.log (173443 / 200000) ≤ (556517 / 3906250) := by
  have h := checkLog_sound (w := (26557 / 373443)) (n := 12)
    (lo := (142468351 / 1000000000)) (hi := (556517 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173443) = 1/(173443 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8698 : Bounds (-556517 / 3906250) (-142468351 / 1000000000) (Real.log (173443 / 200000)) := by
  have h := reflection_log_8698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8699_neg : (17789149 / 1000000000) ≤ -Real.log (39294725751 / 40000000000) ∧
    -Real.log (39294725751 / 40000000000) ≤ (355783 / 20000000) := by
  have h := checkLog_sound (w := (705274249 / 79294725751)) (n := 12)
    (lo := (17789149 / 1000000000)) (hi := (355783 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39294725751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39294725751) = 1/(39294725751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8699 : Bounds (-355783 / 20000000) (-17789149 / 1000000000) (Real.log (39294725751 / 40000000000)) := by
  have h := reflection_log_8699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8700_neg : (2206141 / 125000000) ≤ -Real.log (245626426311 / 250000000000) ∧
    -Real.log (245626426311 / 250000000000) ≤ (17649129 / 1000000000) := by
  have h := checkLog_sound (w := (4373573689 / 495626426311)) (n := 12)
    (lo := (2206141 / 125000000)) (hi := (17649129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245626426311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245626426311) = 1/(245626426311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8700 : Bounds (-17649129 / 1000000000) (-2206141 / 125000000) (Real.log (245626426311 / 250000000000)) := by
  have h := reflection_log_8700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8701_neg : (266090997 / 1000000000) ≤ -Real.log (500000000000 / 652426895799) ∧
    -Real.log (500000000000 / 652426895799) ≤ (133045499 / 500000000) := by
  have h := checkLog_sound (w := (152426895799 / 1152426895799)) (n := 12)
    (lo := (266090997 / 1000000000)) (hi := (133045499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652426895799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652426895799 / 500000000000) = 1/(500000000000 / 652426895799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8701 : Bounds (266090997 / 1000000000) (133045499 / 500000000) (Real.log (652426895799 / 500000000000)) := by
  have h := reflection_log_8701_neg
  have he : Real.log (652426895799 / 500000000000) = -Real.log (500000000000 / 652426895799) := by
    rw [show ((652426895799 / 500000000000) : ℝ) = ((500000000000 / 652426895799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8702_neg : (267147553 / 1000000000) ≤ -Real.log (500000000000 / 653116585853) ∧
    -Real.log (500000000000 / 653116585853) ≤ (133573777 / 500000000) := by
  have h := checkLog_sound (w := (153116585853 / 1153116585853)) (n := 12)
    (lo := (267147553 / 1000000000)) (hi := (133573777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653116585853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653116585853 / 500000000000) = 1/(500000000000 / 653116585853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8702 : Bounds (267147553 / 1000000000) (133573777 / 500000000) (Real.log (653116585853 / 500000000000)) := by
  have h := reflection_log_8702_neg
  have he : Real.log (653116585853 / 500000000000) = -Real.log (500000000000 / 653116585853) := by
    rw [show ((653116585853 / 500000000000) : ℝ) = ((500000000000 / 653116585853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8703_neg : (267717833 / 500000000) ≤ -Real.log (20000000000 / 34163845633) ∧
    -Real.log (20000000000 / 34163845633) ≤ (535435667 / 1000000000) := by
  have h := checkLog_sound (w := (14163845633 / 54163845633)) (n := 12)
    (lo := (267717833 / 500000000)) (hi := (535435667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34163845633 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34163845633 / 20000000000) = 1/(20000000000 / 34163845633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8703 : Bounds (267717833 / 500000000) (535435667 / 1000000000) (Real.log (34163845633 / 20000000000)) := by
  have h := reflection_log_8703_neg
  have he : Real.log (34163845633 / 20000000000) = -Real.log (20000000000 / 34163845633) := by
    rw [show ((34163845633 / 20000000000) : ℝ) = ((20000000000 / 34163845633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
