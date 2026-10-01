import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11648_neg : (87219 / 200000000) ≤ -Real.log (249891 / 250000) ∧
    -Real.log (249891 / 250000) ≤ (3407 / 7812500) := by
  have h := checkLog_sound (w := (109 / 499891)) (n := 12)
    (lo := (87219 / 200000000)) (hi := (3407 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249891) = 1/(249891 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11648 : Bounds (-3407 / 7812500) (-87219 / 200000000) (Real.log (249891 / 250000)) := by
  have h := reflection_log_11648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11649_neg : (203071447 / 1000000000) ≤ -Real.log (25000 / 30629) ∧
    -Real.log (25000 / 30629) ≤ (25383931 / 125000000) := by
  have h := checkLog_sound (w := (5629 / 55629)) (n := 12)
    (lo := (203071447 / 1000000000)) (hi := (25383931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30629 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30629 / 25000) = 1/(25000 / 30629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11649 : Bounds (203071447 / 1000000000) (25383931 / 125000000) (Real.log (30629 / 25000)) := by
  have h := reflection_log_11649_neg
  have he : Real.log (30629 / 25000) = -Real.log (25000 / 30629) := by
    rw [show ((30629 / 25000) : ℝ) = ((25000 / 30629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11650_neg : (127549361 / 500000000) ≤ -Real.log (19371 / 25000) ∧
    -Real.log (19371 / 25000) ≤ (255098723 / 1000000000) := by
  have h := checkLog_sound (w := (5629 / 44371)) (n := 12)
    (lo := (127549361 / 500000000)) (hi := (255098723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19371) = 1/(19371 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11650 : Bounds (-255098723 / 1000000000) (-127549361 / 500000000) (Real.log (19371 / 25000)) := by
  have h := reflection_log_11650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11651_neg : (203867761 / 1000000000) ≤ -Real.log (125000 / 153267) ∧
    -Real.log (125000 / 153267) ≤ (101933881 / 500000000) := by
  have h := checkLog_sound (w := (28267 / 278267)) (n := 12)
    (lo := (203867761 / 1000000000)) (hi := (101933881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153267 / 125000) = 1/(125000 / 153267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11651 : Bounds (203867761 / 1000000000) (101933881 / 500000000) (Real.log (153267 / 125000)) := by
  have h := reflection_log_11651_neg
  have he : Real.log (153267 / 125000) = -Real.log (125000 / 153267) := by
    rw [show ((153267 / 125000) : ℝ) = ((125000 / 153267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11652_neg : (256359131 / 1000000000) ≤ -Real.log (96733 / 125000) ∧
    -Real.log (96733 / 125000) ≤ (64089783 / 250000000) := by
  have h := checkLog_sound (w := (28267 / 221733)) (n := 12)
    (lo := (256359131 / 1000000000)) (hi := (64089783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96733) = 1/(96733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11652 : Bounds (-64089783 / 250000000) (-256359131 / 1000000000) (Real.log (96733 / 125000)) := by
  have h := reflection_log_11652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11653_neg : (5249137 / 100000000) ≤ -Real.log (14825976711 / 15625000000) ∧
    -Real.log (14825976711 / 15625000000) ≤ (52491371 / 1000000000) := by
  have h := checkLog_sound (w := (799023289 / 30450976711)) (n := 12)
    (lo := (5249137 / 100000000)) (hi := (52491371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14825976711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14825976711) = 1/(14825976711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11653 : Bounds (-52491371 / 1000000000) (-5249137 / 100000000) (Real.log (14825976711 / 15625000000)) := by
  have h := reflection_log_11653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11654_neg : (26013637 / 500000000) ≤ -Real.log (593314359 / 625000000) ∧
    -Real.log (593314359 / 625000000) ≤ (2081091 / 40000000) := by
  have h := checkLog_sound (w := (31685641 / 1218314359)) (n := 12)
    (lo := (26013637 / 500000000)) (hi := (2081091 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 593314359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 593314359) = 1/(593314359 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11654 : Bounds (-2081091 / 40000000) (-26013637 / 500000000) (Real.log (593314359 / 625000000)) := by
  have h := reflection_log_11654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11655_neg : (45817017 / 100000000) ≤ -Real.log (50000000000 / 79058902483) ∧
    -Real.log (50000000000 / 79058902483) ≤ (458170171 / 1000000000) := by
  have h := checkLog_sound (w := (29058902483 / 129058902483)) (n := 12)
    (lo := (45817017 / 100000000)) (hi := (458170171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79058902483 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79058902483 / 50000000000) = 1/(50000000000 / 79058902483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11655 : Bounds (45817017 / 100000000) (458170171 / 1000000000) (Real.log (79058902483 / 50000000000)) := by
  have h := reflection_log_11655_neg
  have he : Real.log (79058902483 / 50000000000) = -Real.log (50000000000 / 79058902483) := by
    rw [show ((79058902483 / 50000000000) : ℝ) = ((50000000000 / 79058902483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11656_neg : (115056723 / 250000000) ≤ -Real.log (500000000000 / 792216720251) ∧
    -Real.log (500000000000 / 792216720251) ≤ (460226893 / 1000000000) := by
  have h := checkLog_sound (w := (292216720251 / 1292216720251)) (n := 12)
    (lo := (115056723 / 250000000)) (hi := (460226893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792216720251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792216720251 / 500000000000) = 1/(500000000000 / 792216720251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11656 : Bounds (115056723 / 250000000) (460226893 / 1000000000) (Real.log (792216720251 / 500000000000)) := by
  have h := reflection_log_11656_neg
  have he : Real.log (792216720251 / 500000000000) = -Real.log (500000000000 / 792216720251) := by
    rw [show ((792216720251 / 500000000000) : ℝ) = ((500000000000 / 792216720251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11657_neg : (233023599 / 250000000) ≤ -Real.log (62500000000 / 158738938053) ∧
    -Real.log (62500000000 / 158738938053) ≤ (466047199 / 500000000) := by
  have h := checkLog_sound (w := (33738938053 / 283738938053)) (n := 12)
    (lo := (14934201 / 62500000)) (hi := (238947217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158738938053 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158738938053 / 125000000000) = 1/(62500000000 / 158738938053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11657 : Bounds (233023599 / 250000000) (466047199 / 500000000) (Real.log (158738938053 / 62500000000)) := by
  have h := reflection_log_11657_neg
  have he : Real.log (158738938053 / 62500000000) = -Real.log (62500000000 / 158738938053) := by
    rw [show ((158738938053 / 62500000000) : ℝ) = ((62500000000 / 158738938053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11658_neg : (934562497 / 1000000000) ≤ -Real.log (500000000000 / 1273049645391) ∧
    -Real.log (500000000000 / 1273049645391) ≤ (934562499 / 1000000000) := by
  have h := checkLog_sound (w := (273049645391 / 2273049645391)) (n := 12)
    (lo := (241415317 / 1000000000)) (hi := (120707659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273049645391 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1273049645391 / 1000000000000) = 1/(500000000000 / 1273049645391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11658 : Bounds (934562497 / 1000000000) (934562499 / 1000000000) (Real.log (1273049645391 / 500000000000)) := by
  have h := reflection_log_11658_neg
  have he : Real.log (1273049645391 / 500000000000) = -Real.log (500000000000 / 1273049645391) := by
    rw [show ((1273049645391 / 500000000000) : ℝ) = ((500000000000 / 1273049645391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11659_neg : (362557607 / 1000000000) ≤ -Real.log (1000 / 1437) ∧
    -Real.log (1000 / 1437) ≤ (45319701 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2437)) (n := 12)
    (lo := (362557607 / 1000000000)) (hi := (45319701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1437 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1437 / 1000) = 1/(1000 / 1437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11659 : Bounds (362557607 / 1000000000) (45319701 / 125000000) (Real.log (1437 / 1000)) := by
  have h := reflection_log_11659_neg
  have he : Real.log (1437 / 1000) = -Real.log (1000 / 1437) := by
    rw [show ((1437 / 1000) : ℝ) = ((1000 / 1437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11660_neg : (11489513 / 20000000) ≤ -Real.log (563 / 1000) ∧
    -Real.log (563 / 1000) ≤ (574475651 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 1563)) (n := 12)
    (lo := (11489513 / 20000000)) (hi := (574475651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 563) = 1/(563 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11660 : Bounds (-574475651 / 1000000000) (-11489513 / 20000000) (Real.log (563 / 1000)) := by
  have h := reflection_log_11660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11661_neg : (54613 / 125000000) ≤ -Real.log (1000000 / 1000437) ∧
    -Real.log (1000000 / 1000437) ≤ (87381 / 200000000) := by
  have h := checkLog_sound (w := (437 / 2000437)) (n := 12)
    (lo := (54613 / 125000000)) (hi := (87381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000437 / 1000000) = 1/(1000000 / 1000437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11661 : Bounds (54613 / 125000000) (87381 / 200000000) (Real.log (1000437 / 1000000)) := by
  have h := reflection_log_11661_neg
  have he : Real.log (1000437 / 1000000) = -Real.log (1000000 / 1000437) := by
    rw [show ((1000437 / 1000000) : ℝ) = ((1000000 / 1000437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11662_neg : (87419 / 200000000) ≤ -Real.log (999563 / 1000000) ∧
    -Real.log (999563 / 1000000) ≤ (54637 / 125000000) := by
  have h := checkLog_sound (w := (437 / 1999563)) (n := 12)
    (lo := (87419 / 200000000)) (hi := (54637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999563) = 1/(999563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11662 : Bounds (-54637 / 125000000) (-87419 / 200000000) (Real.log (999563 / 1000000)) := by
  have h := reflection_log_11662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11663_neg : (203525163 / 1000000000) ≤ -Real.log (250000 / 306429) ∧
    -Real.log (250000 / 306429) ≤ (50881291 / 250000000) := by
  have h := checkLog_sound (w := (56429 / 556429)) (n := 12)
    (lo := (203525163 / 1000000000)) (hi := (50881291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306429 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306429 / 250000) = 1/(250000 / 306429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11663 : Bounds (203525163 / 1000000000) (50881291 / 250000000) (Real.log (306429 / 250000)) := by
  have h := reflection_log_11663_neg
  have he : Real.log (306429 / 250000) = -Real.log (250000 / 306429) := by
    rw [show ((306429 / 250000) : ℝ) = ((250000 / 306429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11664_neg : (255816547 / 1000000000) ≤ -Real.log (193571 / 250000) ∧
    -Real.log (193571 / 250000) ≤ (63954137 / 250000000) := by
  have h := checkLog_sound (w := (56429 / 443571)) (n := 12)
    (lo := (255816547 / 1000000000)) (hi := (63954137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193571) = 1/(193571 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11664 : Bounds (-63954137 / 250000000) (-255816547 / 1000000000) (Real.log (193571 / 250000)) := by
  have h := reflection_log_11664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11665_neg : (40864549 / 200000000) ≤ -Real.log (500000 / 613347) ∧
    -Real.log (500000 / 613347) ≤ (102161373 / 500000000) := by
  have h := checkLog_sound (w := (113347 / 1113347)) (n := 12)
    (lo := (40864549 / 200000000)) (hi := (102161373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613347 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613347 / 500000) = 1/(500000 / 613347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11665 : Bounds (40864549 / 200000000) (102161373 / 500000000) (Real.log (613347 / 500000)) := by
  have h := reflection_log_11665_neg
  have he : Real.log (613347 / 500000) = -Real.log (500000 / 613347) := by
    rw [show ((613347 / 500000) : ℝ) = ((500000 / 613347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11666_neg : (2008441 / 7812500) ≤ -Real.log (386653 / 500000) ∧
    -Real.log (386653 / 500000) ≤ (257080449 / 1000000000) := by
  have h := checkLog_sound (w := (113347 / 886653)) (n := 12)
    (lo := (2008441 / 7812500)) (hi := (257080449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386653) = 1/(386653 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11666 : Bounds (-257080449 / 1000000000) (-2008441 / 7812500) (Real.log (386653 / 500000)) := by
  have h := reflection_log_11666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11667_neg : (26378851 / 500000000) ≤ -Real.log (237152457591 / 250000000000) ∧
    -Real.log (237152457591 / 250000000000) ≤ (52757703 / 1000000000) := by
  have h := checkLog_sound (w := (12847542409 / 487152457591)) (n := 12)
    (lo := (26378851 / 500000000)) (hi := (52757703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237152457591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237152457591) = 1/(237152457591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11667 : Bounds (-52757703 / 1000000000) (-26378851 / 500000000) (Real.log (237152457591 / 250000000000)) := by
  have h := reflection_log_11667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11668_neg : (6536423 / 125000000) ≤ -Real.log (59315767959 / 62500000000) ∧
    -Real.log (59315767959 / 62500000000) ≤ (10458277 / 200000000) := by
  have h := checkLog_sound (w := (3184232041 / 121815767959)) (n := 12)
    (lo := (6536423 / 125000000)) (hi := (10458277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59315767959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59315767959) = 1/(59315767959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11668 : Bounds (-10458277 / 200000000) (-6536423 / 125000000) (Real.log (59315767959 / 62500000000)) := by
  have h := reflection_log_11668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11669_neg : (45934171 / 100000000) ≤ -Real.log (500000000000 / 791515774573) ∧
    -Real.log (500000000000 / 791515774573) ≤ (459341711 / 1000000000) := by
  have h := checkLog_sound (w := (291515774573 / 1291515774573)) (n := 12)
    (lo := (45934171 / 100000000)) (hi := (459341711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791515774573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791515774573 / 500000000000) = 1/(500000000000 / 791515774573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11669 : Bounds (45934171 / 100000000) (459341711 / 1000000000) (Real.log (791515774573 / 500000000000)) := by
  have h := reflection_log_11669_neg
  have he : Real.log (791515774573 / 500000000000) = -Real.log (500000000000 / 791515774573) := by
    rw [show ((791515774573 / 500000000000) : ℝ) = ((500000000000 / 791515774573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11670_neg : (230701597 / 500000000) ≤ -Real.log (50000000000 / 79314915441) ∧
    -Real.log (50000000000 / 79314915441) ≤ (92280639 / 200000000) := by
  have h := checkLog_sound (w := (29314915441 / 129314915441)) (n := 12)
    (lo := (230701597 / 500000000)) (hi := (92280639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79314915441 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79314915441 / 50000000000) = 1/(50000000000 / 79314915441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11670 : Bounds (230701597 / 500000000) (92280639 / 200000000) (Real.log (79314915441 / 50000000000)) := by
  have h := reflection_log_11670_neg
  have he : Real.log (79314915441 / 50000000000) = -Real.log (50000000000 / 79314915441) := by
    rw [show ((79314915441 / 50000000000) : ℝ) = ((50000000000 / 79314915441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11671_neg : (934562497 / 1000000000) ≤ -Real.log (50000000000 / 127304964539) ∧
    -Real.log (50000000000 / 127304964539) ≤ (934562499 / 1000000000) := by
  have h := checkLog_sound (w := (27304964539 / 227304964539)) (n := 12)
    (lo := (241415317 / 1000000000)) (hi := (120707659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127304964539 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(127304964539 / 100000000000) = 1/(50000000000 / 127304964539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11671 : Bounds (934562497 / 1000000000) (934562499 / 1000000000) (Real.log (127304964539 / 50000000000)) := by
  have h := reflection_log_11671_neg
  have he : Real.log (127304964539 / 50000000000) = -Real.log (50000000000 / 127304964539) := by
    rw [show ((127304964539 / 50000000000) : ℝ) = ((50000000000 / 127304964539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11672_neg : (937033257 / 1000000000) ≤ -Real.log (500000000000 / 1276198934281) ∧
    -Real.log (500000000000 / 1276198934281) ≤ (937033259 / 1000000000) := by
  have h := checkLog_sound (w := (276198934281 / 2276198934281)) (n := 12)
    (lo := (243886077 / 1000000000)) (hi := (121943039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276198934281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1276198934281 / 1000000000000) = 1/(500000000000 / 1276198934281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11672 : Bounds (937033257 / 1000000000) (937033259 / 1000000000) (Real.log (1276198934281 / 500000000000)) := by
  have h := reflection_log_11672_neg
  have he : Real.log (1276198934281 / 500000000000) = -Real.log (500000000000 / 1276198934281) := by
    rw [show ((1276198934281 / 500000000000) : ℝ) = ((500000000000 / 1276198934281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11673_neg : (363253259 / 1000000000) ≤ -Real.log (500 / 719) ∧
    -Real.log (500 / 719) ≤ (18162663 / 50000000) := by
  have h := checkLog_sound (w := (219 / 1219)) (n := 12)
    (lo := (363253259 / 1000000000)) (hi := (18162663 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719 / 500) = 1/(500 / 719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11673 : Bounds (363253259 / 1000000000) (18162663 / 50000000) (Real.log (719 / 500)) := by
  have h := reflection_log_11673_neg
  have he : Real.log (719 / 500) = -Real.log (500 / 719) := by
    rw [show ((719 / 500) : ℝ) = ((500 / 719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11674_neg : (576253429 / 1000000000) ≤ -Real.log (281 / 500) ∧
    -Real.log (281 / 500) ≤ (57625343 / 100000000) := by
  have h := checkLog_sound (w := (219 / 781)) (n := 12)
    (lo := (576253429 / 1000000000)) (hi := (57625343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 281) = 1/(281 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11674 : Bounds (-57625343 / 100000000) (-576253429 / 1000000000) (Real.log (281 / 500)) := by
  have h := reflection_log_11674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11675_neg : (27369 / 62500000) ≤ -Real.log (500000 / 500219) ∧
    -Real.log (500000 / 500219) ≤ (87581 / 200000000) := by
  have h := checkLog_sound (w := (219 / 1000219)) (n := 12)
    (lo := (27369 / 62500000)) (hi := (87581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500219 / 500000) = 1/(500000 / 500219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11675 : Bounds (27369 / 62500000) (87581 / 200000000) (Real.log (500219 / 500000)) := by
  have h := reflection_log_11675_neg
  have he : Real.log (500219 / 500000) = -Real.log (500000 / 500219) := by
    rw [show ((500219 / 500000) : ℝ) = ((500000 / 500219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11676_neg : (87619 / 200000000) ≤ -Real.log (499781 / 500000) ∧
    -Real.log (499781 / 500000) ≤ (27381 / 62500000) := by
  have h := checkLog_sound (w := (219 / 999781)) (n := 12)
    (lo := (87619 / 200000000)) (hi := (27381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499781) = 1/(499781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11676 : Bounds (-27381 / 62500000) (-87619 / 200000000) (Real.log (499781 / 500000)) := by
  have h := reflection_log_11676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11677_neg : (6374359 / 31250000) ≤ -Real.log (1000000 / 1226273) ∧
    -Real.log (1000000 / 1226273) ≤ (203979489 / 1000000000) := by
  have h := checkLog_sound (w := (226273 / 2226273)) (n := 12)
    (lo := (6374359 / 31250000)) (hi := (203979489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226273 / 1000000) = 1/(1000000 / 1226273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11677 : Bounds (6374359 / 31250000) (203979489 / 1000000000) (Real.log (1226273 / 1000000)) := by
  have h := reflection_log_11677_neg
  have he : Real.log (1226273 / 1000000) = -Real.log (1000000 / 1226273) := by
    rw [show ((1226273 / 1000000) : ℝ) = ((1000000 / 1226273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11678_neg : (12826809 / 50000000) ≤ -Real.log (773727 / 1000000) ∧
    -Real.log (773727 / 1000000) ≤ (256536181 / 1000000000) := by
  have h := checkLog_sound (w := (226273 / 1773727)) (n := 12)
    (lo := (12826809 / 50000000)) (hi := (256536181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773727) = 1/(773727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11678 : Bounds (-256536181 / 1000000000) (-12826809 / 50000000) (Real.log (773727 / 1000000)) := by
  have h := reflection_log_11678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11679_neg : (51194177 / 250000000) ≤ -Real.log (1000000 / 1227251) ∧
    -Real.log (1000000 / 1227251) ≤ (204776709 / 1000000000) := by
  have h := checkLog_sound (w := (227251 / 2227251)) (n := 12)
    (lo := (51194177 / 250000000)) (hi := (204776709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227251 / 1000000) = 1/(1000000 / 1227251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11679 : Bounds (51194177 / 250000000) (204776709 / 1000000000) (Real.log (1227251 / 1000000)) := by
  have h := reflection_log_11679_neg
  have he : Real.log (1227251 / 1000000) = -Real.log (1000000 / 1227251) := by
    rw [show ((1227251 / 1000000) : ℝ) = ((1000000 / 1227251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11680_neg : (8056281 / 31250000) ≤ -Real.log (772749 / 1000000) ∧
    -Real.log (772749 / 1000000) ≤ (257800993 / 1000000000) := by
  have h := checkLog_sound (w := (227251 / 1772749)) (n := 12)
    (lo := (8056281 / 31250000)) (hi := (257800993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772749) = 1/(772749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11680 : Bounds (-257800993 / 1000000000) (-8056281 / 31250000) (Real.log (772749 / 1000000)) := by
  have h := reflection_log_11680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11681_neg : (53024283 / 1000000000) ≤ -Real.log (948356982999 / 1000000000000) ∧
    -Real.log (948356982999 / 1000000000000) ≤ (13256071 / 250000000) := by
  have h := checkLog_sound (w := (51643017001 / 1948356982999)) (n := 12)
    (lo := (53024283 / 1000000000)) (hi := (13256071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948356982999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948356982999) = 1/(948356982999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11681 : Bounds (-13256071 / 250000000) (-53024283 / 1000000000) (Real.log (948356982999 / 1000000000000)) := by
  have h := reflection_log_11681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11682_neg : (13139173 / 250000000) ≤ -Real.log (948800529471 / 1000000000000) ∧
    -Real.log (948800529471 / 1000000000000) ≤ (52556693 / 1000000000) := by
  have h := checkLog_sound (w := (51199470529 / 1948800529471)) (n := 12)
    (lo := (13139173 / 250000000)) (hi := (52556693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948800529471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948800529471) = 1/(948800529471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11682 : Bounds (-52556693 / 1000000000) (-13139173 / 250000000) (Real.log (948800529471 / 1000000000000)) := by
  have h := reflection_log_11682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11683_neg : (115128917 / 250000000) ≤ -Real.log (125000000000 / 198111381663) ∧
    -Real.log (125000000000 / 198111381663) ≤ (460515669 / 1000000000) := by
  have h := checkLog_sound (w := (73111381663 / 323111381663)) (n := 12)
    (lo := (115128917 / 250000000)) (hi := (460515669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198111381663 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198111381663 / 125000000000) = 1/(125000000000 / 198111381663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11683 : Bounds (115128917 / 250000000) (460515669 / 1000000000) (Real.log (198111381663 / 125000000000)) := by
  have h := reflection_log_11683_neg
  have he : Real.log (198111381663 / 125000000000) = -Real.log (125000000000 / 198111381663) := by
    rw [show ((198111381663 / 125000000000) : ℝ) = ((125000000000 / 198111381663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11684_neg : (4625777 / 10000000) ≤ -Real.log (500000000000 / 794081260539) ∧
    -Real.log (500000000000 / 794081260539) ≤ (462577701 / 1000000000) := by
  have h := checkLog_sound (w := (294081260539 / 1294081260539)) (n := 12)
    (lo := (4625777 / 10000000)) (hi := (462577701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794081260539 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794081260539 / 500000000000) = 1/(500000000000 / 794081260539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11684 : Bounds (4625777 / 10000000) (462577701 / 1000000000) (Real.log (794081260539 / 500000000000)) := by
  have h := reflection_log_11684_neg
  have he : Real.log (794081260539 / 500000000000) = -Real.log (500000000000 / 794081260539) := by
    rw [show ((794081260539 / 500000000000) : ℝ) = ((500000000000 / 794081260539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11685_neg : (937033257 / 1000000000) ≤ -Real.log (12500000000 / 31904973357) ∧
    -Real.log (12500000000 / 31904973357) ≤ (937033259 / 1000000000) := by
  have h := checkLog_sound (w := (6904973357 / 56904973357)) (n := 12)
    (lo := (243886077 / 1000000000)) (hi := (121943039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31904973357 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31904973357 / 25000000000) = 1/(12500000000 / 31904973357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11685 : Bounds (937033257 / 1000000000) (937033259 / 1000000000) (Real.log (31904973357 / 12500000000)) := by
  have h := reflection_log_11685_neg
  have he : Real.log (31904973357 / 12500000000) = -Real.log (12500000000 / 31904973357) := by
    rw [show ((31904973357 / 12500000000) : ℝ) = ((12500000000 / 31904973357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11686_neg : (939506687 / 1000000000) ≤ -Real.log (100000000000 / 255871886121) ∧
    -Real.log (100000000000 / 255871886121) ≤ (939506689 / 1000000000) := by
  have h := checkLog_sound (w := (55871886121 / 455871886121)) (n := 12)
    (lo := (246359507 / 1000000000)) (hi := (61589877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255871886121 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(255871886121 / 200000000000) = 1/(100000000000 / 255871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11686 : Bounds (939506687 / 1000000000) (939506689 / 1000000000) (Real.log (255871886121 / 100000000000)) := by
  have h := reflection_log_11686_neg
  have he : Real.log (255871886121 / 100000000000) = -Real.log (100000000000 / 255871886121) := by
    rw [show ((255871886121 / 100000000000) : ℝ) = ((100000000000 / 255871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11687_neg : (363948427 / 1000000000) ≤ -Real.log (1000 / 1439) ∧
    -Real.log (1000 / 1439) ≤ (90987107 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2439)) (n := 12)
    (lo := (363948427 / 1000000000)) (hi := (90987107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1000) = 1/(1000 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11687 : Bounds (363948427 / 1000000000) (90987107 / 250000000) (Real.log (1439 / 1000)) := by
  have h := reflection_log_11687_neg
  have he : Real.log (1439 / 1000) = -Real.log (1000 / 1439) := by
    rw [show ((1439 / 1000) : ℝ) = ((1000 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11688_neg : (578034373 / 1000000000) ≤ -Real.log (561 / 1000) ∧
    -Real.log (561 / 1000) ≤ (289017187 / 500000000) := by
  have h := checkLog_sound (w := (439 / 1561)) (n := 12)
    (lo := (578034373 / 1000000000)) (hi := (289017187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 561) = 1/(561 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11688 : Bounds (-289017187 / 500000000) (-578034373 / 1000000000) (Real.log (561 / 1000)) := by
  have h := reflection_log_11688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11689_neg : (438903 / 1000000000) ≤ -Real.log (1000000 / 1000439) ∧
    -Real.log (1000000 / 1000439) ≤ (54863 / 125000000) := by
  have h := checkLog_sound (w := (439 / 2000439)) (n := 12)
    (lo := (438903 / 1000000000)) (hi := (54863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000439 / 1000000) = 1/(1000000 / 1000439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11689 : Bounds (438903 / 1000000000) (54863 / 125000000) (Real.log (1000439 / 1000000)) := by
  have h := reflection_log_11689_neg
  have he : Real.log (1000439 / 1000000) = -Real.log (1000000 / 1000439) := by
    rw [show ((1000439 / 1000000) : ℝ) = ((1000000 / 1000439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11690_neg : (54887 / 125000000) ≤ -Real.log (999561 / 1000000) ∧
    -Real.log (999561 / 1000000) ≤ (439097 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1999561)) (n := 12)
    (lo := (54887 / 125000000)) (hi := (439097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999561) = 1/(999561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11690 : Bounds (-439097 / 1000000000) (-54887 / 125000000) (Real.log (999561 / 1000000)) := by
  have h := reflection_log_11690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11691_neg : (204432791 / 1000000000) ≤ -Real.log (1000000 / 1226829) ∧
    -Real.log (1000000 / 1226829) ≤ (25554099 / 125000000) := by
  have h := checkLog_sound (w := (226829 / 2226829)) (n := 12)
    (lo := (204432791 / 1000000000)) (hi := (25554099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226829 / 1000000) = 1/(1000000 / 1226829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11691 : Bounds (204432791 / 1000000000) (25554099 / 125000000) (Real.log (1226829 / 1000000)) := by
  have h := reflection_log_11691_neg
  have he : Real.log (1226829 / 1000000) = -Real.log (1000000 / 1226829) := by
    rw [show ((1226829 / 1000000) : ℝ) = ((1000000 / 1226829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11692_neg : (128627519 / 500000000) ≤ -Real.log (773171 / 1000000) ∧
    -Real.log (773171 / 1000000) ≤ (257255039 / 1000000000) := by
  have h := checkLog_sound (w := (226829 / 1773171)) (n := 12)
    (lo := (128627519 / 500000000)) (hi := (257255039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773171) = 1/(773171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11692 : Bounds (-257255039 / 1000000000) (-128627519 / 500000000) (Real.log (773171 / 1000000)) := by
  have h := reflection_log_11692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11693_neg : (2565391 / 12500000) ≤ -Real.log (1000000 / 1227809) ∧
    -Real.log (1000000 / 1227809) ≤ (205231281 / 1000000000) := by
  have h := checkLog_sound (w := (227809 / 2227809)) (n := 12)
    (lo := (2565391 / 12500000)) (hi := (205231281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227809 / 1000000) = 1/(1000000 / 1227809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11693 : Bounds (2565391 / 12500000) (205231281 / 1000000000) (Real.log (1227809 / 1000000)) := by
  have h := reflection_log_11693_neg
  have he : Real.log (1227809 / 1000000) = -Real.log (1000000 / 1227809) := by
    rw [show ((1227809 / 1000000) : ℝ) = ((1000000 / 1227809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11694_neg : (5170467 / 20000000) ≤ -Real.log (772191 / 1000000) ∧
    -Real.log (772191 / 1000000) ≤ (258523351 / 1000000000) := by
  have h := checkLog_sound (w := (227809 / 1772191)) (n := 12)
    (lo := (5170467 / 20000000)) (hi := (258523351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772191) = 1/(772191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11694 : Bounds (-258523351 / 1000000000) (-5170467 / 20000000) (Real.log (772191 / 1000000)) := by
  have h := reflection_log_11694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11695_neg : (5329207 / 100000000) ≤ -Real.log (948103059519 / 1000000000000) ∧
    -Real.log (948103059519 / 1000000000000) ≤ (53292071 / 1000000000) := by
  have h := checkLog_sound (w := (51896940481 / 1948103059519)) (n := 12)
    (lo := (5329207 / 100000000)) (hi := (53292071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948103059519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948103059519) = 1/(948103059519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11695 : Bounds (-53292071 / 1000000000) (-5329207 / 100000000) (Real.log (948103059519 / 1000000000000)) := by
  have h := reflection_log_11695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11696_neg : (52822247 / 1000000000) ≤ -Real.log (948548604759 / 1000000000000) ∧
    -Real.log (948548604759 / 1000000000000) ≤ (6602781 / 125000000) := by
  have h := checkLog_sound (w := (51451395241 / 1948548604759)) (n := 12)
    (lo := (52822247 / 1000000000)) (hi := (6602781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 948548604759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 948548604759) = 1/(948548604759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11696 : Bounds (-6602781 / 125000000) (-52822247 / 1000000000) (Real.log (948548604759 / 1000000000000)) := by
  have h := reflection_log_11696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11697_neg : (46168783 / 100000000) ≤ -Real.log (125000000000 / 198343736379) ∧
    -Real.log (125000000000 / 198343736379) ≤ (461687831 / 1000000000) := by
  have h := checkLog_sound (w := (73343736379 / 323343736379)) (n := 12)
    (lo := (46168783 / 100000000)) (hi := (461687831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198343736379 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198343736379 / 125000000000) = 1/(125000000000 / 198343736379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11697 : Bounds (46168783 / 100000000) (461687831 / 1000000000) (Real.log (198343736379 / 125000000000)) := by
  have h := reflection_log_11697_neg
  have he : Real.log (198343736379 / 125000000000) = -Real.log (125000000000 / 198343736379) := by
    rw [show ((198343736379 / 125000000000) : ℝ) = ((125000000000 / 198343736379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11698_neg : (46375463 / 100000000) ≤ -Real.log (500000000000 / 795016388433) ∧
    -Real.log (500000000000 / 795016388433) ≤ (463754631 / 1000000000) := by
  have h := checkLog_sound (w := (295016388433 / 1295016388433)) (n := 12)
    (lo := (46375463 / 100000000)) (hi := (463754631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795016388433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795016388433 / 500000000000) = 1/(500000000000 / 795016388433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11698 : Bounds (46375463 / 100000000) (463754631 / 1000000000) (Real.log (795016388433 / 500000000000)) := by
  have h := reflection_log_11698_neg
  have he : Real.log (795016388433 / 500000000000) = -Real.log (500000000000 / 795016388433) := by
    rw [show ((795016388433 / 500000000000) : ℝ) = ((500000000000 / 795016388433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11699_neg : (939506687 / 1000000000) ≤ -Real.log (125000000000 / 319839857651) ∧
    -Real.log (125000000000 / 319839857651) ≤ (939506689 / 1000000000) := by
  have h := checkLog_sound (w := (69839857651 / 569839857651)) (n := 12)
    (lo := (246359507 / 1000000000)) (hi := (61589877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319839857651 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(319839857651 / 250000000000) = 1/(125000000000 / 319839857651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11699 : Bounds (939506687 / 1000000000) (939506689 / 1000000000) (Real.log (319839857651 / 125000000000)) := by
  have h := reflection_log_11699_neg
  have he : Real.log (319839857651 / 125000000000) = -Real.log (125000000000 / 319839857651) := by
    rw [show ((319839857651 / 125000000000) : ℝ) = ((125000000000 / 319839857651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11700_neg : (2354957 / 2500000) ≤ -Real.log (62500000000 / 160316399287) ∧
    -Real.log (62500000000 / 160316399287) ≤ (470991401 / 500000000) := by
  have h := checkLog_sound (w := (35316399287 / 285316399287)) (n := 12)
    (lo := (12441781 / 50000000)) (hi := (248835621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160316399287 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160316399287 / 125000000000) = 1/(62500000000 / 160316399287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11700 : Bounds (2354957 / 2500000) (470991401 / 500000000) (Real.log (160316399287 / 62500000000)) := by
  have h := reflection_log_11700_neg
  have he : Real.log (160316399287 / 62500000000) = -Real.log (62500000000 / 160316399287) := by
    rw [show ((160316399287 / 62500000000) : ℝ) = ((62500000000 / 160316399287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11701_neg : (364643113 / 1000000000) ≤ -Real.log (25 / 36) ∧
    -Real.log (25 / 36) ≤ (182321557 / 500000000) := by
  have h := checkLog_sound (w := (11 / 61)) (n := 12)
    (lo := (364643113 / 1000000000)) (hi := (182321557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36 / 25) = 1/(25 / 36) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11701 : Bounds (364643113 / 1000000000) (182321557 / 500000000) (Real.log (36 / 25)) := by
  have h := reflection_log_11701_neg
  have he : Real.log (36 / 25) = -Real.log (25 / 36) := by
    rw [show ((36 / 25) : ℝ) = ((25 / 36) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11702_neg : (115963699 / 200000000) ≤ -Real.log (14 / 25) ∧
    -Real.log (14 / 25) ≤ (1132458 / 1953125) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 14) = 1/(14 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11702 : Bounds (-1132458 / 1953125) (-115963699 / 200000000) (Real.log (14 / 25)) := by
  have h := reflection_log_11702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11703_neg : (439903 / 1000000000) ≤ -Real.log (25000 / 25011) ∧
    -Real.log (25000 / 25011) ≤ (13747 / 31250000) := by
  have h := checkLog_sound (w := (11 / 50011)) (n := 12)
    (lo := (439903 / 1000000000)) (hi := (13747 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25011 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25011 / 25000) = 1/(25000 / 25011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11703 : Bounds (439903 / 1000000000) (13747 / 31250000) (Real.log (25011 / 25000)) := by
  have h := reflection_log_11703_neg
  have he : Real.log (25011 / 25000) = -Real.log (25000 / 25011) := by
    rw [show ((25011 / 25000) : ℝ) = ((25000 / 25011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11704_neg : (13753 / 31250000) ≤ -Real.log (24989 / 25000) ∧
    -Real.log (24989 / 25000) ≤ (440097 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 49989)) (n := 12)
    (lo := (13753 / 31250000)) (hi := (440097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24989) = 1/(24989 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11704 : Bounds (-440097 / 1000000000) (-13753 / 31250000) (Real.log (24989 / 25000)) := by
  have h := reflection_log_11704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11705_neg : (12805419 / 62500000) ≤ -Real.log (500000 / 613693) ∧
    -Real.log (500000 / 613693) ≤ (40977341 / 200000000) := by
  have h := checkLog_sound (w := (113693 / 1113693)) (n := 12)
    (lo := (12805419 / 62500000)) (hi := (40977341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613693 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613693 / 500000) = 1/(500000 / 613693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11705 : Bounds (12805419 / 62500000) (40977341 / 200000000) (Real.log (613693 / 500000)) := by
  have h := reflection_log_11705_neg
  have he : Real.log (613693 / 500000) = -Real.log (500000 / 613693) := by
    rw [show ((613693 / 500000) : ℝ) = ((500000 / 613693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11706_neg : (64493927 / 250000000) ≤ -Real.log (386307 / 500000) ∧
    -Real.log (386307 / 500000) ≤ (257975709 / 1000000000) := by
  have h := checkLog_sound (w := (113693 / 886307)) (n := 12)
    (lo := (64493927 / 250000000)) (hi := (257975709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386307) = 1/(386307 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11706 : Bounds (-257975709 / 1000000000) (-64493927 / 250000000) (Real.log (386307 / 500000)) := by
  have h := reflection_log_11706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11707_neg : (205686459 / 1000000000) ≤ -Real.log (62500 / 76773) ∧
    -Real.log (62500 / 76773) ≤ (10284323 / 50000000) := by
  have h := checkLog_sound (w := (14273 / 139273)) (n := 12)
    (lo := (205686459 / 1000000000)) (hi := (10284323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76773 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76773 / 62500) = 1/(62500 / 76773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11707 : Bounds (205686459 / 1000000000) (10284323 / 50000000) (Real.log (76773 / 62500)) := by
  have h := reflection_log_11707_neg
  have he : Real.log (76773 / 62500) = -Real.log (62500 / 76773) := by
    rw [show ((76773 / 62500) : ℝ) = ((62500 / 76773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11708_neg : (129623763 / 500000000) ≤ -Real.log (48227 / 62500) ∧
    -Real.log (48227 / 62500) ≤ (259247527 / 1000000000) := by
  have h := checkLog_sound (w := (14273 / 110727)) (n := 12)
    (lo := (129623763 / 500000000)) (hi := (259247527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48227) = 1/(48227 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11708 : Bounds (-259247527 / 1000000000) (-129623763 / 500000000) (Real.log (48227 / 62500)) := by
  have h := reflection_log_11708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11709_neg : (53561067 / 1000000000) ≤ -Real.log (3702531471 / 3906250000) ∧
    -Real.log (3702531471 / 3906250000) ≤ (13390267 / 250000000) := by
  have h := checkLog_sound (w := (203718529 / 7608781471)) (n := 12)
    (lo := (53561067 / 1000000000)) (hi := (13390267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3702531471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3702531471) = 1/(3702531471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11709 : Bounds (-13390267 / 250000000) (-53561067 / 1000000000) (Real.log (3702531471 / 3906250000)) := by
  have h := reflection_log_11709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11710_neg : (53089003 / 1000000000) ≤ -Real.log (237073901751 / 250000000000) ∧
    -Real.log (237073901751 / 250000000000) ≤ (13272251 / 250000000) := by
  have h := checkLog_sound (w := (12926098249 / 487073901751)) (n := 12)
    (lo := (53089003 / 1000000000)) (hi := (13272251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237073901751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237073901751) = 1/(237073901751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11710 : Bounds (-13272251 / 250000000) (-53089003 / 1000000000) (Real.log (237073901751 / 250000000000)) := by
  have h := reflection_log_11710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11711_neg : (115715603 / 250000000) ≤ -Real.log (500000000000 / 794307377293) ∧
    -Real.log (500000000000 / 794307377293) ≤ (462862413 / 1000000000) := by
  have h := checkLog_sound (w := (294307377293 / 1294307377293)) (n := 12)
    (lo := (115715603 / 250000000)) (hi := (462862413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794307377293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794307377293 / 500000000000) = 1/(500000000000 / 794307377293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11711 : Bounds (115715603 / 250000000) (462862413 / 1000000000) (Real.log (794307377293 / 500000000000)) := by
  have h := reflection_log_11711_neg
  have he : Real.log (794307377293 / 500000000000) = -Real.log (500000000000 / 794307377293) := by
    rw [show ((794307377293 / 500000000000) : ℝ) = ((500000000000 / 794307377293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
