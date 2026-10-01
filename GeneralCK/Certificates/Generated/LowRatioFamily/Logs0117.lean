import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7488_neg : (247180129 / 1000000000) ≤ -Real.log (781 / 1000) ∧
    -Real.log (781 / 1000) ≤ (24718013 / 100000000) := by
  have h := checkLog_sound (w := (219 / 1781)) (n := 12)
    (lo := (247180129 / 1000000000)) (hi := (24718013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 781) = 1/(781 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7488 : Bounds (-24718013 / 100000000) (-247180129 / 1000000000) (Real.log (781 / 1000)) := by
  have h := reflection_log_7488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7489_neg : (6843 / 31250000) ≤ -Real.log (1000000 / 1000219) ∧
    -Real.log (1000000 / 1000219) ≤ (218977 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 2000219)) (n := 12)
    (lo := (6843 / 31250000)) (hi := (218977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000219 / 1000000) = 1/(1000000 / 1000219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7489 : Bounds (6843 / 31250000) (218977 / 1000000000) (Real.log (1000219 / 1000000)) := by
  have h := reflection_log_7489_neg
  have he : Real.log (1000219 / 1000000) = -Real.log (1000000 / 1000219) := by
    rw [show ((1000219 / 1000000) : ℝ) = ((1000000 / 1000219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7490_neg : (219023 / 1000000000) ≤ -Real.log (999781 / 1000000) ∧
    -Real.log (999781 / 1000000) ≤ (13689 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1999781)) (n := 12)
    (lo := (219023 / 1000000000)) (hi := (13689 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999781) = 1/(999781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7490 : Bounds (-13689 / 62500000) (-219023 / 1000000000) (Real.log (999781 / 1000000)) := by
  have h := reflection_log_7490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7491_neg : (104445597 / 1000000000) ≤ -Real.log (200000 / 222019) ∧
    -Real.log (200000 / 222019) ≤ (52222799 / 500000000) := by
  have h := checkLog_sound (w := (22019 / 422019)) (n := 12)
    (lo := (104445597 / 1000000000)) (hi := (52222799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222019 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222019 / 200000) = 1/(200000 / 222019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7491 : Bounds (104445597 / 1000000000) (52222799 / 500000000) (Real.log (222019 / 200000)) := by
  have h := reflection_log_7491_neg
  have he : Real.log (222019 / 200000) = -Real.log (200000 / 222019) := by
    rw [show ((222019 / 200000) : ℝ) = ((200000 / 222019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7492_neg : (116640563 / 1000000000) ≤ -Real.log (177981 / 200000) ∧
    -Real.log (177981 / 200000) ≤ (29160141 / 250000000) := by
  have h := checkLog_sound (w := (22019 / 377981)) (n := 12)
    (lo := (116640563 / 1000000000)) (hi := (29160141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177981) = 1/(177981 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7492 : Bounds (-29160141 / 250000000) (-116640563 / 1000000000) (Real.log (177981 / 200000)) := by
  have h := reflection_log_7492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7493_neg : (104873397 / 1000000000) ≤ -Real.log (100000 / 111057) ∧
    -Real.log (100000 / 111057) ≤ (52436699 / 500000000) := by
  have h := checkLog_sound (w := (11057 / 211057)) (n := 12)
    (lo := (104873397 / 1000000000)) (hi := (52436699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111057 / 100000) = 1/(100000 / 111057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7493 : Bounds (104873397 / 1000000000) (52436699 / 500000000) (Real.log (111057 / 100000)) := by
  have h := reflection_log_7493_neg
  have he : Real.log (111057 / 100000) = -Real.log (100000 / 111057) := by
    rw [show ((111057 / 100000) : ℝ) = ((100000 / 111057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7494_neg : (11717447 / 100000000) ≤ -Real.log (88943 / 100000) ∧
    -Real.log (88943 / 100000) ≤ (117174471 / 1000000000) := by
  have h := checkLog_sound (w := (11057 / 188943)) (n := 12)
    (lo := (11717447 / 100000000)) (hi := (117174471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 88943) = 1/(88943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7494 : Bounds (-117174471 / 1000000000) (-11717447 / 100000000) (Real.log (88943 / 100000)) := by
  have h := reflection_log_7494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7495_neg : (12301073 / 1000000000) ≤ -Real.log (9877742751 / 10000000000) ∧
    -Real.log (9877742751 / 10000000000) ≤ (6150537 / 500000000) := by
  have h := checkLog_sound (w := (122257249 / 19877742751)) (n := 12)
    (lo := (12301073 / 1000000000)) (hi := (6150537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9877742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9877742751) = 1/(9877742751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7495 : Bounds (-6150537 / 500000000) (-12301073 / 1000000000) (Real.log (9877742751 / 10000000000)) := by
  have h := reflection_log_7495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7496_neg : (6097483 / 500000000) ≤ -Real.log (39515163639 / 40000000000) ∧
    -Real.log (39515163639 / 40000000000) ≤ (12194967 / 1000000000) := by
  have h := checkLog_sound (w := (484836361 / 79515163639)) (n := 12)
    (lo := (6097483 / 500000000)) (hi := (12194967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39515163639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39515163639) = 1/(39515163639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7496 : Bounds (-12194967 / 1000000000) (-6097483 / 500000000) (Real.log (39515163639 / 40000000000)) := by
  have h := reflection_log_7496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7497_neg : (2763577 / 12500000) ≤ -Real.log (500000000000 / 623715452773) ∧
    -Real.log (500000000000 / 623715452773) ≤ (221086161 / 1000000000) := by
  have h := checkLog_sound (w := (123715452773 / 1123715452773)) (n := 12)
    (lo := (2763577 / 12500000)) (hi := (221086161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623715452773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623715452773 / 500000000000) = 1/(500000000000 / 623715452773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7497 : Bounds (2763577 / 12500000) (221086161 / 1000000000) (Real.log (623715452773 / 500000000000)) := by
  have h := reflection_log_7497_neg
  have he : Real.log (623715452773 / 500000000000) = -Real.log (500000000000 / 623715452773) := by
    rw [show ((623715452773 / 500000000000) : ℝ) = ((500000000000 / 623715452773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7498_neg : (222047867 / 1000000000) ≤ -Real.log (15625000000 / 19509861653) ∧
    -Real.log (15625000000 / 19509861653) ≤ (55511967 / 250000000) := by
  have h := checkLog_sound (w := (3884861653 / 35134861653)) (n := 12)
    (lo := (222047867 / 1000000000)) (hi := (55511967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19509861653 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19509861653 / 15625000000) = 1/(15625000000 / 19509861653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7498 : Bounds (222047867 / 1000000000) (55511967 / 250000000) (Real.log (19509861653 / 15625000000)) := by
  have h := reflection_log_7498_neg
  have he : Real.log (19509861653 / 15625000000) = -Real.log (15625000000 / 19509861653) := by
    rw [show ((19509861653 / 15625000000) : ℝ) = ((15625000000 / 19509861653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7499_neg : (444160723 / 1000000000) ≤ -Real.log (50000000000 / 77959053103) ∧
    -Real.log (50000000000 / 77959053103) ≤ (111040181 / 250000000) := by
  have h := checkLog_sound (w := (27959053103 / 127959053103)) (n := 12)
    (lo := (444160723 / 1000000000)) (hi := (111040181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77959053103 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77959053103 / 50000000000) = 1/(50000000000 / 77959053103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7499 : Bounds (444160723 / 1000000000) (111040181 / 250000000) (Real.log (77959053103 / 50000000000)) := by
  have h := reflection_log_7499_neg
  have he : Real.log (77959053103 / 50000000000) = -Real.log (50000000000 / 77959053103) := by
    rw [show ((77959053103 / 50000000000) : ℝ) = ((50000000000 / 77959053103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7500_neg : (445210979 / 1000000000) ≤ -Real.log (250000000000 / 390204865557) ∧
    -Real.log (250000000000 / 390204865557) ≤ (22260549 / 50000000) := by
  have h := checkLog_sound (w := (140204865557 / 640204865557)) (n := 12)
    (lo := (445210979 / 1000000000)) (hi := (22260549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390204865557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390204865557 / 250000000000) = 1/(250000000000 / 390204865557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7500 : Bounds (445210979 / 1000000000) (22260549 / 50000000) (Real.log (390204865557 / 250000000000)) := by
  have h := reflection_log_7500_neg
  have he : Real.log (390204865557 / 250000000000) = -Real.log (250000000000 / 390204865557) := by
    rw [show ((390204865557 / 250000000000) : ℝ) = ((250000000000 / 390204865557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7501_neg : (99220469 / 500000000) ≤ -Real.log (2000 / 2439) ∧
    -Real.log (2000 / 2439) ≤ (198440939 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 4439)) (n := 12)
    (lo := (99220469 / 500000000)) (hi := (198440939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2439 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2439 / 2000) = 1/(2000 / 2439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7501 : Bounds (99220469 / 500000000) (198440939 / 1000000000) (Real.log (2439 / 2000)) := by
  have h := reflection_log_7501_neg
  have he : Real.log (2439 / 2000) = -Real.log (2000 / 2439) := by
    rw [show ((2439 / 2000) : ℝ) = ((2000 / 2439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7502_neg : (247820539 / 1000000000) ≤ -Real.log (1561 / 2000) ∧
    -Real.log (1561 / 2000) ≤ (12391027 / 50000000) := by
  have h := checkLog_sound (w := (439 / 3561)) (n := 12)
    (lo := (247820539 / 1000000000)) (hi := (12391027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1561) = 1/(1561 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7502 : Bounds (-12391027 / 50000000) (-247820539 / 1000000000) (Real.log (1561 / 2000)) := by
  have h := reflection_log_7502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7503_neg : (8779 / 40000000) ≤ -Real.log (2000000 / 2000439) ∧
    -Real.log (2000000 / 2000439) ≤ (54869 / 250000000) := by
  have h := checkLog_sound (w := (439 / 4000439)) (n := 12)
    (lo := (8779 / 40000000)) (hi := (54869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000439 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000439 / 2000000) = 1/(2000000 / 2000439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7503 : Bounds (8779 / 40000000) (54869 / 250000000) (Real.log (2000439 / 2000000)) := by
  have h := reflection_log_7503_neg
  have he : Real.log (2000439 / 2000000) = -Real.log (2000000 / 2000439) := by
    rw [show ((2000439 / 2000000) : ℝ) = ((2000000 / 2000439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7504_neg : (54881 / 250000000) ≤ -Real.log (1999561 / 2000000) ∧
    -Real.log (1999561 / 2000000) ≤ (8781 / 40000000) := by
  have h := checkLog_sound (w := (439 / 3999561)) (n := 12)
    (lo := (54881 / 250000000)) (hi := (8781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999561) = 1/(1999561 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7504 : Bounds (-8781 / 40000000) (-54881 / 250000000) (Real.log (1999561 / 2000000)) := by
  have h := reflection_log_7504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7505_neg : (52338541 / 500000000) ≤ -Real.log (62500 / 69397) ∧
    -Real.log (62500 / 69397) ≤ (104677083 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 131897)) (n := 12)
    (lo := (52338541 / 500000000)) (hi := (104677083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69397 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69397 / 62500) = 1/(62500 / 69397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7505 : Bounds (52338541 / 500000000) (104677083 / 1000000000) (Real.log (69397 / 62500)) := by
  have h := reflection_log_7505_neg
  have he : Real.log (69397 / 62500) = -Real.log (62500 / 69397) := by
    rw [show ((69397 / 62500) : ℝ) = ((62500 / 69397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7506_neg : (584647 / 5000000) ≤ -Real.log (55603 / 62500) ∧
    -Real.log (55603 / 62500) ≤ (116929401 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 118103)) (n := 12)
    (lo := (584647 / 5000000)) (hi := (116929401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55603) = 1/(55603 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7506 : Bounds (-116929401 / 1000000000) (-584647 / 5000000) (Real.log (55603 / 62500)) := by
  have h := reflection_log_7506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7507_neg : (52552391 / 500000000) ≤ -Real.log (1000000 / 1110827) ∧
    -Real.log (1000000 / 1110827) ≤ (105104783 / 1000000000) := by
  have h := checkLog_sound (w := (110827 / 2110827)) (n := 12)
    (lo := (52552391 / 500000000)) (hi := (105104783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1110827 / 1000000) = 1/(1000000 / 1110827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7507 : Bounds (52552391 / 500000000) (105104783 / 1000000000) (Real.log (1110827 / 1000000)) := by
  have h := reflection_log_7507_neg
  have he : Real.log (1110827 / 1000000) = -Real.log (1000000 / 1110827) := by
    rw [show ((1110827 / 1000000) : ℝ) = ((1000000 / 1110827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7508_neg : (117463461 / 1000000000) ≤ -Real.log (889173 / 1000000) ∧
    -Real.log (889173 / 1000000) ≤ (58731731 / 500000000) := by
  have h := checkLog_sound (w := (110827 / 1889173)) (n := 12)
    (lo := (117463461 / 1000000000)) (hi := (58731731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 889173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 889173) = 1/(889173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7508 : Bounds (-58731731 / 500000000) (-117463461 / 1000000000) (Real.log (889173 / 1000000)) := by
  have h := reflection_log_7508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7509_neg : (6179339 / 500000000) ≤ -Real.log (987717376071 / 1000000000000) ∧
    -Real.log (987717376071 / 1000000000000) ≤ (12358679 / 1000000000) := by
  have h := checkLog_sound (w := (12282623929 / 1987717376071)) (n := 12)
    (lo := (6179339 / 500000000)) (hi := (12358679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987717376071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987717376071) = 1/(987717376071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7509 : Bounds (-12358679 / 1000000000) (-6179339 / 500000000) (Real.log (987717376071 / 1000000000000)) := by
  have h := reflection_log_7509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7510_neg : (12252317 / 1000000000) ≤ -Real.log (3858681391 / 3906250000) ∧
    -Real.log (3858681391 / 3906250000) ≤ (6126159 / 500000000) := by
  have h := checkLog_sound (w := (47568609 / 7764931391)) (n := 12)
    (lo := (12252317 / 1000000000)) (hi := (6126159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858681391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858681391) = 1/(3858681391 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7510 : Bounds (-6126159 / 500000000) (-12252317 / 1000000000) (Real.log (3858681391 / 3906250000)) := by
  have h := reflection_log_7510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7511_neg : (110803241 / 500000000) ≤ -Real.log (25000000000 / 31202003489) ∧
    -Real.log (25000000000 / 31202003489) ≤ (221606483 / 1000000000) := by
  have h := checkLog_sound (w := (6202003489 / 56202003489)) (n := 12)
    (lo := (110803241 / 500000000)) (hi := (221606483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31202003489 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31202003489 / 25000000000) = 1/(25000000000 / 31202003489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7511 : Bounds (110803241 / 500000000) (221606483 / 1000000000) (Real.log (31202003489 / 25000000000)) := by
  have h := reflection_log_7511_neg
  have he : Real.log (31202003489 / 25000000000) = -Real.log (25000000000 / 31202003489) := by
    rw [show ((31202003489 / 25000000000) : ℝ) = ((25000000000 / 31202003489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7512_neg : (55642061 / 250000000) ≤ -Real.log (500000000000 / 624640536769) ∧
    -Real.log (500000000000 / 624640536769) ≤ (44513649 / 200000000) := by
  have h := checkLog_sound (w := (124640536769 / 1124640536769)) (n := 12)
    (lo := (55642061 / 250000000)) (hi := (44513649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624640536769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624640536769 / 500000000000) = 1/(500000000000 / 624640536769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7512 : Bounds (55642061 / 250000000) (44513649 / 200000000) (Real.log (624640536769 / 500000000000)) := by
  have h := reflection_log_7512_neg
  have he : Real.log (624640536769 / 500000000000) = -Real.log (500000000000 / 624640536769) := by
    rw [show ((624640536769 / 500000000000) : ℝ) = ((500000000000 / 624640536769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7513_neg : (445210979 / 1000000000) ≤ -Real.log (500000000000 / 780409731113) ∧
    -Real.log (500000000000 / 780409731113) ≤ (22260549 / 50000000) := by
  have h := checkLog_sound (w := (280409731113 / 1280409731113)) (n := 12)
    (lo := (445210979 / 1000000000)) (hi := (22260549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780409731113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780409731113 / 500000000000) = 1/(500000000000 / 780409731113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7513 : Bounds (445210979 / 1000000000) (22260549 / 50000000) (Real.log (780409731113 / 500000000000)) := by
  have h := reflection_log_7513_neg
  have he : Real.log (780409731113 / 500000000000) = -Real.log (500000000000 / 780409731113) := by
    rw [show ((780409731113 / 500000000000) : ℝ) = ((500000000000 / 780409731113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7514_neg : (446261477 / 1000000000) ≤ -Real.log (250000000000 / 390614990391) ∧
    -Real.log (250000000000 / 390614990391) ≤ (223130739 / 500000000) := by
  have h := checkLog_sound (w := (140614990391 / 640614990391)) (n := 12)
    (lo := (446261477 / 1000000000)) (hi := (223130739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390614990391 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390614990391 / 250000000000) = 1/(250000000000 / 390614990391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7514 : Bounds (446261477 / 1000000000) (223130739 / 500000000) (Real.log (390614990391 / 250000000000)) := by
  have h := reflection_log_7514_neg
  have he : Real.log (390614990391 / 250000000000) = -Real.log (250000000000 / 390614990391) := by
    rw [show ((390614990391 / 250000000000) : ℝ) = ((250000000000 / 390614990391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7515_neg : (99425429 / 500000000) ≤ -Real.log (50 / 61) ∧
    -Real.log (50 / 61) ≤ (198850859 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 111)) (n := 12)
    (lo := (99425429 / 500000000)) (hi := (198850859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 50) = 1/(50 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7515 : Bounds (99425429 / 500000000) (198850859 / 1000000000) (Real.log (61 / 50)) := by
  have h := reflection_log_7515_neg
  have he : Real.log (61 / 50) = -Real.log (50 / 61) := by
    rw [show ((61 / 50) : ℝ) = ((50 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7516_neg : (248461359 / 1000000000) ≤ -Real.log (39 / 50) ∧
    -Real.log (39 / 50) ≤ (3105767 / 12500000) := by
  have h := checkLog_sound (w := (11 / 89)) (n := 12)
    (lo := (248461359 / 1000000000)) (hi := (3105767 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 39) = 1/(39 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7516 : Bounds (-3105767 / 12500000) (-248461359 / 1000000000) (Real.log (39 / 50)) := by
  have h := reflection_log_7516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7517_neg : (8799 / 40000000) ≤ -Real.log (50000 / 50011) ∧
    -Real.log (50000 / 50011) ≤ (27497 / 125000000) := by
  have h := checkLog_sound (w := (11 / 100011)) (n := 12)
    (lo := (8799 / 40000000)) (hi := (27497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50011 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50011 / 50000) = 1/(50000 / 50011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7517 : Bounds (8799 / 40000000) (27497 / 125000000) (Real.log (50011 / 50000)) := by
  have h := reflection_log_7517_neg
  have he : Real.log (50011 / 50000) = -Real.log (50000 / 50011) := by
    rw [show ((50011 / 50000) : ℝ) = ((50000 / 50011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7518_neg : (27503 / 125000000) ≤ -Real.log (49989 / 50000) ∧
    -Real.log (49989 / 50000) ≤ (8801 / 40000000) := by
  have h := checkLog_sound (w := (11 / 99989)) (n := 12)
    (lo := (27503 / 125000000)) (hi := (8801 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49989) = 1/(49989 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7518 : Bounds (-8801 / 40000000) (-27503 / 125000000) (Real.log (49989 / 50000)) := by
  have h := reflection_log_7518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7519_neg : (104907613 / 1000000000) ≤ -Real.log (62500 / 69413) ∧
    -Real.log (62500 / 69413) ≤ (52453807 / 500000000) := by
  have h := checkLog_sound (w := (6913 / 131913)) (n := 12)
    (lo := (104907613 / 1000000000)) (hi := (52453807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69413 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69413 / 62500) = 1/(62500 / 69413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7519 : Bounds (104907613 / 1000000000) (52453807 / 500000000) (Real.log (69413 / 62500)) := by
  have h := reflection_log_7519_neg
  have he : Real.log (69413 / 62500) = -Real.log (62500 / 69413) := by
    rw [show ((69413 / 62500) : ℝ) = ((62500 / 69413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7520_neg : (23443439 / 200000000) ≤ -Real.log (55587 / 62500) ∧
    -Real.log (55587 / 62500) ≤ (29304299 / 250000000) := by
  have h := checkLog_sound (w := (6913 / 118087)) (n := 12)
    (lo := (23443439 / 200000000)) (hi := (29304299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55587) = 1/(55587 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7520 : Bounds (-29304299 / 250000000) (-23443439 / 200000000) (Real.log (55587 / 62500)) := by
  have h := reflection_log_7520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7521_neg : (21067223 / 200000000) ≤ -Real.log (250000 / 277771) ∧
    -Real.log (250000 / 277771) ≤ (26334029 / 250000000) := by
  have h := checkLog_sound (w := (27771 / 527771)) (n := 12)
    (lo := (21067223 / 200000000)) (hi := (26334029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277771 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277771 / 250000) = 1/(250000 / 277771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7521 : Bounds (21067223 / 200000000) (26334029 / 250000000) (Real.log (277771 / 250000)) := by
  have h := reflection_log_7521_neg
  have he : Real.log (277771 / 250000) = -Real.log (250000 / 277771) := by
    rw [show ((277771 / 250000) : ℝ) = ((250000 / 277771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7522_neg : (14719067 / 125000000) ≤ -Real.log (222229 / 250000) ∧
    -Real.log (222229 / 250000) ≤ (117752537 / 1000000000) := by
  have h := checkLog_sound (w := (27771 / 472229)) (n := 12)
    (lo := (14719067 / 125000000)) (hi := (117752537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 222229) = 1/(222229 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7522 : Bounds (-117752537 / 1000000000) (-14719067 / 125000000) (Real.log (222229 / 250000)) := by
  have h := reflection_log_7522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7523_neg : (620821 / 50000000) ≤ -Real.log (61728771559 / 62500000000) ∧
    -Real.log (61728771559 / 62500000000) ≤ (12416421 / 1000000000) := by
  have h := checkLog_sound (w := (771228441 / 124228771559)) (n := 12)
    (lo := (620821 / 50000000)) (hi := (12416421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61728771559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61728771559) = 1/(61728771559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7523 : Bounds (-12416421 / 1000000000) (-620821 / 50000000) (Real.log (61728771559 / 62500000000)) := by
  have h := reflection_log_7523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7524_neg : (6154791 / 500000000) ≤ -Real.log (3858460431 / 3906250000) ∧
    -Real.log (3858460431 / 3906250000) ≤ (12309583 / 1000000000) := by
  have h := checkLog_sound (w := (47789569 / 7764710431)) (n := 12)
    (lo := (6154791 / 500000000)) (hi := (12309583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858460431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858460431) = 1/(3858460431 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7524 : Bounds (-12309583 / 1000000000) (-6154791 / 500000000) (Real.log (3858460431 / 3906250000)) := by
  have h := reflection_log_7524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7525_neg : (27765601 / 125000000) ≤ -Real.log (125000000000 / 156090902549) ∧
    -Real.log (125000000000 / 156090902549) ≤ (222124809 / 1000000000) := by
  have h := checkLog_sound (w := (31090902549 / 281090902549)) (n := 12)
    (lo := (27765601 / 125000000)) (hi := (222124809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156090902549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156090902549 / 125000000000) = 1/(125000000000 / 156090902549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7525 : Bounds (27765601 / 125000000) (222124809 / 1000000000) (Real.log (156090902549 / 125000000000)) := by
  have h := reflection_log_7525_neg
  have he : Real.log (156090902549 / 125000000000) = -Real.log (125000000000 / 156090902549) := by
    rw [show ((156090902549 / 125000000000) : ℝ) = ((125000000000 / 156090902549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7526_neg : (223088651 / 1000000000) ≤ -Real.log (500000000000 / 624965688547) ∧
    -Real.log (500000000000 / 624965688547) ≤ (55772163 / 250000000) := by
  have h := checkLog_sound (w := (124965688547 / 1124965688547)) (n := 12)
    (lo := (223088651 / 1000000000)) (hi := (55772163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624965688547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624965688547 / 500000000000) = 1/(500000000000 / 624965688547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7526 : Bounds (223088651 / 1000000000) (55772163 / 250000000) (Real.log (624965688547 / 500000000000)) := by
  have h := reflection_log_7526_neg
  have he : Real.log (624965688547 / 500000000000) = -Real.log (500000000000 / 624965688547) := by
    rw [show ((624965688547 / 500000000000) : ℝ) = ((500000000000 / 624965688547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7527_neg : (446261477 / 1000000000) ≤ -Real.log (500000000000 / 781229980781) ∧
    -Real.log (500000000000 / 781229980781) ≤ (223130739 / 500000000) := by
  have h := checkLog_sound (w := (281229980781 / 1281229980781)) (n := 12)
    (lo := (446261477 / 1000000000)) (hi := (223130739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781229980781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781229980781 / 500000000000) = 1/(500000000000 / 781229980781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7527 : Bounds (446261477 / 1000000000) (223130739 / 500000000) (Real.log (781229980781 / 500000000000)) := by
  have h := reflection_log_7527_neg
  have he : Real.log (781229980781 / 500000000000) = -Real.log (500000000000 / 781229980781) := by
    rw [show ((781229980781 / 500000000000) : ℝ) = ((500000000000 / 781229980781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7528_neg : (223656109 / 500000000) ≤ -Real.log (125000000000 / 195512820513) ∧
    -Real.log (125000000000 / 195512820513) ≤ (447312219 / 1000000000) := by
  have h := checkLog_sound (w := (70512820513 / 320512820513)) (n := 12)
    (lo := (223656109 / 500000000)) (hi := (447312219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195512820513 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195512820513 / 125000000000) = 1/(125000000000 / 195512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7528 : Bounds (223656109 / 500000000) (447312219 / 1000000000) (Real.log (195512820513 / 125000000000)) := by
  have h := reflection_log_7528_neg
  have he : Real.log (195512820513 / 125000000000) = -Real.log (125000000000 / 195512820513) := by
    rw [show ((195512820513 / 125000000000) : ℝ) = ((125000000000 / 195512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7529_neg : (19926061 / 100000000) ≤ -Real.log (2000 / 2441) ∧
    -Real.log (2000 / 2441) ≤ (199260611 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 4441)) (n := 12)
    (lo := (19926061 / 100000000)) (hi := (199260611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2441 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2441 / 2000) = 1/(2000 / 2441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7529 : Bounds (19926061 / 100000000) (199260611 / 1000000000) (Real.log (2441 / 2000)) := by
  have h := reflection_log_7529_neg
  have he : Real.log (2441 / 2000) = -Real.log (2000 / 2441) := by
    rw [show ((2441 / 2000) : ℝ) = ((2000 / 2441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7530_neg : (24910259 / 100000000) ≤ -Real.log (1559 / 2000) ∧
    -Real.log (1559 / 2000) ≤ (249102591 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 3559)) (n := 12)
    (lo := (24910259 / 100000000)) (hi := (249102591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1559) = 1/(1559 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7530 : Bounds (-249102591 / 1000000000) (-24910259 / 100000000) (Real.log (1559 / 2000)) := by
  have h := reflection_log_7530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7531_neg : (8819 / 40000000) ≤ -Real.log (2000000 / 2000441) ∧
    -Real.log (2000000 / 2000441) ≤ (55119 / 250000000) := by
  have h := checkLog_sound (w := (441 / 4000441)) (n := 12)
    (lo := (8819 / 40000000)) (hi := (55119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000441 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000441 / 2000000) = 1/(2000000 / 2000441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7531 : Bounds (8819 / 40000000) (55119 / 250000000) (Real.log (2000441 / 2000000)) := by
  have h := reflection_log_7531_neg
  have he : Real.log (2000441 / 2000000) = -Real.log (2000000 / 2000441) := by
    rw [show ((2000441 / 2000000) : ℝ) = ((2000000 / 2000441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7532_neg : (55131 / 250000000) ≤ -Real.log (1999559 / 2000000) ∧
    -Real.log (1999559 / 2000000) ≤ (8821 / 40000000) := by
  have h := checkLog_sound (w := (441 / 3999559)) (n := 12)
    (lo := (55131 / 250000000)) (hi := (8821 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999559) = 1/(1999559 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7532 : Bounds (-8821 / 40000000) (-55131 / 250000000) (Real.log (1999559 / 2000000)) := by
  have h := reflection_log_7532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7533_neg : (10513809 / 100000000) ≤ -Real.log (62500 / 69429) ∧
    -Real.log (62500 / 69429) ≤ (105138091 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 131929)) (n := 12)
    (lo := (10513809 / 100000000)) (hi := (105138091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69429 / 62500) = 1/(62500 / 69429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7533 : Bounds (10513809 / 100000000) (105138091 / 1000000000) (Real.log (69429 / 62500)) := by
  have h := reflection_log_7533_neg
  have he : Real.log (69429 / 62500) = -Real.log (62500 / 69429) := by
    rw [show ((69429 / 62500) : ℝ) = ((62500 / 69429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7534_neg : (58752537 / 500000000) ≤ -Real.log (55571 / 62500) ∧
    -Real.log (55571 / 62500) ≤ (4700203 / 40000000) := by
  have h := checkLog_sound (w := (6929 / 118071)) (n := 12)
    (lo := (58752537 / 500000000)) (hi := (4700203 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55571) = 1/(55571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7534 : Bounds (-4700203 / 40000000) (-58752537 / 500000000) (Real.log (55571 / 62500)) := by
  have h := reflection_log_7534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7535_neg : (52783247 / 500000000) ≤ -Real.log (50000 / 55567) ∧
    -Real.log (50000 / 55567) ≤ (21113299 / 200000000) := by
  have h := checkLog_sound (w := (5567 / 105567)) (n := 12)
    (lo := (52783247 / 500000000)) (hi := (21113299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55567 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55567 / 50000) = 1/(50000 / 55567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7535 : Bounds (52783247 / 500000000) (21113299 / 200000000) (Real.log (55567 / 50000)) := by
  have h := reflection_log_7535_neg
  have he : Real.log (55567 / 50000) = -Real.log (50000 / 55567) := by
    rw [show ((55567 / 50000) : ℝ) = ((50000 / 55567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7536_neg : (14755071 / 125000000) ≤ -Real.log (44433 / 50000) ∧
    -Real.log (44433 / 50000) ≤ (118040569 / 1000000000) := by
  have h := checkLog_sound (w := (5567 / 94433)) (n := 12)
    (lo := (14755071 / 125000000)) (hi := (118040569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44433) = 1/(44433 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7536 : Bounds (-118040569 / 1000000000) (-14755071 / 125000000) (Real.log (44433 / 50000)) := by
  have h := reflection_log_7536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7537_neg : (6237037 / 500000000) ≤ -Real.log (2469008511 / 2500000000) ∧
    -Real.log (2469008511 / 2500000000) ≤ (498963 / 40000000) := by
  have h := checkLog_sound (w := (30991489 / 4969008511)) (n := 12)
    (lo := (6237037 / 500000000)) (hi := (498963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2469008511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2469008511) = 1/(2469008511 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7537 : Bounds (-498963 / 40000000) (-6237037 / 500000000) (Real.log (2469008511 / 2500000000)) := by
  have h := reflection_log_7537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7538_neg : (12366983 / 1000000000) ≤ -Real.log (3858238959 / 3906250000) ∧
    -Real.log (3858238959 / 3906250000) ≤ (1545873 / 125000000) := by
  have h := checkLog_sound (w := (48011041 / 7764488959)) (n := 12)
    (lo := (12366983 / 1000000000)) (hi := (1545873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3858238959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3858238959) = 1/(3858238959 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7538 : Bounds (-1545873 / 125000000) (-12366983 / 1000000000) (Real.log (3858238959 / 3906250000)) := by
  have h := reflection_log_7538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7539_neg : (44528633 / 200000000) ≤ -Real.log (12500000000 / 15617183423) ∧
    -Real.log (12500000000 / 15617183423) ≤ (111321583 / 500000000) := by
  have h := checkLog_sound (w := (3117183423 / 28117183423)) (n := 12)
    (lo := (44528633 / 200000000)) (hi := (111321583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15617183423 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15617183423 / 12500000000) = 1/(12500000000 / 15617183423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7539 : Bounds (44528633 / 200000000) (111321583 / 500000000) (Real.log (15617183423 / 12500000000)) := by
  have h := reflection_log_7539_neg
  have he : Real.log (15617183423 / 12500000000) = -Real.log (12500000000 / 15617183423) := by
    rw [show ((15617183423 / 12500000000) : ℝ) = ((12500000000 / 15617183423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7540_neg : (223607063 / 1000000000) ≤ -Real.log (250000000000 / 312644881057) ∧
    -Real.log (250000000000 / 312644881057) ≤ (27950883 / 125000000) := by
  have h := checkLog_sound (w := (62644881057 / 562644881057)) (n := 12)
    (lo := (223607063 / 1000000000)) (hi := (27950883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312644881057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312644881057 / 250000000000) = 1/(250000000000 / 312644881057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7540 : Bounds (223607063 / 1000000000) (27950883 / 125000000) (Real.log (312644881057 / 250000000000)) := by
  have h := reflection_log_7540_neg
  have he : Real.log (312644881057 / 250000000000) = -Real.log (250000000000 / 312644881057) := by
    rw [show ((312644881057 / 250000000000) : ℝ) = ((250000000000 / 312644881057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7541_neg : (223656109 / 500000000) ≤ -Real.log (500000000000 / 782051282051) ∧
    -Real.log (500000000000 / 782051282051) ≤ (447312219 / 1000000000) := by
  have h := checkLog_sound (w := (282051282051 / 1282051282051)) (n := 12)
    (lo := (223656109 / 500000000)) (hi := (447312219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782051282051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782051282051 / 500000000000) = 1/(500000000000 / 782051282051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7541 : Bounds (223656109 / 500000000) (447312219 / 1000000000) (Real.log (782051282051 / 500000000000)) := by
  have h := reflection_log_7541_neg
  have he : Real.log (782051282051 / 500000000000) = -Real.log (500000000000 / 782051282051) := by
    rw [show ((782051282051 / 500000000000) : ℝ) = ((500000000000 / 782051282051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7542_neg : (448363201 / 1000000000) ≤ -Real.log (500000000000 / 782873636947) ∧
    -Real.log (500000000000 / 782873636947) ≤ (224181601 / 500000000) := by
  have h := checkLog_sound (w := (282873636947 / 1282873636947)) (n := 12)
    (lo := (448363201 / 1000000000)) (hi := (224181601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782873636947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782873636947 / 500000000000) = 1/(500000000000 / 782873636947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7542 : Bounds (448363201 / 1000000000) (224181601 / 500000000) (Real.log (782873636947 / 500000000000)) := by
  have h := reflection_log_7542_neg
  have he : Real.log (782873636947 / 500000000000) = -Real.log (500000000000 / 782873636947) := by
    rw [show ((782873636947 / 500000000000) : ℝ) = ((500000000000 / 782873636947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7543_neg : (39934039 / 200000000) ≤ -Real.log (1000 / 1221) ∧
    -Real.log (1000 / 1221) ≤ (49917549 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2221)) (n := 12)
    (lo := (39934039 / 200000000)) (hi := (49917549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221 / 1000) = 1/(1000 / 1221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7543 : Bounds (39934039 / 200000000) (49917549 / 250000000) (Real.log (1221 / 1000)) := by
  have h := reflection_log_7543_neg
  have he : Real.log (1221 / 1000) = -Real.log (1000 / 1221) := by
    rw [show ((1221 / 1000) : ℝ) = ((1000 / 1221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7544_neg : (249744233 / 1000000000) ≤ -Real.log (779 / 1000) ∧
    -Real.log (779 / 1000) ≤ (124872117 / 500000000) := by
  have h := checkLog_sound (w := (221 / 1779)) (n := 12)
    (lo := (249744233 / 1000000000)) (hi := (124872117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 779) = 1/(779 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7544 : Bounds (-124872117 / 500000000) (-249744233 / 1000000000) (Real.log (779 / 1000)) := by
  have h := reflection_log_7544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7545_neg : (8839 / 40000000) ≤ -Real.log (1000000 / 1000221) ∧
    -Real.log (1000000 / 1000221) ≤ (13811 / 62500000) := by
  have h := checkLog_sound (w := (221 / 2000221)) (n := 12)
    (lo := (8839 / 40000000)) (hi := (13811 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000221 / 1000000) = 1/(1000000 / 1000221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7545 : Bounds (8839 / 40000000) (13811 / 62500000) (Real.log (1000221 / 1000000)) := by
  have h := reflection_log_7545_neg
  have he : Real.log (1000221 / 1000000) = -Real.log (1000000 / 1000221) := by
    rw [show ((1000221 / 1000000) : ℝ) = ((1000000 / 1000221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7546_neg : (6907 / 31250000) ≤ -Real.log (999779 / 1000000) ∧
    -Real.log (999779 / 1000000) ≤ (8841 / 40000000) := by
  have h := checkLog_sound (w := (221 / 1999779)) (n := 12)
    (lo := (6907 / 31250000)) (hi := (8841 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999779) = 1/(999779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7546 : Bounds (-8841 / 40000000) (-6907 / 31250000) (Real.log (999779 / 1000000)) := by
  have h := reflection_log_7546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7547_neg : (21073883 / 200000000) ≤ -Real.log (1000000 / 1111121) ∧
    -Real.log (1000000 / 1111121) ≤ (13171177 / 125000000) := by
  have h := checkLog_sound (w := (111121 / 2111121)) (n := 12)
    (lo := (21073883 / 200000000)) (hi := (13171177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111121 / 1000000) = 1/(1000000 / 1111121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7547 : Bounds (21073883 / 200000000) (13171177 / 125000000) (Real.log (1111121 / 1000000)) := by
  have h := reflection_log_7547_neg
  have he : Real.log (1111121 / 1000000) = -Real.log (1000000 / 1111121) := by
    rw [show ((1111121 / 1000000) : ℝ) = ((1000000 / 1111121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7548_neg : (1472427 / 12500000) ≤ -Real.log (888879 / 1000000) ∧
    -Real.log (888879 / 1000000) ≤ (117794161 / 1000000000) := by
  have h := checkLog_sound (w := (111121 / 1888879)) (n := 12)
    (lo := (1472427 / 12500000)) (hi := (117794161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888879) = 1/(888879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7548 : Bounds (-117794161 / 1000000000) (-1472427 / 12500000) (Real.log (888879 / 1000000)) := by
  have h := reflection_log_7548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7549_neg : (2644943 / 25000000) ≤ -Real.log (1000000 / 1111597) ∧
    -Real.log (1000000 / 1111597) ≤ (105797721 / 1000000000) := by
  have h := checkLog_sound (w := (111597 / 2111597)) (n := 12)
    (lo := (2644943 / 25000000)) (hi := (105797721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1111597 / 1000000) = 1/(1000000 / 1111597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7549 : Bounds (2644943 / 25000000) (105797721 / 1000000000) (Real.log (1111597 / 1000000)) := by
  have h := reflection_log_7549_neg
  have he : Real.log (1111597 / 1000000) = -Real.log (1000000 / 1111597) := by
    rw [show ((1111597 / 1000000) : ℝ) = ((1000000 / 1111597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7550_neg : (11832981 / 100000000) ≤ -Real.log (888403 / 1000000) ∧
    -Real.log (888403 / 1000000) ≤ (118329811 / 1000000000) := by
  have h := checkLog_sound (w := (111597 / 1888403)) (n := 12)
    (lo := (11832981 / 100000000)) (hi := (118329811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 888403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 888403) = 1/(888403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7550 : Bounds (-118329811 / 1000000000) (-11832981 / 100000000) (Real.log (888403 / 1000000)) := by
  have h := reflection_log_7550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7551_neg : (1253209 / 100000000) ≤ -Real.log (987546109591 / 1000000000000) ∧
    -Real.log (987546109591 / 1000000000000) ≤ (12532091 / 1000000000) := by
  have h := checkLog_sound (w := (12453890409 / 1987546109591)) (n := 12)
    (lo := (1253209 / 100000000)) (hi := (12532091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987546109591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987546109591) = 1/(987546109591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7551 : Bounds (-12532091 / 1000000000) (-1253209 / 100000000) (Real.log (987546109591 / 1000000000000)) := by
  have h := reflection_log_7551_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
