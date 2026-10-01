import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0006
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

theorem reflection_log_1_neg : (682815673 / 1000000000) ≤ -Real.log (20480 / 40539) ∧
    -Real.log (20480 / 40539) ≤ (341407837 / 500000000) := by
  have h := checkLog_sound (w := (20059 / 61019)) (n := 12)
    (lo := (682815673 / 1000000000)) (hi := (341407837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40539 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40539 / 20480) = 1/(20480 / 40539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682815673 / 1000000000) (341407837 / 500000000) (Real.log (40539 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40539 / 20480) = -Real.log (20480 / 40539) := by
    rw [show ((40539 / 20480) : ℝ) = ((20480 / 40539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1942285621 / 500000000) ≤ -Real.log (421 / 20480) ∧
    -Real.log (421 / 20480) ≤ (242785703 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 421) = 1/(421 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242785703 / 62500000) (-1942285621 / 500000000) (Real.log (421 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170692201 / 250000000) ≤ -Real.log (1000000000000 / 1979350585937) ∧
    -Real.log (1000000000000 / 1979350585937) ≤ (136553761 / 200000000) := by
  have h := checkLog_sound (w := (979350585937 / 2979350585937)) (n := 12)
    (lo := (170692201 / 250000000)) (hi := (136553761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979350585937 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979350585937 / 1000000000000) = 1/(1000000000000 / 1979350585937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170692201 / 250000000) (136553761 / 200000000) (Real.log (1979350585937 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1979350585937 / 1000000000000) = -Real.log (1000000000000 / 1979350585937) := by
    rw [show ((1979350585937 / 1000000000000) : ℝ) = ((1000000000000 / 1979350585937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3880068331 / 1000000000) ≤ -Real.log (20649414063 / 1000000000000) ∧
    -Real.log (20649414063 / 1000000000000) ≤ (3880068337 / 1000000000) := by
  have h := checkLog_sound (w := (10600585937 / 51899414063)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20649414063) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20649414063) = 1/(20649414063 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3880068337 / 1000000000) (-3880068331 / 1000000000) (Real.log (20649414063 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672376311 / 1000000000) ≤ -Real.log (10240 / 20059) ∧
    -Real.log (10240 / 20059) ≤ (84047039 / 125000000) := by
  have h := checkLog_sound (w := (9819 / 30299)) (n := 12)
    (lo := (672376311 / 1000000000)) (hi := (84047039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20059 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20059 / 10240) = 1/(10240 / 20059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672376311 / 1000000000) (84047039 / 125000000) (Real.log (20059 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (20059 / 10240) = -Real.log (10240 / 20059) := by
    rw [show ((20059 / 10240) : ℝ) = ((10240 / 20059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1595712031 / 500000000) ≤ -Real.log (421 / 10240) ∧
    -Real.log (421 / 10240) ≤ (3191424067 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 421) = 1/(421 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3191424067 / 1000000000) (-1595712031 / 500000000) (Real.log (421 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (336140793 / 500000000) ≤ -Real.log (102400 / 200571) ∧
    -Real.log (102400 / 200571) ≤ (672281587 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 302971)) (n := 12)
    (lo := (336140793 / 500000000)) (hi := (672281587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200571 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200571 / 102400) = 1/(102400 / 200571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (336140793 / 500000000) (672281587 / 1000000000) (Real.log (200571 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200571 / 102400) = -Real.log (102400 / 200571) := by
    rw [show ((200571 / 102400) : ℝ) = ((102400 / 200571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3186921151 / 1000000000) ≤ -Real.log (4229 / 102400) ∧
    -Real.log (4229 / 102400) ≤ (796730289 / 250000000) := by
  have h := checkLog_sound (w := (2171 / 10629)) (n := 12)
    (lo := (414332431 / 1000000000)) (hi := (25895777 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4229) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4229) = 1/(4229 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-796730289 / 250000000) (-3186921151 / 1000000000) (Real.log (4229 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4277103 / 6250000) ≤ -Real.log (125000 / 247807) ∧
    -Real.log (125000 / 247807) ≤ (684336481 / 1000000000) := by
  have h := checkLog_sound (w := (122807 / 372807)) (n := 12)
    (lo := (4277103 / 6250000)) (hi := (684336481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247807 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247807 / 125000) = 1/(125000 / 247807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4277103 / 6250000) (684336481 / 1000000000) (Real.log (247807 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247807 / 125000) = -Real.log (125000 / 247807) := by
    rw [show ((247807 / 125000) : ℝ) = ((125000 / 247807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (808608653 / 200000000) ≤ -Real.log (2193 / 125000) ∧
    -Real.log (2193 / 125000) ≤ (4043043271 / 1000000000) := by
  have h := checkLog_sound (w := (6853 / 24397)) (n := 12)
    (lo := (115461473 / 200000000)) (hi := (288653683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8772) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8772) = 1/(2193 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4043043271 / 1000000000) (-808608653 / 200000000) (Real.log (2193 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17109383 / 25000000) ≤ -Real.log (1000000 / 1982533) ∧
    -Real.log (1000000 / 1982533) ≤ (684375321 / 1000000000) := by
  have h := checkLog_sound (w := (982533 / 2982533)) (n := 12)
    (lo := (17109383 / 25000000)) (hi := (684375321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982533 / 1000000) = 1/(1000000 / 1982533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17109383 / 25000000) (684375321 / 1000000000) (Real.log (1982533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982533 / 1000000) = -Real.log (1000000 / 1982533) := by
    rw [show ((1982533 / 1000000) : ℝ) = ((1000000 / 1982533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4047441889 / 1000000000) ≤ -Real.log (17467 / 1000000) ∧
    -Real.log (17467 / 1000000) ≤ (809488379 / 200000000) := by
  have h := checkLog_sound (w := (13783 / 48717)) (n := 12)
    (lo := (581705989 / 1000000000)) (hi := (58170599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17467) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17467) = 1/(17467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-809488379 / 200000000) (-4047441889 / 1000000000) (Real.log (17467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684303187 / 1000000000) ≤ -Real.log (100000 / 198239) ∧
    -Real.log (100000 / 198239) ≤ (171075797 / 250000000) := by
  have h := checkLog_sound (w := (98239 / 298239)) (n := 12)
    (lo := (684303187 / 1000000000)) (hi := (171075797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198239 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198239 / 100000) = 1/(100000 / 198239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684303187 / 1000000000) (171075797 / 250000000) (Real.log (198239 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (198239 / 100000) = -Real.log (100000 / 198239) := by
    rw [show ((198239 / 100000) : ℝ) = ((100000 / 198239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4039288353 / 1000000000) ≤ -Real.log (1761 / 100000) ∧
    -Real.log (1761 / 100000) ≤ (4039288359 / 1000000000) := by
  have h := checkLog_sound (w := (682 / 2443)) (n := 12)
    (lo := (573552453 / 1000000000)) (hi := (286776227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1761) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1761) = 1/(1761 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4039288359 / 1000000000) (-4039288353 / 1000000000) (Real.log (1761 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (171085507 / 250000000) ≤ -Real.log (1000000 / 1982467) ∧
    -Real.log (1000000 / 1982467) ≤ (684342029 / 1000000000) := by
  have h := checkLog_sound (w := (982467 / 2982467)) (n := 12)
    (lo := (171085507 / 250000000)) (hi := (684342029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982467 / 1000000) = 1/(1000000 / 1982467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (171085507 / 250000000) (684342029 / 1000000000) (Real.log (1982467 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982467 / 1000000) = -Real.log (1000000 / 1982467) := by
    rw [show ((1982467 / 1000000) : ℝ) = ((1000000 / 1982467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (505458807 / 125000000) ≤ -Real.log (17533 / 1000000) ∧
    -Real.log (17533 / 1000000) ≤ (2021835231 / 500000000) := by
  have h := checkLog_sound (w := (13717 / 48783)) (n := 12)
    (lo := (144483639 / 250000000)) (hi := (577934557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17533) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17533) = 1/(17533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2021835231 / 500000000) (-505458807 / 125000000) (Real.log (17533 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (147730617 / 31250000) ≤ -Real.log (500000000000 / 56499544003647) ∧
    -Real.log (500000000000 / 56499544003647) ≤ (4727379751 / 1000000000) := by
  have h := checkLog_sound (w := (24499544003647 / 88499544003647)) (n := 12)
    (lo := (71062083 / 125000000)) (hi := (113699333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56499544003647 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56499544003647 / 32000000000000) = 1/(500000000000 / 56499544003647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (147730617 / 31250000) (4727379751 / 1000000000) (Real.log (56499544003647 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (56499544003647 / 500000000000) = -Real.log (500000000000 / 56499544003647) := by
    rw [show ((56499544003647 / 500000000000) : ℝ) = ((500000000000 / 56499544003647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4731817209 / 1000000000) ≤ -Real.log (250000000000 / 28375407912063) ∧
    -Real.log (250000000000 / 28375407912063) ≤ (18483661 / 3906250) := by
  have h := checkLog_sound (w := (12375407912063 / 44375407912063)) (n := 12)
    (lo := (572934129 / 1000000000)) (hi := (57293413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28375407912063 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28375407912063 / 16000000000000) = 1/(250000000000 / 28375407912063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4731817209 / 1000000000) (18483661 / 3906250) (Real.log (28375407912063 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28375407912063 / 250000000000) = -Real.log (250000000000 / 28375407912063) := by
    rw [show ((28375407912063 / 250000000000) : ℝ) = ((250000000000 / 28375407912063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236179577 / 50000000) ≤ -Real.log (500000000000 / 56285917092561) ∧
    -Real.log (500000000000 / 56285917092561) ≤ (4723591547 / 1000000000) := by
  have h := checkLog_sound (w := (24285917092561 / 88285917092561)) (n := 12)
    (lo := (28235423 / 50000000)) (hi := (564708461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56285917092561 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56285917092561 / 32000000000000) = 1/(500000000000 / 56285917092561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236179577 / 50000000) (4723591547 / 1000000000) (Real.log (56285917092561 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56285917092561 / 500000000000) = -Real.log (500000000000 / 56285917092561) := by
    rw [show ((56285917092561 / 500000000000) : ℝ) = ((500000000000 / 56285917092561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1182003121 / 250000000) ≤ -Real.log (100000000000 / 11307060970741) ∧
    -Real.log (100000000000 / 11307060970741) ≤ (4728012491 / 1000000000) := by
  have h := checkLog_sound (w := (4907060970741 / 17707060970741)) (n := 12)
    (lo := (142282351 / 250000000)) (hi := (113825881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11307060970741 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11307060970741 / 6400000000000) = 1/(100000000000 / 11307060970741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1182003121 / 250000000) (4728012491 / 1000000000) (Real.log (11307060970741 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11307060970741 / 100000000000) = -Real.log (100000000000 / 11307060970741) := by
    rw [show ((11307060970741 / 100000000000) : ℝ) = ((100000000000 / 11307060970741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0006
