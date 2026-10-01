import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell132
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

theorem reflection_log_1_neg : (283621103 / 1000000000) ≤ -Real.log (5120 / 6799) ∧
    -Real.log (5120 / 6799) ≤ (17726319 / 62500000) := by
  have h := checkLog_sound (w := (1679 / 11919)) (n := 12)
    (lo := (283621103 / 1000000000)) (hi := (17726319 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6799 / 5120) = 1/(5120 / 6799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (283621103 / 1000000000) (17726319 / 62500000) (Real.log (6799 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6799 / 5120) = -Real.log (5120 / 6799) := by
    rw [show ((6799 / 5120) : ℝ) = ((5120 / 6799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (49674039 / 125000000) ≤ -Real.log (3441 / 5120) ∧
    -Real.log (3441 / 5120) ≤ (397392313 / 1000000000) := by
  have h := checkLog_sound (w := (1679 / 8561)) (n := 12)
    (lo := (49674039 / 125000000)) (hi := (397392313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3441) = 1/(3441 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-397392313 / 1000000000) (-49674039 / 125000000) (Real.log (3441 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (70794941 / 250000000) ≤ -Real.log (1280 / 1699) ∧
    -Real.log (1280 / 1699) ≤ (56635953 / 200000000) := by
  have h := checkLog_sound (w := (419 / 2979)) (n := 12)
    (lo := (70794941 / 250000000)) (hi := (56635953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1699 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1699 / 1280) = 1/(1280 / 1699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (70794941 / 250000000) (56635953 / 200000000) (Real.log (1699 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1699 / 1280) = -Real.log (1280 / 1699) := by
    rw [show ((1699 / 1280) : ℝ) = ((1280 / 1699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99130213 / 250000000) ≤ -Real.log (861 / 1280) ∧
    -Real.log (861 / 1280) ≤ (396520853 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2141)) (n := 12)
    (lo := (99130213 / 250000000)) (hi := (396520853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 861) = 1/(861 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-396520853 / 1000000000) (-99130213 / 250000000) (Real.log (861 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (104542191 / 500000000) ≤ -Real.log (1000000 / 1232549) ∧
    -Real.log (1000000 / 1232549) ≤ (209084383 / 1000000000) := by
  have h := checkLog_sound (w := (232549 / 2232549)) (n := 12)
    (lo := (104542191 / 500000000)) (hi := (209084383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232549 / 1000000) = 1/(1000000 / 1232549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (104542191 / 500000000) (209084383 / 1000000000) (Real.log (1232549 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1232549 / 1000000) = -Real.log (1000000 / 1232549) := by
    rw [show ((1232549 / 1000000) : ℝ) = ((1000000 / 1232549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52936129 / 200000000) ≤ -Real.log (767451 / 1000000) ∧
    -Real.log (767451 / 1000000) ≤ (132340323 / 500000000) := by
  have h := checkLog_sound (w := (232549 / 1767451)) (n := 12)
    (lo := (52936129 / 200000000)) (hi := (132340323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767451) = 1/(767451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-132340323 / 500000000) (-52936129 / 200000000) (Real.log (767451 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (52356473 / 250000000) ≤ -Real.log (100000 / 123297) ∧
    -Real.log (100000 / 123297) ≤ (209425893 / 1000000000) := by
  have h := checkLog_sound (w := (23297 / 223297)) (n := 12)
    (lo := (52356473 / 250000000)) (hi := (209425893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123297 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123297 / 100000) = 1/(100000 / 123297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (52356473 / 250000000) (209425893 / 1000000000) (Real.log (123297 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (123297 / 100000) = -Real.log (100000 / 123297) := by
    rw [show ((123297 / 100000) : ℝ) = ((100000 / 123297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (66307341 / 250000000) ≤ -Real.log (76703 / 100000) ∧
    -Real.log (76703 / 100000) ≤ (53045873 / 200000000) := by
  have h := checkLog_sound (w := (23297 / 176703)) (n := 12)
    (lo := (66307341 / 250000000)) (hi := (53045873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76703) = 1/(76703 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53045873 / 200000000) (-66307341 / 250000000) (Real.log (76703 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (19297903 / 125000000) ≤ -Real.log (500000 / 583469) ∧
    -Real.log (500000 / 583469) ≤ (6175329 / 40000000) := by
  have h := checkLog_sound (w := (83469 / 1083469)) (n := 12)
    (lo := (19297903 / 125000000)) (hi := (6175329 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583469 / 500000) = 1/(500000 / 583469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (19297903 / 125000000) (6175329 / 40000000) (Real.log (583469 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (583469 / 500000) = -Real.log (500000 / 583469) := by
    rw [show ((583469 / 500000) : ℝ) = ((500000 / 583469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182647209 / 1000000000) ≤ -Real.log (416531 / 500000) ∧
    -Real.log (416531 / 500000) ≤ (18264721 / 100000000) := by
  have h := checkLog_sound (w := (83469 / 916531)) (n := 12)
    (lo := (182647209 / 1000000000)) (hi := (18264721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416531) = 1/(416531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18264721 / 100000000) (-182647209 / 1000000000) (Real.log (416531 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77325277 / 500000000) ≤ -Real.log (4000 / 4669) ∧
    -Real.log (4000 / 4669) ≤ (30930111 / 200000000) := by
  have h := checkLog_sound (w := (669 / 8669)) (n := 12)
    (lo := (77325277 / 500000000)) (hi := (30930111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4669 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4669 / 4000) = 1/(4000 / 4669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77325277 / 500000000) (30930111 / 200000000) (Real.log (4669 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4669 / 4000) = -Real.log (4000 / 4669) := by
    rw [show ((4669 / 4000) : ℝ) = ((4000 / 4669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (183021801 / 1000000000) ≤ -Real.log (3331 / 4000) ∧
    -Real.log (3331 / 4000) ≤ (91510901 / 500000000) := by
  have h := checkLog_sound (w := (669 / 7331)) (n := 12)
    (lo := (183021801 / 1000000000)) (hi := (91510901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3331) = 1/(3331 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91510901 / 500000000) (-183021801 / 1000000000) (Real.log (3331 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679700617 / 1000000000) ≤ -Real.log (250000000000 / 493321718931) ∧
    -Real.log (250000000000 / 493321718931) ≤ (339850309 / 500000000) := by
  have h := checkLog_sound (w := (243321718931 / 743321718931)) (n := 12)
    (lo := (679700617 / 1000000000)) (hi := (339850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493321718931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493321718931 / 250000000000) = 1/(250000000000 / 493321718931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679700617 / 1000000000) (339850309 / 500000000) (Real.log (493321718931 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493321718931 / 250000000000) = -Real.log (250000000000 / 493321718931) := by
    rw [show ((493321718931 / 250000000000) : ℝ) = ((250000000000 / 493321718931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136202683 / 200000000) ≤ -Real.log (62500000000 / 123492444057) ∧
    -Real.log (62500000000 / 123492444057) ≤ (85126677 / 125000000) := by
  have h := checkLog_sound (w := (60992444057 / 185992444057)) (n := 12)
    (lo := (136202683 / 200000000)) (hi := (85126677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123492444057 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123492444057 / 62500000000) = 1/(62500000000 / 123492444057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (136202683 / 200000000) (85126677 / 125000000) (Real.log (123492444057 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (123492444057 / 62500000000) = -Real.log (62500000000 / 123492444057) := by
    rw [show ((123492444057 / 62500000000) : ℝ) = ((62500000000 / 123492444057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (473765027 / 1000000000) ≤ -Real.log (125000000000 / 200753696327) ∧
    -Real.log (125000000000 / 200753696327) ≤ (118441257 / 250000000) := by
  have h := checkLog_sound (w := (75753696327 / 325753696327)) (n := 12)
    (lo := (473765027 / 1000000000)) (hi := (118441257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200753696327 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200753696327 / 125000000000) = 1/(125000000000 / 200753696327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (473765027 / 1000000000) (118441257 / 250000000) (Real.log (200753696327 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (200753696327 / 125000000000) = -Real.log (125000000000 / 200753696327) := by
    rw [show ((200753696327 / 125000000000) : ℝ) = ((125000000000 / 200753696327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (474655257 / 1000000000) ≤ -Real.log (500000000000 / 803729971449) ∧
    -Real.log (500000000000 / 803729971449) ≤ (237327629 / 500000000) := by
  have h := checkLog_sound (w := (303729971449 / 1303729971449)) (n := 12)
    (lo := (474655257 / 1000000000)) (hi := (237327629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803729971449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803729971449 / 500000000000) = 1/(500000000000 / 803729971449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (474655257 / 1000000000) (237327629 / 500000000) (Real.log (803729971449 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (803729971449 / 500000000000) = -Real.log (500000000000 / 803729971449) := by
    rw [show ((803729971449 / 500000000000) : ℝ) = ((500000000000 / 803729971449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (168515217 / 500000000) ≤ -Real.log (500000000000 / 700390847259) ∧
    -Real.log (500000000000 / 700390847259) ≤ (67406087 / 200000000) := by
  have h := checkLog_sound (w := (200390847259 / 1200390847259)) (n := 12)
    (lo := (168515217 / 500000000)) (hi := (67406087 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700390847259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700390847259 / 500000000000) = 1/(500000000000 / 700390847259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (168515217 / 500000000) (67406087 / 200000000) (Real.log (700390847259 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (700390847259 / 500000000000) = -Real.log (500000000000 / 700390847259) := by
    rw [show ((700390847259 / 500000000000) : ℝ) = ((500000000000 / 700390847259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (84418089 / 250000000) ≤ -Real.log (125000000000 / 175210147103) ∧
    -Real.log (125000000000 / 175210147103) ≤ (337672357 / 1000000000) := by
  have h := checkLog_sound (w := (50210147103 / 300210147103)) (n := 12)
    (lo := (84418089 / 250000000)) (hi := (337672357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175210147103 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175210147103 / 125000000000) = 1/(125000000000 / 175210147103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (84418089 / 250000000) (337672357 / 1000000000) (Real.log (175210147103 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (175210147103 / 125000000000) = -Real.log (125000000000 / 175210147103) := by
    rw [show ((175210147103 / 125000000000) : ℝ) = ((125000000000 / 175210147103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (28371247 / 1000000000) ≤ -Real.log (15552439 / 16000000) ∧
    -Real.log (15552439 / 16000000) ≤ (1773203 / 62500000) := by
  have h := checkLog_sound (w := (447561 / 31552439)) (n := 12)
    (lo := (28371247 / 1000000000)) (hi := (1773203 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15552439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15552439) = 1/(15552439 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1773203 / 62500000) (-28371247 / 1000000000) (Real.log (15552439 / 16000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5652797 / 200000000) ≤ -Real.log (243032926039 / 250000000000) ∧
    -Real.log (243032926039 / 250000000000) ≤ (14131993 / 500000000) := by
  have h := checkLog_sound (w := (6967073961 / 493032926039)) (n := 12)
    (lo := (5652797 / 200000000)) (hi := (14131993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243032926039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243032926039) = 1/(243032926039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14131993 / 500000000) (-5652797 / 200000000) (Real.log (243032926039 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell132
