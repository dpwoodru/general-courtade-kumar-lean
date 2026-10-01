import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4544_neg : (92021871 / 500000000) ≤ -Real.log (20000000000 / 24041368057) ∧
    -Real.log (20000000000 / 24041368057) ≤ (184043743 / 1000000000) := by
  have h := checkLog_sound (w := (4041368057 / 44041368057)) (n := 12)
    (lo := (92021871 / 500000000)) (hi := (184043743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24041368057 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24041368057 / 20000000000) = 1/(20000000000 / 24041368057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4544 : Bounds (92021871 / 500000000) (184043743 / 1000000000) (Real.log (24041368057 / 20000000000)) := by
  have h := reflection_log_4544_neg
  have he : Real.log (24041368057 / 20000000000) = -Real.log (20000000000 / 24041368057) := by
    rw [show ((24041368057 / 20000000000) : ℝ) = ((20000000000 / 24041368057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4545_neg : (92257863 / 500000000) ≤ -Real.log (125000000000 / 150329486797) ∧
    -Real.log (125000000000 / 150329486797) ≤ (184515727 / 1000000000) := by
  have h := checkLog_sound (w := (25329486797 / 275329486797)) (n := 12)
    (lo := (92257863 / 500000000)) (hi := (184515727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150329486797 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150329486797 / 125000000000) = 1/(125000000000 / 150329486797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4545 : Bounds (92257863 / 500000000) (184515727 / 1000000000) (Real.log (150329486797 / 125000000000)) := by
  have h := reflection_log_4545_neg
  have he : Real.log (150329486797 / 125000000000) = -Real.log (125000000000 / 150329486797) := by
    rw [show ((150329486797 / 125000000000) : ℝ) = ((125000000000 / 150329486797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4546_neg : (11541941 / 31250000) ≤ -Real.log (250000000000 / 361695620259) ∧
    -Real.log (250000000000 / 361695620259) ≤ (369342113 / 1000000000) := by
  have h := checkLog_sound (w := (111695620259 / 611695620259)) (n := 12)
    (lo := (11541941 / 31250000)) (hi := (369342113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361695620259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361695620259 / 250000000000) = 1/(250000000000 / 361695620259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4546 : Bounds (11541941 / 31250000) (369342113 / 1000000000) (Real.log (361695620259 / 250000000000)) := by
  have h := reflection_log_4546_neg
  have he : Real.log (361695620259 / 250000000000) = -Real.log (250000000000 / 361695620259) := by
    rw [show ((361695620259 / 250000000000) : ℝ) = ((250000000000 / 361695620259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4547_neg : (184774507 / 500000000) ≤ -Real.log (100000000000 / 144708185489) ∧
    -Real.log (100000000000 / 144708185489) ≤ (73909803 / 200000000) := by
  have h := checkLog_sound (w := (44708185489 / 244708185489)) (n := 12)
    (lo := (184774507 / 500000000)) (hi := (73909803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144708185489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144708185489 / 100000000000) = 1/(100000000000 / 144708185489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4547 : Bounds (184774507 / 500000000) (73909803 / 200000000) (Real.log (144708185489 / 100000000000)) := by
  have h := reflection_log_4547_neg
  have he : Real.log (144708185489 / 100000000000) = -Real.log (100000000000 / 144708185489) := by
    rw [show ((144708185489 / 100000000000) : ℝ) = ((100000000000 / 144708185489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4548_neg : (41971127 / 250000000) ≤ -Real.log (2500 / 2957) ∧
    -Real.log (2500 / 2957) ≤ (167884509 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 5457)) (n := 12)
    (lo := (41971127 / 250000000)) (hi := (167884509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2957 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2957 / 2500) = 1/(2500 / 2957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4548 : Bounds (41971127 / 250000000) (167884509 / 1000000000) (Real.log (2957 / 2500)) := by
  have h := reflection_log_4548_neg
  have he : Real.log (2957 / 2500) = -Real.log (2500 / 2957) := by
    rw [show ((2957 / 2500) : ℝ) = ((2500 / 2957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4549_neg : (25233927 / 125000000) ≤ -Real.log (2043 / 2500) ∧
    -Real.log (2043 / 2500) ≤ (201871417 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 4543)) (n := 12)
    (lo := (25233927 / 125000000)) (hi := (201871417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2043) = 1/(2043 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4549 : Bounds (-201871417 / 1000000000) (-25233927 / 125000000) (Real.log (2043 / 2500)) := by
  have h := reflection_log_4549_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4550_neg : (182783 / 1000000000) ≤ -Real.log (2500000 / 2500457) ∧
    -Real.log (2500000 / 2500457) ≤ (357 / 1953125) := by
  have h := checkLog_sound (w := (457 / 5000457)) (n := 12)
    (lo := (182783 / 1000000000)) (hi := (357 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500457 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500457 / 2500000) = 1/(2500000 / 2500457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4550 : Bounds (182783 / 1000000000) (357 / 1953125) (Real.log (2500457 / 2500000)) := by
  have h := reflection_log_4550_neg
  have he : Real.log (2500457 / 2500000) = -Real.log (2500000 / 2500457) := by
    rw [show ((2500457 / 2500000) : ℝ) = ((2500000 / 2500457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4551_neg : (5713 / 31250000) ≤ -Real.log (2499543 / 2500000) ∧
    -Real.log (2499543 / 2500000) ≤ (182817 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 4999543)) (n := 12)
    (lo := (5713 / 31250000)) (hi := (182817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499543) = 1/(2499543 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4551 : Bounds (-182817 / 1000000000) (-5713 / 31250000) (Real.log (2499543 / 2500000)) := by
  have h := reflection_log_4551_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4552_neg : (87840533 / 1000000000) ≤ -Real.log (500000 / 545907) ∧
    -Real.log (500000 / 545907) ≤ (43920267 / 500000000) := by
  have h := checkLog_sound (w := (45907 / 1045907)) (n := 12)
    (lo := (87840533 / 1000000000)) (hi := (43920267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545907 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545907 / 500000) = 1/(500000 / 545907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4552 : Bounds (87840533 / 1000000000) (43920267 / 500000000) (Real.log (545907 / 500000)) := by
  have h := reflection_log_4552_neg
  have he : Real.log (545907 / 500000) = -Real.log (500000 / 545907) := by
    rw [show ((545907 / 500000) : ℝ) = ((500000 / 545907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4553_neg : (3852243 / 40000000) ≤ -Real.log (454093 / 500000) ∧
    -Real.log (454093 / 500000) ≤ (24076519 / 250000000) := by
  have h := checkLog_sound (w := (45907 / 954093)) (n := 12)
    (lo := (3852243 / 40000000)) (hi := (24076519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454093) = 1/(454093 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4553 : Bounds (-24076519 / 250000000) (-3852243 / 40000000) (Real.log (454093 / 500000)) := by
  have h := reflection_log_4553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4554_neg : (5503427 / 62500000) ≤ -Real.log (62500 / 68253) ∧
    -Real.log (62500 / 68253) ≤ (88054833 / 1000000000) := by
  have h := checkLog_sound (w := (5753 / 130753)) (n := 12)
    (lo := (5503427 / 62500000)) (hi := (88054833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68253 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68253 / 62500) = 1/(62500 / 68253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4554 : Bounds (5503427 / 62500000) (88054833 / 1000000000) (Real.log (68253 / 62500)) := by
  have h := reflection_log_4554_neg
  have he : Real.log (68253 / 62500) = -Real.log (62500 / 68253) := by
    rw [show ((68253 / 62500) : ℝ) = ((62500 / 68253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4555_neg : (19312753 / 200000000) ≤ -Real.log (56747 / 62500) ∧
    -Real.log (56747 / 62500) ≤ (48281883 / 500000000) := by
  have h := checkLog_sound (w := (5753 / 119247)) (n := 12)
    (lo := (19312753 / 200000000)) (hi := (48281883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56747) = 1/(56747 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4555 : Bounds (-48281883 / 500000000) (-19312753 / 200000000) (Real.log (56747 / 62500)) := by
  have h := reflection_log_4555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4556_neg : (2127233 / 250000000) ≤ -Real.log (3873152991 / 3906250000) ∧
    -Real.log (3873152991 / 3906250000) ≤ (8508933 / 1000000000) := by
  have h := checkLog_sound (w := (33097009 / 7779402991)) (n := 12)
    (lo := (2127233 / 250000000)) (hi := (8508933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3873152991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3873152991) = 1/(3873152991 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4556 : Bounds (-8508933 / 1000000000) (-2127233 / 250000000) (Real.log (3873152991 / 3906250000)) := by
  have h := reflection_log_4556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4557_neg : (4232771 / 500000000) ≤ -Real.log (247892547351 / 250000000000) ∧
    -Real.log (247892547351 / 250000000000) ≤ (8465543 / 1000000000) := by
  have h := checkLog_sound (w := (2107452649 / 497892547351)) (n := 12)
    (lo := (4232771 / 500000000)) (hi := (8465543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247892547351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247892547351) = 1/(247892547351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4557 : Bounds (-8465543 / 1000000000) (-4232771 / 500000000) (Real.log (247892547351 / 250000000000)) := by
  have h := reflection_log_4557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4558_neg : (11509163 / 62500000) ≤ -Real.log (500000000000 / 601096030989) ∧
    -Real.log (500000000000 / 601096030989) ≤ (184146609 / 1000000000) := by
  have h := checkLog_sound (w := (101096030989 / 1101096030989)) (n := 12)
    (lo := (11509163 / 62500000)) (hi := (184146609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601096030989 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601096030989 / 500000000000) = 1/(500000000000 / 601096030989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4558 : Bounds (11509163 / 62500000) (184146609 / 1000000000) (Real.log (601096030989 / 500000000000)) := by
  have h := reflection_log_4558_neg
  have he : Real.log (601096030989 / 500000000000) = -Real.log (500000000000 / 601096030989) := by
    rw [show ((601096030989 / 500000000000) : ℝ) = ((500000000000 / 601096030989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4559_neg : (184618597 / 1000000000) ≤ -Real.log (4000000000 / 4811038469) ∧
    -Real.log (4000000000 / 4811038469) ≤ (92309299 / 500000000) := by
  have h := checkLog_sound (w := (811038469 / 8811038469)) (n := 12)
    (lo := (184618597 / 1000000000)) (hi := (92309299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4811038469 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4811038469 / 4000000000) = 1/(4000000000 / 4811038469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4559 : Bounds (184618597 / 1000000000) (92309299 / 500000000) (Real.log (4811038469 / 4000000000)) := by
  have h := reflection_log_4559_neg
  have he : Real.log (4811038469 / 4000000000) = -Real.log (4000000000 / 4811038469) := by
    rw [show ((4811038469 / 4000000000) : ℝ) = ((4000000000 / 4811038469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4560_neg : (184774507 / 500000000) ≤ -Real.log (125000000000 / 180885231861) ∧
    -Real.log (125000000000 / 180885231861) ≤ (73909803 / 200000000) := by
  have h := checkLog_sound (w := (55885231861 / 305885231861)) (n := 12)
    (lo := (184774507 / 500000000)) (hi := (73909803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180885231861 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180885231861 / 125000000000) = 1/(125000000000 / 180885231861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4560 : Bounds (184774507 / 500000000) (73909803 / 200000000) (Real.log (180885231861 / 125000000000)) := by
  have h := reflection_log_4560_neg
  have he : Real.log (180885231861 / 125000000000) = -Real.log (125000000000 / 180885231861) := by
    rw [show ((180885231861 / 125000000000) : ℝ) = ((125000000000 / 180885231861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4561_neg : (14790237 / 40000000) ≤ -Real.log (125000000000 / 180922662751) ∧
    -Real.log (125000000000 / 180922662751) ≤ (184877963 / 500000000) := by
  have h := checkLog_sound (w := (55922662751 / 305922662751)) (n := 12)
    (lo := (14790237 / 40000000)) (hi := (184877963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180922662751 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180922662751 / 125000000000) = 1/(125000000000 / 180922662751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4561 : Bounds (14790237 / 40000000) (184877963 / 500000000) (Real.log (180922662751 / 125000000000)) := by
  have h := reflection_log_4561_neg
  have he : Real.log (180922662751 / 125000000000) = -Real.log (125000000000 / 180922662751) := by
    rw [show ((180922662751 / 125000000000) : ℝ) = ((125000000000 / 180922662751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4562_neg : (3359381 / 20000000) ≤ -Real.log (10000 / 11829) ∧
    -Real.log (10000 / 11829) ≤ (167969051 / 1000000000) := by
  have h := checkLog_sound (w := (1829 / 21829)) (n := 12)
    (lo := (3359381 / 20000000)) (hi := (167969051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11829 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11829 / 10000) = 1/(10000 / 11829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4562 : Bounds (3359381 / 20000000) (167969051 / 1000000000) (Real.log (11829 / 10000)) := by
  have h := reflection_log_4562_neg
  have he : Real.log (11829 / 10000) = -Real.log (10000 / 11829) := by
    rw [show ((11829 / 10000) : ℝ) = ((10000 / 11829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4563_neg : (3156153 / 15625000) ≤ -Real.log (8171 / 10000) ∧
    -Real.log (8171 / 10000) ≤ (201993793 / 1000000000) := by
  have h := checkLog_sound (w := (1829 / 18171)) (n := 12)
    (lo := (3156153 / 15625000)) (hi := (201993793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8171) = 1/(8171 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4563 : Bounds (-201993793 / 1000000000) (-3156153 / 15625000) (Real.log (8171 / 10000)) := by
  have h := reflection_log_4563_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4564_neg : (182883 / 1000000000) ≤ -Real.log (10000000 / 10001829) ∧
    -Real.log (10000000 / 10001829) ≤ (45721 / 250000000) := by
  have h := checkLog_sound (w := (1829 / 20001829)) (n := 12)
    (lo := (182883 / 1000000000)) (hi := (45721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001829 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001829 / 10000000) = 1/(10000000 / 10001829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4564 : Bounds (182883 / 1000000000) (45721 / 250000000) (Real.log (10001829 / 10000000)) := by
  have h := reflection_log_4564_neg
  have he : Real.log (10001829 / 10000000) = -Real.log (10000000 / 10001829) := by
    rw [show ((10001829 / 10000000) : ℝ) = ((10000000 / 10001829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4565_neg : (45729 / 250000000) ≤ -Real.log (9998171 / 10000000) ∧
    -Real.log (9998171 / 10000000) ≤ (182917 / 1000000000) := by
  have h := checkLog_sound (w := (1829 / 19998171)) (n := 12)
    (lo := (45729 / 250000000)) (hi := (182917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998171) = 1/(9998171 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4565 : Bounds (-182917 / 1000000000) (-45729 / 250000000) (Real.log (9998171 / 10000000)) := by
  have h := reflection_log_4565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4566_neg : (87887243 / 1000000000) ≤ -Real.log (200000 / 218373) ∧
    -Real.log (200000 / 218373) ≤ (21971811 / 250000000) := by
  have h := checkLog_sound (w := (18373 / 418373)) (n := 12)
    (lo := (87887243 / 1000000000)) (hi := (21971811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218373 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218373 / 200000) = 1/(200000 / 218373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4566 : Bounds (87887243 / 1000000000) (21971811 / 250000000) (Real.log (218373 / 200000)) := by
  have h := reflection_log_4566_neg
  have he : Real.log (218373 / 200000) = -Real.log (200000 / 218373) := by
    rw [show ((218373 / 200000) : ℝ) = ((200000 / 218373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4567_neg : (96362233 / 1000000000) ≤ -Real.log (181627 / 200000) ∧
    -Real.log (181627 / 200000) ≤ (48181117 / 500000000) := by
  have h := checkLog_sound (w := (18373 / 381627)) (n := 12)
    (lo := (96362233 / 1000000000)) (hi := (48181117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181627) = 1/(181627 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4567 : Bounds (-48181117 / 500000000) (-96362233 / 1000000000) (Real.log (181627 / 200000)) := by
  have h := reflection_log_4567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4568_neg : (22025383 / 250000000) ≤ -Real.log (1000000 / 1092099) ∧
    -Real.log (1000000 / 1092099) ≤ (88101533 / 1000000000) := by
  have h := checkLog_sound (w := (92099 / 2092099)) (n := 12)
    (lo := (22025383 / 250000000)) (hi := (88101533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092099 / 1000000) = 1/(1000000 / 1092099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4568 : Bounds (22025383 / 250000000) (88101533 / 1000000000) (Real.log (1092099 / 1000000)) := by
  have h := reflection_log_4568_neg
  have he : Real.log (1092099 / 1000000) = -Real.log (1000000 / 1092099) := by
    rw [show ((1092099 / 1000000) : ℝ) = ((1000000 / 1092099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4569_neg : (96619937 / 1000000000) ≤ -Real.log (907901 / 1000000) ∧
    -Real.log (907901 / 1000000) ≤ (48309969 / 500000000) := by
  have h := checkLog_sound (w := (92099 / 1907901)) (n := 12)
    (lo := (96619937 / 1000000000)) (hi := (48309969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907901) = 1/(907901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4569 : Bounds (-48309969 / 500000000) (-96619937 / 1000000000) (Real.log (907901 / 1000000)) := by
  have h := reflection_log_4569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4570_neg : (2129601 / 250000000) ≤ -Real.log (991517774199 / 1000000000000) ∧
    -Real.log (991517774199 / 1000000000000) ≤ (1703681 / 200000000) := by
  have h := checkLog_sound (w := (8482225801 / 1991517774199)) (n := 12)
    (lo := (2129601 / 250000000)) (hi := (1703681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991517774199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991517774199) = 1/(991517774199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4570 : Bounds (-1703681 / 200000000) (-2129601 / 250000000) (Real.log (991517774199 / 1000000000000)) := by
  have h := reflection_log_4570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4571_neg : (8474989 / 1000000000) ≤ -Real.log (39662432871 / 40000000000) ∧
    -Real.log (39662432871 / 40000000000) ≤ (847499 / 100000000) := by
  have h := checkLog_sound (w := (337567129 / 79662432871)) (n := 12)
    (lo := (8474989 / 1000000000)) (hi := (847499 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39662432871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39662432871) = 1/(39662432871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4571 : Bounds (-847499 / 100000000) (-8474989 / 1000000000) (Real.log (39662432871 / 40000000000)) := by
  have h := reflection_log_4571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4572_neg : (46062369 / 250000000) ≤ -Real.log (500000000000 / 601157867497) ∧
    -Real.log (500000000000 / 601157867497) ≤ (184249477 / 1000000000) := by
  have h := checkLog_sound (w := (101157867497 / 1101157867497)) (n := 12)
    (lo := (46062369 / 250000000)) (hi := (184249477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601157867497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601157867497 / 500000000000) = 1/(500000000000 / 601157867497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4572 : Bounds (46062369 / 250000000) (184249477 / 1000000000) (Real.log (601157867497 / 500000000000)) := by
  have h := reflection_log_4572_neg
  have he : Real.log (601157867497 / 500000000000) = -Real.log (500000000000 / 601157867497) := by
    rw [show ((601157867497 / 500000000000) : ℝ) = ((500000000000 / 601157867497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4573_neg : (184721469 / 1000000000) ≤ -Real.log (125000000000 / 150360419253) ∧
    -Real.log (125000000000 / 150360419253) ≤ (18472147 / 100000000) := by
  have h := checkLog_sound (w := (25360419253 / 275360419253)) (n := 12)
    (lo := (184721469 / 1000000000)) (hi := (18472147 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150360419253 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150360419253 / 125000000000) = 1/(125000000000 / 150360419253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4573 : Bounds (184721469 / 1000000000) (18472147 / 100000000) (Real.log (150360419253 / 125000000000)) := by
  have h := reflection_log_4573_neg
  have he : Real.log (150360419253 / 125000000000) = -Real.log (125000000000 / 150360419253) := by
    rw [show ((150360419253 / 125000000000) : ℝ) = ((125000000000 / 150360419253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4574_neg : (14790237 / 40000000) ≤ -Real.log (500000000000 / 723690651003) ∧
    -Real.log (500000000000 / 723690651003) ≤ (184877963 / 500000000) := by
  have h := checkLog_sound (w := (223690651003 / 1223690651003)) (n := 12)
    (lo := (14790237 / 40000000)) (hi := (184877963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723690651003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723690651003 / 500000000000) = 1/(500000000000 / 723690651003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4574 : Bounds (14790237 / 40000000) (184877963 / 500000000) (Real.log (723690651003 / 500000000000)) := by
  have h := reflection_log_4574_neg
  have he : Real.log (723690651003 / 500000000000) = -Real.log (500000000000 / 723690651003) := by
    rw [show ((723690651003 / 500000000000) : ℝ) = ((500000000000 / 723690651003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4575_neg : (369962843 / 1000000000) ≤ -Real.log (500000000000 / 723840411211) ∧
    -Real.log (500000000000 / 723840411211) ≤ (92490711 / 250000000) := by
  have h := checkLog_sound (w := (223840411211 / 1223840411211)) (n := 12)
    (lo := (369962843 / 1000000000)) (hi := (92490711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723840411211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723840411211 / 500000000000) = 1/(500000000000 / 723840411211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4575 : Bounds (369962843 / 1000000000) (92490711 / 250000000) (Real.log (723840411211 / 500000000000)) := by
  have h := reflection_log_4575_neg
  have he : Real.log (723840411211 / 500000000000) = -Real.log (500000000000 / 723840411211) := by
    rw [show ((723840411211 / 500000000000) : ℝ) = ((500000000000 / 723840411211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4576_neg : (10503349 / 62500000) ≤ -Real.log (1000 / 1183) ∧
    -Real.log (1000 / 1183) ≤ (33610717 / 200000000) := by
  have h := checkLog_sound (w := (183 / 2183)) (n := 12)
    (lo := (10503349 / 62500000)) (hi := (33610717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183 / 1000) = 1/(1000 / 1183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4576 : Bounds (10503349 / 62500000) (33610717 / 200000000) (Real.log (1183 / 1000)) := by
  have h := reflection_log_4576_neg
  have he : Real.log (1183 / 1000) = -Real.log (1000 / 1183) := by
    rw [show ((1183 / 1000) : ℝ) = ((1000 / 1183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4577_neg : (25264523 / 125000000) ≤ -Real.log (817 / 1000) ∧
    -Real.log (817 / 1000) ≤ (40423237 / 200000000) := by
  have h := checkLog_sound (w := (183 / 1817)) (n := 12)
    (lo := (25264523 / 125000000)) (hi := (40423237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 817) = 1/(817 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4577 : Bounds (-40423237 / 200000000) (-25264523 / 125000000) (Real.log (817 / 1000)) := by
  have h := reflection_log_4577_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4578_neg : (182983 / 1000000000) ≤ -Real.log (1000000 / 1000183) ∧
    -Real.log (1000000 / 1000183) ≤ (22873 / 125000000) := by
  have h := checkLog_sound (w := (183 / 2000183)) (n := 12)
    (lo := (182983 / 1000000000)) (hi := (22873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000183 / 1000000) = 1/(1000000 / 1000183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4578 : Bounds (182983 / 1000000000) (22873 / 125000000) (Real.log (1000183 / 1000000)) := by
  have h := reflection_log_4578_neg
  have he : Real.log (1000183 / 1000000) = -Real.log (1000000 / 1000183) := by
    rw [show ((1000183 / 1000000) : ℝ) = ((1000000 / 1000183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4579_neg : (22877 / 125000000) ≤ -Real.log (999817 / 1000000) ∧
    -Real.log (999817 / 1000000) ≤ (183017 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 1999817)) (n := 12)
    (lo := (22877 / 125000000)) (hi := (183017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999817) = 1/(999817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4579 : Bounds (-183017 / 1000000000) (-22877 / 125000000) (Real.log (999817 / 1000000)) := by
  have h := reflection_log_4579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4580_neg : (87933951 / 1000000000) ≤ -Real.log (250000 / 272979) ∧
    -Real.log (250000 / 272979) ≤ (171746 / 1953125) := by
  have h := checkLog_sound (w := (22979 / 522979)) (n := 12)
    (lo := (87933951 / 1000000000)) (hi := (171746 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272979 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272979 / 250000) = 1/(250000 / 272979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4580 : Bounds (87933951 / 1000000000) (171746 / 1953125) (Real.log (272979 / 250000)) := by
  have h := reflection_log_4580_neg
  have he : Real.log (272979 / 250000) = -Real.log (250000 / 272979) := by
    rw [show ((272979 / 250000) : ℝ) = ((250000 / 272979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4581_neg : (96418393 / 1000000000) ≤ -Real.log (227021 / 250000) ∧
    -Real.log (227021 / 250000) ≤ (48209197 / 500000000) := by
  have h := checkLog_sound (w := (22979 / 477021)) (n := 12)
    (lo := (96418393 / 1000000000)) (hi := (48209197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227021) = 1/(227021 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4581 : Bounds (-48209197 / 500000000) (-96418393 / 1000000000) (Real.log (227021 / 250000)) := by
  have h := reflection_log_4581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4582_neg : (8814823 / 100000000) ≤ -Real.log (20000 / 21843) ∧
    -Real.log (20000 / 21843) ≤ (88148231 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 41843)) (n := 12)
    (lo := (8814823 / 100000000)) (hi := (88148231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21843 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21843 / 20000) = 1/(20000 / 21843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4582 : Bounds (8814823 / 100000000) (88148231 / 1000000000) (Real.log (21843 / 20000)) := by
  have h := reflection_log_4582_neg
  have he : Real.log (21843 / 20000) = -Real.log (20000 / 21843) := by
    rw [show ((21843 / 20000) : ℝ) = ((20000 / 21843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4583_neg : (6042257 / 62500000) ≤ -Real.log (18157 / 20000) ∧
    -Real.log (18157 / 20000) ≤ (96676113 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 38157)) (n := 12)
    (lo := (6042257 / 62500000)) (hi := (96676113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18157) = 1/(18157 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4583 : Bounds (-96676113 / 1000000000) (-6042257 / 62500000) (Real.log (18157 / 20000)) := by
  have h := reflection_log_4583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4584_neg : (8527881 / 1000000000) ≤ -Real.log (396603351 / 400000000) ∧
    -Real.log (396603351 / 400000000) ≤ (4263941 / 500000000) := by
  have h := checkLog_sound (w := (3396649 / 796603351)) (n := 12)
    (lo := (8527881 / 1000000000)) (hi := (4263941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396603351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396603351) = 1/(396603351 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4584 : Bounds (-4263941 / 500000000) (-8527881 / 1000000000) (Real.log (396603351 / 400000000)) := by
  have h := reflection_log_4584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4585_neg : (4242221 / 500000000) ≤ -Real.log (61971965559 / 62500000000) ∧
    -Real.log (61971965559 / 62500000000) ≤ (8484443 / 1000000000) := by
  have h := checkLog_sound (w := (528034441 / 124471965559)) (n := 12)
    (lo := (4242221 / 500000000)) (hi := (8484443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61971965559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61971965559) = 1/(61971965559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4585 : Bounds (-8484443 / 1000000000) (-4242221 / 500000000) (Real.log (61971965559 / 62500000000)) := by
  have h := reflection_log_4585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4586_neg : (23044043 / 125000000) ≤ -Real.log (500000000000 / 601219710951) ∧
    -Real.log (500000000000 / 601219710951) ≤ (36870469 / 200000000) := by
  have h := checkLog_sound (w := (101219710951 / 1101219710951)) (n := 12)
    (lo := (23044043 / 125000000)) (hi := (36870469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601219710951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601219710951 / 500000000000) = 1/(500000000000 / 601219710951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4586 : Bounds (23044043 / 125000000) (36870469 / 200000000) (Real.log (601219710951 / 500000000000)) := by
  have h := reflection_log_4586_neg
  have he : Real.log (601219710951 / 500000000000) = -Real.log (500000000000 / 601219710951) := by
    rw [show ((601219710951 / 500000000000) : ℝ) = ((500000000000 / 601219710951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4587_neg : (92412171 / 500000000) ≤ -Real.log (500000000000 / 601503552349) ∧
    -Real.log (500000000000 / 601503552349) ≤ (184824343 / 1000000000) := by
  have h := checkLog_sound (w := (101503552349 / 1101503552349)) (n := 12)
    (lo := (92412171 / 500000000)) (hi := (184824343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601503552349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601503552349 / 500000000000) = 1/(500000000000 / 601503552349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4587 : Bounds (92412171 / 500000000) (184824343 / 1000000000) (Real.log (601503552349 / 500000000000)) := by
  have h := reflection_log_4587_neg
  have he : Real.log (601503552349 / 500000000000) = -Real.log (500000000000 / 601503552349) := by
    rw [show ((601503552349 / 500000000000) : ℝ) = ((500000000000 / 601503552349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4588_neg : (369962843 / 1000000000) ≤ -Real.log (50000000000 / 72384041121) ∧
    -Real.log (50000000000 / 72384041121) ≤ (92490711 / 250000000) := by
  have h := checkLog_sound (w := (22384041121 / 122384041121)) (n := 12)
    (lo := (369962843 / 1000000000)) (hi := (92490711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72384041121 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72384041121 / 50000000000) = 1/(50000000000 / 72384041121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4588 : Bounds (369962843 / 1000000000) (92490711 / 250000000) (Real.log (72384041121 / 50000000000)) := by
  have h := reflection_log_4588_neg
  have he : Real.log (72384041121 / 50000000000) = -Real.log (50000000000 / 72384041121) := by
    rw [show ((72384041121 / 50000000000) : ℝ) = ((50000000000 / 72384041121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4589_neg : (370169769 / 1000000000) ≤ -Real.log (500000000000 / 723990208079) ∧
    -Real.log (500000000000 / 723990208079) ≤ (37016977 / 100000000) := by
  have h := checkLog_sound (w := (223990208079 / 1223990208079)) (n := 12)
    (lo := (370169769 / 1000000000)) (hi := (37016977 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723990208079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723990208079 / 500000000000) = 1/(500000000000 / 723990208079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4589 : Bounds (370169769 / 1000000000) (37016977 / 100000000) (Real.log (723990208079 / 500000000000)) := by
  have h := reflection_log_4589_neg
  have he : Real.log (723990208079 / 500000000000) = -Real.log (500000000000 / 723990208079) := by
    rw [show ((723990208079 / 500000000000) : ℝ) = ((500000000000 / 723990208079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4590_neg : (1313579 / 7812500) ≤ -Real.log (10000 / 11831) ∧
    -Real.log (10000 / 11831) ≤ (168138113 / 1000000000) := by
  have h := checkLog_sound (w := (1831 / 21831)) (n := 12)
    (lo := (1313579 / 7812500)) (hi := (168138113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11831 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11831 / 10000) = 1/(10000 / 11831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4590 : Bounds (1313579 / 7812500) (168138113 / 1000000000) (Real.log (11831 / 10000)) := by
  have h := reflection_log_4590_neg
  have he : Real.log (11831 / 10000) = -Real.log (10000 / 11831) := by
    rw [show ((11831 / 10000) : ℝ) = ((10000 / 11831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4591_neg : (20223859 / 100000000) ≤ -Real.log (8169 / 10000) ∧
    -Real.log (8169 / 10000) ≤ (202238591 / 1000000000) := by
  have h := checkLog_sound (w := (1831 / 18169)) (n := 12)
    (lo := (20223859 / 100000000)) (hi := (202238591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8169) = 1/(8169 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4591 : Bounds (-202238591 / 1000000000) (-20223859 / 100000000) (Real.log (8169 / 10000)) := by
  have h := reflection_log_4591_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4592_neg : (183083 / 1000000000) ≤ -Real.log (10000000 / 10001831) ∧
    -Real.log (10000000 / 10001831) ≤ (45771 / 250000000) := by
  have h := checkLog_sound (w := (1831 / 20001831)) (n := 12)
    (lo := (183083 / 1000000000)) (hi := (45771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001831 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001831 / 10000000) = 1/(10000000 / 10001831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4592 : Bounds (183083 / 1000000000) (45771 / 250000000) (Real.log (10001831 / 10000000)) := by
  have h := reflection_log_4592_neg
  have he : Real.log (10001831 / 10000000) = -Real.log (10000000 / 10001831) := by
    rw [show ((10001831 / 10000000) : ℝ) = ((10000000 / 10001831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4593_neg : (45779 / 250000000) ≤ -Real.log (9998169 / 10000000) ∧
    -Real.log (9998169 / 10000000) ≤ (183117 / 1000000000) := by
  have h := checkLog_sound (w := (1831 / 19998169)) (n := 12)
    (lo := (45779 / 250000000)) (hi := (183117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998169) = 1/(9998169 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4593 : Bounds (-183117 / 1000000000) (-45779 / 250000000) (Real.log (9998169 / 10000000)) := by
  have h := reflection_log_4593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4594_neg : (87980657 / 1000000000) ≤ -Real.log (1000000 / 1091967) ∧
    -Real.log (1000000 / 1091967) ≤ (43990329 / 500000000) := by
  have h := checkLog_sound (w := (91967 / 2091967)) (n := 12)
    (lo := (87980657 / 1000000000)) (hi := (43990329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091967 / 1000000) = 1/(1000000 / 1091967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4594 : Bounds (87980657 / 1000000000) (43990329 / 500000000) (Real.log (1091967 / 1000000)) := by
  have h := reflection_log_4594_neg
  have he : Real.log (1091967 / 1000000) = -Real.log (1000000 / 1091967) := by
    rw [show ((1091967 / 1000000) : ℝ) = ((1000000 / 1091967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4595_neg : (96474557 / 1000000000) ≤ -Real.log (908033 / 1000000) ∧
    -Real.log (908033 / 1000000) ≤ (48237279 / 500000000) := by
  have h := checkLog_sound (w := (91967 / 1908033)) (n := 12)
    (lo := (96474557 / 1000000000)) (hi := (48237279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908033) = 1/(908033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4595 : Bounds (-48237279 / 500000000) (-96474557 / 1000000000) (Real.log (908033 / 1000000)) := by
  have h := reflection_log_4595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4596_neg : (8819401 / 100000000) ≤ -Real.log (5000 / 5461) ∧
    -Real.log (5000 / 5461) ≤ (88194011 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 10461)) (n := 12)
    (lo := (8819401 / 100000000)) (hi := (88194011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5461 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5461 / 5000) = 1/(5000 / 5461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4596 : Bounds (8819401 / 100000000) (88194011 / 1000000000) (Real.log (5461 / 5000)) := by
  have h := reflection_log_4596_neg
  have he : Real.log (5461 / 5000) = -Real.log (5000 / 5461) := by
    rw [show ((5461 / 5000) : ℝ) = ((5000 / 5461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4597_neg : (24182797 / 250000000) ≤ -Real.log (4539 / 5000) ∧
    -Real.log (4539 / 5000) ≤ (96731189 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 9539)) (n := 12)
    (lo := (24182797 / 250000000)) (hi := (96731189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4539) = 1/(4539 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4597 : Bounds (-96731189 / 1000000000) (-24182797 / 250000000) (Real.log (4539 / 5000)) := by
  have h := reflection_log_4597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4598_neg : (4268589 / 500000000) ≤ -Real.log (24787479 / 25000000) ∧
    -Real.log (24787479 / 25000000) ≤ (8537179 / 1000000000) := by
  have h := checkLog_sound (w := (212521 / 49787479)) (n := 12)
    (lo := (4268589 / 500000000)) (hi := (8537179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24787479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24787479) = 1/(24787479 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4598 : Bounds (-8537179 / 1000000000) (-4268589 / 500000000) (Real.log (24787479 / 25000000)) := by
  have h := reflection_log_4598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4599_neg : (84939 / 10000000) ≤ -Real.log (991542070911 / 1000000000000) ∧
    -Real.log (991542070911 / 1000000000000) ≤ (8493901 / 1000000000) := by
  have h := checkLog_sound (w := (8457929089 / 1991542070911)) (n := 12)
    (lo := (84939 / 10000000)) (hi := (8493901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991542070911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991542070911) = 1/(991542070911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4599 : Bounds (-8493901 / 1000000000) (-84939 / 10000000) (Real.log (991542070911 / 1000000000000)) := by
  have h := reflection_log_4599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4600_neg : (92227607 / 500000000) ≤ -Real.log (62500000000 / 75160195169) ∧
    -Real.log (62500000000 / 75160195169) ≤ (36891043 / 200000000) := by
  have h := checkLog_sound (w := (12660195169 / 137660195169)) (n := 12)
    (lo := (92227607 / 500000000)) (hi := (36891043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75160195169 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75160195169 / 62500000000) = 1/(62500000000 / 75160195169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4600 : Bounds (92227607 / 500000000) (36891043 / 200000000) (Real.log (75160195169 / 62500000000)) := by
  have h := reflection_log_4600_neg
  have he : Real.log (75160195169 / 62500000000) = -Real.log (62500000000 / 75160195169) := by
    rw [show ((75160195169 / 62500000000) : ℝ) = ((62500000000 / 75160195169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4601_neg : (184925199 / 1000000000) ≤ -Real.log (100000000000 / 120312844239) ∧
    -Real.log (100000000000 / 120312844239) ≤ (462313 / 2500000) := by
  have h := checkLog_sound (w := (20312844239 / 220312844239)) (n := 12)
    (lo := (184925199 / 1000000000)) (hi := (462313 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120312844239 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120312844239 / 100000000000) = 1/(100000000000 / 120312844239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4601 : Bounds (184925199 / 1000000000) (462313 / 2500000) (Real.log (120312844239 / 100000000000)) := by
  have h := reflection_log_4601_neg
  have he : Real.log (120312844239 / 100000000000) = -Real.log (100000000000 / 120312844239) := by
    rw [show ((120312844239 / 100000000000) : ℝ) = ((100000000000 / 120312844239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4602_neg : (370169769 / 1000000000) ≤ -Real.log (250000000000 / 361995104039) ∧
    -Real.log (250000000000 / 361995104039) ≤ (37016977 / 100000000) := by
  have h := checkLog_sound (w := (111995104039 / 611995104039)) (n := 12)
    (lo := (370169769 / 1000000000)) (hi := (37016977 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361995104039 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361995104039 / 250000000000) = 1/(250000000000 / 361995104039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4602 : Bounds (370169769 / 1000000000) (37016977 / 100000000) (Real.log (361995104039 / 250000000000)) := by
  have h := reflection_log_4602_neg
  have he : Real.log (361995104039 / 250000000000) = -Real.log (250000000000 / 361995104039) := by
    rw [show ((361995104039 / 250000000000) : ℝ) = ((250000000000 / 361995104039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4603_neg : (185188351 / 500000000) ≤ -Real.log (500000000000 / 724140041621) ∧
    -Real.log (500000000000 / 724140041621) ≤ (370376703 / 1000000000) := by
  have h := checkLog_sound (w := (224140041621 / 1224140041621)) (n := 12)
    (lo := (185188351 / 500000000)) (hi := (370376703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724140041621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724140041621 / 500000000000) = 1/(500000000000 / 724140041621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4603 : Bounds (185188351 / 500000000) (370376703 / 1000000000) (Real.log (724140041621 / 500000000000)) := by
  have h := reflection_log_4603_neg
  have he : Real.log (724140041621 / 500000000000) = -Real.log (500000000000 / 724140041621) := by
    rw [show ((724140041621 / 500000000000) : ℝ) = ((500000000000 / 724140041621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4604_neg : (21027829 / 125000000) ≤ -Real.log (1250 / 1479) ∧
    -Real.log (1250 / 1479) ≤ (168222633 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2729)) (n := 12)
    (lo := (21027829 / 125000000)) (hi := (168222633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479 / 1250) = 1/(1250 / 1479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4604 : Bounds (21027829 / 125000000) (168222633 / 1000000000) (Real.log (1479 / 1250)) := by
  have h := reflection_log_4604_neg
  have he : Real.log (1479 / 1250) = -Real.log (1250 / 1479) := by
    rw [show ((1479 / 1250) : ℝ) = ((1250 / 1479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4605_neg : (50590253 / 250000000) ≤ -Real.log (1021 / 1250) ∧
    -Real.log (1021 / 1250) ≤ (202361013 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2271)) (n := 12)
    (lo := (50590253 / 250000000)) (hi := (202361013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1021) = 1/(1021 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4605 : Bounds (-202361013 / 1000000000) (-50590253 / 250000000) (Real.log (1021 / 1250)) := by
  have h := reflection_log_4605_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4606_neg : (183183 / 1000000000) ≤ -Real.log (1250000 / 1250229) ∧
    -Real.log (1250000 / 1250229) ≤ (11449 / 62500000) := by
  have h := checkLog_sound (w := (229 / 2500229)) (n := 12)
    (lo := (183183 / 1000000000)) (hi := (11449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250229 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250229 / 1250000) = 1/(1250000 / 1250229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4606 : Bounds (183183 / 1000000000) (11449 / 62500000) (Real.log (1250229 / 1250000)) := by
  have h := reflection_log_4606_neg
  have he : Real.log (1250229 / 1250000) = -Real.log (1250000 / 1250229) := by
    rw [show ((1250229 / 1250000) : ℝ) = ((1250000 / 1250229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4607_neg : (11451 / 62500000) ≤ -Real.log (1249771 / 1250000) ∧
    -Real.log (1249771 / 1250000) ≤ (183217 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2499771)) (n := 12)
    (lo := (11451 / 62500000)) (hi := (183217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249771) = 1/(1249771 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4607 : Bounds (-183217 / 1000000000) (-11451 / 62500000) (Real.log (1249771 / 1250000)) := by
  have h := reflection_log_4607_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
