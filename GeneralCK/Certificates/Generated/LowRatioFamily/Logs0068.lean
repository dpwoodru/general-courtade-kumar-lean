import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4352_neg : (6668007 / 40000000) ≤ -Real.log (5000 / 5907) ∧
    -Real.log (5000 / 5907) ≤ (10418761 / 62500000) := by
  have h := checkLog_sound (w := (907 / 10907)) (n := 12)
    (lo := (6668007 / 40000000)) (hi := (10418761 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5907 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5907 / 5000) = 1/(5000 / 5907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4352 : Bounds (6668007 / 40000000) (10418761 / 62500000) (Real.log (5907 / 5000)) := by
  have h := reflection_log_4352_neg
  have he : Real.log (5907 / 5000) = -Real.log (5000 / 5907) := by
    rw [show ((5907 / 5000) : ℝ) = ((5000 / 5907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4353_neg : (100079857 / 500000000) ≤ -Real.log (4093 / 5000) ∧
    -Real.log (4093 / 5000) ≤ (40031943 / 200000000) := by
  have h := checkLog_sound (w := (907 / 9093)) (n := 12)
    (lo := (100079857 / 500000000)) (hi := (40031943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4093) = 1/(4093 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4353 : Bounds (-40031943 / 200000000) (-100079857 / 500000000) (Real.log (4093 / 5000)) := by
  have h := reflection_log_4353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4354_neg : (181383 / 1000000000) ≤ -Real.log (5000000 / 5000907) ∧
    -Real.log (5000000 / 5000907) ≤ (22673 / 125000000) := by
  have h := checkLog_sound (w := (907 / 10000907)) (n := 12)
    (lo := (181383 / 1000000000)) (hi := (22673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000907 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000907 / 5000000) = 1/(5000000 / 5000907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4354 : Bounds (181383 / 1000000000) (22673 / 125000000) (Real.log (5000907 / 5000000)) := by
  have h := reflection_log_4354_neg
  have he : Real.log (5000907 / 5000000) = -Real.log (5000000 / 5000907) := by
    rw [show ((5000907 / 5000000) : ℝ) = ((5000000 / 5000907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4355_neg : (22677 / 125000000) ≤ -Real.log (4999093 / 5000000) ∧
    -Real.log (4999093 / 5000000) ≤ (181417 / 1000000000) := by
  have h := checkLog_sound (w := (907 / 9999093)) (n := 12)
    (lo := (22677 / 125000000)) (hi := (181417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999093) = 1/(4999093 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4355 : Bounds (-181417 / 1000000000) (-22677 / 125000000) (Real.log (4999093 / 5000000)) := by
  have h := reflection_log_4355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4356_neg : (43594097 / 500000000) ≤ -Real.log (500000 / 545551) ∧
    -Real.log (500000 / 545551) ≤ (17437639 / 200000000) := by
  have h := checkLog_sound (w := (45551 / 1045551)) (n := 12)
    (lo := (43594097 / 500000000)) (hi := (17437639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545551 / 500000) = 1/(500000 / 545551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4356 : Bounds (43594097 / 500000000) (17437639 / 200000000) (Real.log (545551 / 500000)) := by
  have h := reflection_log_4356_neg
  have he : Real.log (545551 / 500000) = -Real.log (500000 / 545551) := by
    rw [show ((545551 / 500000) : ℝ) = ((500000 / 545551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4357_neg : (47761201 / 500000000) ≤ -Real.log (454449 / 500000) ∧
    -Real.log (454449 / 500000) ≤ (95522403 / 1000000000) := by
  have h := checkLog_sound (w := (45551 / 954449)) (n := 12)
    (lo := (47761201 / 500000000)) (hi := (95522403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454449) = 1/(454449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4357 : Bounds (-95522403 / 1000000000) (-47761201 / 500000000) (Real.log (454449 / 500000)) := by
  have h := reflection_log_4357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4358_neg : (87400801 / 1000000000) ≤ -Real.log (500000 / 545667) ∧
    -Real.log (500000 / 545667) ≤ (43700401 / 500000000) := by
  have h := checkLog_sound (w := (45667 / 1045667)) (n := 12)
    (lo := (87400801 / 1000000000)) (hi := (43700401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545667 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545667 / 500000) = 1/(500000 / 545667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4358 : Bounds (87400801 / 1000000000) (43700401 / 500000000) (Real.log (545667 / 500000)) := by
  have h := reflection_log_4358_neg
  have he : Real.log (545667 / 500000) = -Real.log (500000 / 545667) := by
    rw [show ((545667 / 500000) : ℝ) = ((500000 / 545667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4359_neg : (95777689 / 1000000000) ≤ -Real.log (454333 / 500000) ∧
    -Real.log (454333 / 500000) ≤ (9577769 / 100000000) := by
  have h := checkLog_sound (w := (45667 / 954333)) (n := 12)
    (lo := (95777689 / 1000000000)) (hi := (9577769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454333) = 1/(454333 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4359 : Bounds (-9577769 / 100000000) (-95777689 / 1000000000) (Real.log (454333 / 500000)) := by
  have h := reflection_log_4359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4360_neg : (8376887 / 1000000000) ≤ -Real.log (247914525111 / 250000000000) ∧
    -Real.log (247914525111 / 250000000000) ≤ (1047111 / 125000000) := by
  have h := checkLog_sound (w := (2085474889 / 497914525111)) (n := 12)
    (lo := (8376887 / 1000000000)) (hi := (1047111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247914525111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247914525111) = 1/(247914525111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4360 : Bounds (-1047111 / 125000000) (-8376887 / 1000000000) (Real.log (247914525111 / 250000000000)) := by
  have h := reflection_log_4360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4361_neg : (8334207 / 1000000000) ≤ -Real.log (247925106399 / 250000000000) ∧
    -Real.log (247925106399 / 250000000000) ≤ (65111 / 7812500) := by
  have h := checkLog_sound (w := (2074893601 / 497925106399)) (n := 12)
    (lo := (8334207 / 1000000000)) (hi := (65111 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247925106399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247925106399) = 1/(247925106399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4361 : Bounds (-65111 / 7812500) (-8334207 / 1000000000) (Real.log (247925106399 / 250000000000)) := by
  have h := reflection_log_4361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4362_neg : (182710597 / 1000000000) ≤ -Real.log (250000000000 / 300116734771) ∧
    -Real.log (250000000000 / 300116734771) ≤ (91355299 / 500000000) := by
  have h := checkLog_sound (w := (50116734771 / 550116734771)) (n := 12)
    (lo := (182710597 / 1000000000)) (hi := (91355299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300116734771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300116734771 / 250000000000) = 1/(250000000000 / 300116734771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4362 : Bounds (182710597 / 1000000000) (91355299 / 500000000) (Real.log (300116734771 / 250000000000)) := by
  have h := reflection_log_4362_neg
  have he : Real.log (300116734771 / 250000000000) = -Real.log (250000000000 / 300116734771) := by
    rw [show ((300116734771 / 250000000000) : ℝ) = ((250000000000 / 300116734771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4363_neg : (18317849 / 100000000) ≤ -Real.log (250000000000 / 300257190211) ∧
    -Real.log (250000000000 / 300257190211) ≤ (183178491 / 1000000000) := by
  have h := checkLog_sound (w := (50257190211 / 550257190211)) (n := 12)
    (lo := (18317849 / 100000000)) (hi := (183178491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300257190211 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300257190211 / 250000000000) = 1/(250000000000 / 300257190211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4363 : Bounds (18317849 / 100000000) (183178491 / 1000000000) (Real.log (300257190211 / 250000000000)) := by
  have h := reflection_log_4363_neg
  have he : Real.log (300257190211 / 250000000000) = -Real.log (250000000000 / 300257190211) := by
    rw [show ((300257190211 / 250000000000) : ℝ) = ((250000000000 / 300257190211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4364_neg : (366653089 / 1000000000) ≤ -Real.log (125000000000 / 180362159521) ∧
    -Real.log (125000000000 / 180362159521) ≤ (36665309 / 100000000) := by
  have h := checkLog_sound (w := (55362159521 / 305362159521)) (n := 12)
    (lo := (366653089 / 1000000000)) (hi := (36665309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180362159521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180362159521 / 125000000000) = 1/(125000000000 / 180362159521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4364 : Bounds (366653089 / 1000000000) (36665309 / 100000000) (Real.log (180362159521 / 125000000000)) := by
  have h := reflection_log_4364_neg
  have he : Real.log (180362159521 / 125000000000) = -Real.log (125000000000 / 180362159521) := by
    rw [show ((180362159521 / 125000000000) : ℝ) = ((125000000000 / 180362159521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4365_neg : (36685989 / 100000000) ≤ -Real.log (125000000000 / 180399462497) ∧
    -Real.log (125000000000 / 180399462497) ≤ (366859891 / 1000000000) := by
  have h := checkLog_sound (w := (55399462497 / 305399462497)) (n := 12)
    (lo := (36685989 / 100000000)) (hi := (366859891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180399462497 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180399462497 / 125000000000) = 1/(125000000000 / 180399462497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4365 : Bounds (36685989 / 100000000) (366859891 / 1000000000) (Real.log (180399462497 / 125000000000)) := by
  have h := reflection_log_4365_neg
  have he : Real.log (180399462497 / 125000000000) = -Real.log (125000000000 / 180399462497) := by
    rw [show ((180399462497 / 125000000000) : ℝ) = ((125000000000 / 180399462497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4366_neg : (166784817 / 1000000000) ≤ -Real.log (2000 / 2363) ∧
    -Real.log (2000 / 2363) ≤ (83392409 / 500000000) := by
  have h := checkLog_sound (w := (363 / 4363)) (n := 12)
    (lo := (166784817 / 1000000000)) (hi := (83392409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2363 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2363 / 2000) = 1/(2000 / 2363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4366 : Bounds (166784817 / 1000000000) (83392409 / 500000000) (Real.log (2363 / 2000)) := by
  have h := reflection_log_4366_neg
  have he : Real.log (2363 / 2000) = -Real.log (2000 / 2363) := by
    rw [show ((2363 / 2000) : ℝ) = ((2000 / 2363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4367_neg : (100140941 / 500000000) ≤ -Real.log (1637 / 2000) ∧
    -Real.log (1637 / 2000) ≤ (200281883 / 1000000000) := by
  have h := checkLog_sound (w := (363 / 3637)) (n := 12)
    (lo := (100140941 / 500000000)) (hi := (200281883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1637) = 1/(1637 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4367 : Bounds (-200281883 / 1000000000) (-100140941 / 500000000) (Real.log (1637 / 2000)) := by
  have h := reflection_log_4367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4368_neg : (181483 / 1000000000) ≤ -Real.log (2000000 / 2000363) ∧
    -Real.log (2000000 / 2000363) ≤ (45371 / 250000000) := by
  have h := checkLog_sound (w := (363 / 4000363)) (n := 12)
    (lo := (181483 / 1000000000)) (hi := (45371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000363 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000363 / 2000000) = 1/(2000000 / 2000363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4368 : Bounds (181483 / 1000000000) (45371 / 250000000) (Real.log (2000363 / 2000000)) := by
  have h := reflection_log_4368_neg
  have he : Real.log (2000363 / 2000000) = -Real.log (2000000 / 2000363) := by
    rw [show ((2000363 / 2000000) : ℝ) = ((2000000 / 2000363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4369_neg : (45379 / 250000000) ≤ -Real.log (1999637 / 2000000) ∧
    -Real.log (1999637 / 2000000) ≤ (181517 / 1000000000) := by
  have h := checkLog_sound (w := (363 / 3999637)) (n := 12)
    (lo := (45379 / 250000000)) (hi := (181517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999637) = 1/(1999637 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4369 : Bounds (-181517 / 1000000000) (-45379 / 250000000) (Real.log (1999637 / 2000000)) := by
  have h := reflection_log_4369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4370_neg : (17446987 / 200000000) ≤ -Real.log (1000000 / 1091153) ∧
    -Real.log (1000000 / 1091153) ≤ (10904367 / 125000000) := by
  have h := checkLog_sound (w := (91153 / 2091153)) (n := 12)
    (lo := (17446987 / 200000000)) (hi := (10904367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091153 / 1000000) = 1/(1000000 / 1091153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4370 : Bounds (17446987 / 200000000) (10904367 / 125000000) (Real.log (1091153 / 1000000)) := by
  have h := reflection_log_4370_neg
  have he : Real.log (1091153 / 1000000) = -Real.log (1000000 / 1091153) := by
    rw [show ((1091153 / 1000000) : ℝ) = ((1000000 / 1091153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4371_neg : (19115703 / 200000000) ≤ -Real.log (908847 / 1000000) ∧
    -Real.log (908847 / 1000000) ≤ (23894629 / 250000000) := by
  have h := checkLog_sound (w := (91153 / 1908847)) (n := 12)
    (lo := (19115703 / 200000000)) (hi := (23894629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908847) = 1/(908847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4371 : Bounds (-23894629 / 250000000) (-19115703 / 200000000) (Real.log (908847 / 1000000)) := by
  have h := reflection_log_4371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4372_neg : (87447531 / 1000000000) ≤ -Real.log (200000 / 218277) ∧
    -Real.log (200000 / 218277) ≤ (21861883 / 250000000) := by
  have h := checkLog_sound (w := (18277 / 418277)) (n := 12)
    (lo := (87447531 / 1000000000)) (hi := (21861883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218277 / 200000) = 1/(200000 / 218277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4372 : Bounds (87447531 / 1000000000) (21861883 / 250000000) (Real.log (218277 / 200000)) := by
  have h := reflection_log_4372_neg
  have he : Real.log (218277 / 200000) = -Real.log (200000 / 218277) := by
    rw [show ((218277 / 200000) : ℝ) = ((200000 / 218277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4373_neg : (11979227 / 125000000) ≤ -Real.log (181723 / 200000) ∧
    -Real.log (181723 / 200000) ≤ (95833817 / 1000000000) := by
  have h := checkLog_sound (w := (18277 / 381723)) (n := 12)
    (lo := (11979227 / 125000000)) (hi := (95833817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181723) = 1/(181723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4373 : Bounds (-95833817 / 1000000000) (-11979227 / 125000000) (Real.log (181723 / 200000)) := by
  have h := reflection_log_4373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4374_neg : (1677257 / 200000000) ≤ -Real.log (39665951271 / 40000000000) ∧
    -Real.log (39665951271 / 40000000000) ≤ (4193143 / 500000000) := by
  have h := checkLog_sound (w := (334048729 / 79665951271)) (n := 12)
    (lo := (1677257 / 200000000)) (hi := (4193143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39665951271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39665951271) = 1/(39665951271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4374 : Bounds (-4193143 / 500000000) (-1677257 / 200000000) (Real.log (39665951271 / 40000000000)) := by
  have h := reflection_log_4374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4375_neg : (417179 / 50000000) ≤ -Real.log (991691130591 / 1000000000000) ∧
    -Real.log (991691130591 / 1000000000000) ≤ (8343581 / 1000000000) := by
  have h := checkLog_sound (w := (8308869409 / 1991691130591)) (n := 12)
    (lo := (417179 / 50000000)) (hi := (8343581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991691130591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991691130591) = 1/(991691130591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4375 : Bounds (-8343581 / 1000000000) (-417179 / 50000000) (Real.log (991691130591 / 1000000000000)) := by
  have h := reflection_log_4375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4376_neg : (182813451 / 1000000000) ≤ -Real.log (125000000000 / 150073802301) ∧
    -Real.log (125000000000 / 150073802301) ≤ (45703363 / 250000000) := by
  have h := checkLog_sound (w := (25073802301 / 275073802301)) (n := 12)
    (lo := (182813451 / 1000000000)) (hi := (45703363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150073802301 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150073802301 / 125000000000) = 1/(125000000000 / 150073802301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4376 : Bounds (182813451 / 1000000000) (45703363 / 250000000) (Real.log (150073802301 / 125000000000)) := by
  have h := reflection_log_4376_neg
  have he : Real.log (150073802301 / 125000000000) = -Real.log (125000000000 / 150073802301) := by
    rw [show ((150073802301 / 125000000000) : ℝ) = ((125000000000 / 150073802301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4377_neg : (45820337 / 250000000) ≤ -Real.log (7812500000 / 9384002369) ∧
    -Real.log (7812500000 / 9384002369) ≤ (183281349 / 1000000000) := by
  have h := checkLog_sound (w := (1571502369 / 17196502369)) (n := 12)
    (lo := (45820337 / 250000000)) (hi := (183281349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9384002369 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9384002369 / 7812500000) = 1/(7812500000 / 9384002369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4377 : Bounds (45820337 / 250000000) (183281349 / 1000000000) (Real.log (9384002369 / 7812500000)) := by
  have h := reflection_log_4377_neg
  have he : Real.log (9384002369 / 7812500000) = -Real.log (7812500000 / 9384002369) := by
    rw [show ((9384002369 / 7812500000) : ℝ) = ((7812500000 / 9384002369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4378_neg : (36685989 / 100000000) ≤ -Real.log (500000000000 / 721597849987) ∧
    -Real.log (500000000000 / 721597849987) ≤ (366859891 / 1000000000) := by
  have h := checkLog_sound (w := (221597849987 / 1221597849987)) (n := 12)
    (lo := (36685989 / 100000000)) (hi := (366859891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721597849987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721597849987 / 500000000000) = 1/(500000000000 / 721597849987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4378 : Bounds (36685989 / 100000000) (366859891 / 1000000000) (Real.log (721597849987 / 500000000000)) := by
  have h := reflection_log_4378_neg
  have he : Real.log (721597849987 / 500000000000) = -Real.log (500000000000 / 721597849987) := by
    rw [show ((721597849987 / 500000000000) : ℝ) = ((500000000000 / 721597849987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4379_neg : (367066699 / 1000000000) ≤ -Real.log (500000000000 / 721747098351) ∧
    -Real.log (500000000000 / 721747098351) ≤ (3670667 / 10000000) := by
  have h := checkLog_sound (w := (221747098351 / 1221747098351)) (n := 12)
    (lo := (367066699 / 1000000000)) (hi := (3670667 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721747098351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721747098351 / 500000000000) = 1/(500000000000 / 721747098351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4379 : Bounds (367066699 / 1000000000) (3670667 / 10000000) (Real.log (721747098351 / 500000000000)) := by
  have h := reflection_log_4379_neg
  have he : Real.log (721747098351 / 500000000000) = -Real.log (500000000000 / 721747098351) := by
    rw [show ((721747098351 / 500000000000) : ℝ) = ((500000000000 / 721747098351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4380_neg : (41717363 / 250000000) ≤ -Real.log (1250 / 1477) ∧
    -Real.log (1250 / 1477) ≤ (166869453 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 2727)) (n := 12)
    (lo := (41717363 / 250000000)) (hi := (166869453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1477 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1477 / 1250) = 1/(1250 / 1477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4380 : Bounds (41717363 / 250000000) (166869453 / 1000000000) (Real.log (1477 / 1250)) := by
  have h := reflection_log_4380_neg
  have he : Real.log (1477 / 1250) = -Real.log (1250 / 1477) := by
    rw [show ((1477 / 1250) : ℝ) = ((1250 / 1477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4381_neg : (6262627 / 31250000) ≤ -Real.log (1023 / 1250) ∧
    -Real.log (1023 / 1250) ≤ (40080813 / 200000000) := by
  have h := checkLog_sound (w := (227 / 2273)) (n := 12)
    (lo := (6262627 / 31250000)) (hi := (40080813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1023) = 1/(1023 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4381 : Bounds (-40080813 / 200000000) (-6262627 / 31250000) (Real.log (1023 / 1250)) := by
  have h := reflection_log_4381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4382_neg : (181583 / 1000000000) ≤ -Real.log (1250000 / 1250227) ∧
    -Real.log (1250000 / 1250227) ≤ (11349 / 62500000) := by
  have h := checkLog_sound (w := (227 / 2500227)) (n := 12)
    (lo := (181583 / 1000000000)) (hi := (11349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250227 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250227 / 1250000) = 1/(1250000 / 1250227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4382 : Bounds (181583 / 1000000000) (11349 / 62500000) (Real.log (1250227 / 1250000)) := by
  have h := reflection_log_4382_neg
  have he : Real.log (1250227 / 1250000) = -Real.log (1250000 / 1250227) := by
    rw [show ((1250227 / 1250000) : ℝ) = ((1250000 / 1250227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4383_neg : (11351 / 62500000) ≤ -Real.log (1249773 / 1250000) ∧
    -Real.log (1249773 / 1250000) ≤ (181617 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 2499773)) (n := 12)
    (lo := (11351 / 62500000)) (hi := (181617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249773) = 1/(1249773 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4383 : Bounds (-181617 / 1000000000) (-11351 / 62500000) (Real.log (1249773 / 1250000)) := by
  have h := reflection_log_4383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4384_neg : (87281673 / 1000000000) ≤ -Real.log (250000 / 272801) ∧
    -Real.log (250000 / 272801) ≤ (43640837 / 500000000) := by
  have h := checkLog_sound (w := (22801 / 522801)) (n := 12)
    (lo := (87281673 / 1000000000)) (hi := (43640837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272801 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272801 / 250000) = 1/(250000 / 272801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4384 : Bounds (87281673 / 1000000000) (43640837 / 500000000) (Real.log (272801 / 250000)) := by
  have h := reflection_log_4384_neg
  have he : Real.log (272801 / 250000) = -Real.log (250000 / 272801) := by
    rw [show ((272801 / 250000) : ℝ) = ((250000 / 272801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4385_neg : (11954329 / 125000000) ≤ -Real.log (227199 / 250000) ∧
    -Real.log (227199 / 250000) ≤ (95634633 / 1000000000) := by
  have h := checkLog_sound (w := (22801 / 477199)) (n := 12)
    (lo := (11954329 / 125000000)) (hi := (95634633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227199) = 1/(227199 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4385 : Bounds (-95634633 / 1000000000) (-11954329 / 125000000) (Real.log (227199 / 250000)) := by
  have h := reflection_log_4385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4386_neg : (4374713 / 50000000) ≤ -Real.log (250000 / 272859) ∧
    -Real.log (250000 / 272859) ≤ (87494261 / 1000000000) := by
  have h := checkLog_sound (w := (22859 / 522859)) (n := 12)
    (lo := (4374713 / 50000000)) (hi := (87494261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272859 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272859 / 250000) = 1/(250000 / 272859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4386 : Bounds (4374713 / 50000000) (87494261 / 1000000000) (Real.log (272859 / 250000)) := by
  have h := reflection_log_4386_neg
  have he : Real.log (272859 / 250000) = -Real.log (250000 / 272859) := by
    rw [show ((272859 / 250000) : ℝ) = ((250000 / 272859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4387_neg : (95889947 / 1000000000) ≤ -Real.log (227141 / 250000) ∧
    -Real.log (227141 / 250000) ≤ (23972487 / 250000000) := by
  have h := checkLog_sound (w := (22859 / 477141)) (n := 12)
    (lo := (95889947 / 1000000000)) (hi := (23972487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227141) = 1/(227141 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4387 : Bounds (-23972487 / 250000000) (-95889947 / 1000000000) (Real.log (227141 / 250000)) := by
  have h := reflection_log_4387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4388_neg : (8395687 / 1000000000) ≤ -Real.log (61977466119 / 62500000000) ∧
    -Real.log (61977466119 / 62500000000) ≤ (1049461 / 125000000) := by
  have h := checkLog_sound (w := (522533881 / 124477466119)) (n := 12)
    (lo := (8395687 / 1000000000)) (hi := (1049461 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61977466119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61977466119) = 1/(61977466119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4388 : Bounds (-1049461 / 125000000) (-8395687 / 1000000000) (Real.log (61977466119 / 62500000000)) := by
  have h := reflection_log_4388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4389_neg : (4176479 / 500000000) ≤ -Real.log (61980114399 / 62500000000) ∧
    -Real.log (61980114399 / 62500000000) ≤ (8352959 / 1000000000) := by
  have h := checkLog_sound (w := (519885601 / 124480114399)) (n := 12)
    (lo := (4176479 / 500000000)) (hi := (8352959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61980114399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61980114399) = 1/(61980114399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4389 : Bounds (-8352959 / 1000000000) (-4176479 / 500000000) (Real.log (61980114399 / 62500000000)) := by
  have h := reflection_log_4389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4390_neg : (91458153 / 500000000) ≤ -Real.log (125000000000 / 150089238949) ∧
    -Real.log (125000000000 / 150089238949) ≤ (182916307 / 1000000000) := by
  have h := checkLog_sound (w := (25089238949 / 275089238949)) (n := 12)
    (lo := (91458153 / 500000000)) (hi := (182916307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150089238949 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150089238949 / 125000000000) = 1/(125000000000 / 150089238949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4390 : Bounds (91458153 / 500000000) (182916307 / 1000000000) (Real.log (150089238949 / 125000000000)) := by
  have h := reflection_log_4390_neg
  have he : Real.log (150089238949 / 125000000000) = -Real.log (125000000000 / 150089238949) := by
    rw [show ((150089238949 / 125000000000) : ℝ) = ((125000000000 / 150089238949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4391_neg : (11461513 / 62500000) ≤ -Real.log (100000000000 / 120127585949) ∧
    -Real.log (100000000000 / 120127585949) ≤ (183384209 / 1000000000) := by
  have h := checkLog_sound (w := (20127585949 / 220127585949)) (n := 12)
    (lo := (11461513 / 62500000)) (hi := (183384209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120127585949 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120127585949 / 100000000000) = 1/(100000000000 / 120127585949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4391 : Bounds (11461513 / 62500000) (183384209 / 1000000000) (Real.log (120127585949 / 100000000000)) := by
  have h := reflection_log_4391_neg
  have he : Real.log (120127585949 / 100000000000) = -Real.log (100000000000 / 120127585949) := by
    rw [show ((120127585949 / 100000000000) : ℝ) = ((100000000000 / 120127585949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4392_neg : (367066699 / 1000000000) ≤ -Real.log (10000000000 / 14434941967) ∧
    -Real.log (10000000000 / 14434941967) ≤ (3670667 / 10000000) := by
  have h := checkLog_sound (w := (4434941967 / 24434941967)) (n := 12)
    (lo := (367066699 / 1000000000)) (hi := (3670667 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14434941967 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14434941967 / 10000000000) = 1/(10000000000 / 14434941967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4392 : Bounds (367066699 / 1000000000) (3670667 / 10000000) (Real.log (14434941967 / 10000000000)) := by
  have h := reflection_log_4392_neg
  have he : Real.log (14434941967 / 10000000000) = -Real.log (10000000000 / 14434941967) := by
    rw [show ((14434941967 / 10000000000) : ℝ) = ((10000000000 / 14434941967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4393_neg : (91818379 / 250000000) ≤ -Real.log (500000000000 / 721896383187) ∧
    -Real.log (500000000000 / 721896383187) ≤ (367273517 / 1000000000) := by
  have h := checkLog_sound (w := (221896383187 / 1221896383187)) (n := 12)
    (lo := (91818379 / 250000000)) (hi := (367273517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721896383187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721896383187 / 500000000000) = 1/(500000000000 / 721896383187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4393 : Bounds (91818379 / 250000000) (367273517 / 1000000000) (Real.log (721896383187 / 500000000000)) := by
  have h := reflection_log_4393_neg
  have he : Real.log (721896383187 / 500000000000) = -Real.log (500000000000 / 721896383187) := by
    rw [show ((721896383187 / 500000000000) : ℝ) = ((500000000000 / 721896383187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4394_neg : (166954079 / 1000000000) ≤ -Real.log (10000 / 11817) ∧
    -Real.log (10000 / 11817) ≤ (1043463 / 6250000) := by
  have h := checkLog_sound (w := (1817 / 21817)) (n := 12)
    (lo := (166954079 / 1000000000)) (hi := (1043463 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817 / 10000) = 1/(10000 / 11817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4394 : Bounds (166954079 / 1000000000) (1043463 / 6250000) (Real.log (11817 / 10000)) := by
  have h := reflection_log_4394_neg
  have he : Real.log (11817 / 10000) = -Real.log (10000 / 11817) := by
    rw [show ((11817 / 10000) : ℝ) = ((10000 / 11817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4395_neg : (200526261 / 1000000000) ≤ -Real.log (8183 / 10000) ∧
    -Real.log (8183 / 10000) ≤ (100263131 / 500000000) := by
  have h := checkLog_sound (w := (1817 / 18183)) (n := 12)
    (lo := (200526261 / 1000000000)) (hi := (100263131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8183) = 1/(8183 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4395 : Bounds (-100263131 / 500000000) (-200526261 / 1000000000) (Real.log (8183 / 10000)) := by
  have h := reflection_log_4395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4396_neg : (181683 / 1000000000) ≤ -Real.log (10000000 / 10001817) ∧
    -Real.log (10000000 / 10001817) ≤ (45421 / 250000000) := by
  have h := checkLog_sound (w := (1817 / 20001817)) (n := 12)
    (lo := (181683 / 1000000000)) (hi := (45421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001817 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001817 / 10000000) = 1/(10000000 / 10001817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4396 : Bounds (181683 / 1000000000) (45421 / 250000000) (Real.log (10001817 / 10000000)) := by
  have h := reflection_log_4396_neg
  have he : Real.log (10001817 / 10000000) = -Real.log (10000000 / 10001817) := by
    rw [show ((10001817 / 10000000) : ℝ) = ((10000000 / 10001817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4397_neg : (45429 / 250000000) ≤ -Real.log (9998183 / 10000000) ∧
    -Real.log (9998183 / 10000000) ≤ (181717 / 1000000000) := by
  have h := checkLog_sound (w := (1817 / 19998183)) (n := 12)
    (lo := (45429 / 250000000)) (hi := (181717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998183) = 1/(9998183 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4397 : Bounds (-181717 / 1000000000) (-45429 / 250000000) (Real.log (9998183 / 10000000)) := by
  have h := reflection_log_4397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4398_neg : (8732841 / 100000000) ≤ -Real.log (200000 / 218251) ∧
    -Real.log (200000 / 218251) ≤ (87328411 / 1000000000) := by
  have h := checkLog_sound (w := (18251 / 418251)) (n := 12)
    (lo := (8732841 / 100000000)) (hi := (87328411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218251 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218251 / 200000) = 1/(200000 / 218251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4398 : Bounds (8732841 / 100000000) (87328411 / 1000000000) (Real.log (218251 / 200000)) := by
  have h := reflection_log_4398_neg
  have he : Real.log (218251 / 200000) = -Real.log (200000 / 218251) := by
    rw [show ((218251 / 200000) : ℝ) = ((200000 / 218251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4399_neg : (186896 / 1953125) ≤ -Real.log (181749 / 200000) ∧
    -Real.log (181749 / 200000) ≤ (95690753 / 1000000000) := by
  have h := checkLog_sound (w := (18251 / 381749)) (n := 12)
    (lo := (186896 / 1953125)) (hi := (95690753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181749) = 1/(181749 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4399 : Bounds (-95690753 / 1000000000) (-186896 / 1953125) (Real.log (181749 / 200000)) := by
  have h := reflection_log_4399_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4400_neg : (43770493 / 500000000) ≤ -Real.log (1000000 / 1091487) ∧
    -Real.log (1000000 / 1091487) ≤ (87540987 / 1000000000) := by
  have h := checkLog_sound (w := (91487 / 2091487)) (n := 12)
    (lo := (43770493 / 500000000)) (hi := (87540987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091487 / 1000000) = 1/(1000000 / 1091487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4400 : Bounds (43770493 / 500000000) (87540987 / 1000000000) (Real.log (1091487 / 1000000)) := by
  have h := reflection_log_4400_neg
  have he : Real.log (1091487 / 1000000) = -Real.log (1000000 / 1091487) := by
    rw [show ((1091487 / 1000000) : ℝ) = ((1000000 / 1091487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4401_neg : (95946081 / 1000000000) ≤ -Real.log (908513 / 1000000) ∧
    -Real.log (908513 / 1000000) ≤ (47973041 / 500000000) := by
  have h := checkLog_sound (w := (91487 / 1908513)) (n := 12)
    (lo := (95946081 / 1000000000)) (hi := (47973041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908513) = 1/(908513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4401 : Bounds (-47973041 / 500000000) (-95946081 / 1000000000) (Real.log (908513 / 1000000)) := by
  have h := reflection_log_4401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4402_neg : (1681019 / 200000000) ≤ -Real.log (991630128831 / 1000000000000) ∧
    -Real.log (991630128831 / 1000000000000) ≤ (1050637 / 125000000) := by
  have h := checkLog_sound (w := (8369871169 / 1991630128831)) (n := 12)
    (lo := (1681019 / 200000000)) (hi := (1050637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991630128831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991630128831) = 1/(991630128831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4402 : Bounds (-1050637 / 125000000) (-1681019 / 200000000) (Real.log (991630128831 / 1000000000000)) := by
  have h := reflection_log_4402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4403_neg : (4181171 / 500000000) ≤ -Real.log (39666900999 / 40000000000) ∧
    -Real.log (39666900999 / 40000000000) ≤ (8362343 / 1000000000) := by
  have h := checkLog_sound (w := (333099001 / 79666900999)) (n := 12)
    (lo := (4181171 / 500000000)) (hi := (8362343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39666900999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39666900999) = 1/(39666900999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4403 : Bounds (-8362343 / 1000000000) (-4181171 / 500000000) (Real.log (39666900999 / 40000000000)) := by
  have h := reflection_log_4403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4404_neg : (91509581 / 500000000) ≤ -Real.log (250000000000 / 300209354659) ∧
    -Real.log (250000000000 / 300209354659) ≤ (183019163 / 1000000000) := by
  have h := checkLog_sound (w := (50209354659 / 550209354659)) (n := 12)
    (lo := (91509581 / 500000000)) (hi := (183019163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300209354659 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300209354659 / 250000000000) = 1/(250000000000 / 300209354659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4404 : Bounds (91509581 / 500000000) (183019163 / 1000000000) (Real.log (300209354659 / 250000000000)) := by
  have h := reflection_log_4404_neg
  have he : Real.log (300209354659 / 250000000000) = -Real.log (250000000000 / 300209354659) := by
    rw [show ((300209354659 / 250000000000) : ℝ) = ((250000000000 / 300209354659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4405_neg : (45871767 / 250000000) ≤ -Real.log (500000000000 / 600699714809) ∧
    -Real.log (500000000000 / 600699714809) ≤ (183487069 / 1000000000) := by
  have h := checkLog_sound (w := (100699714809 / 1100699714809)) (n := 12)
    (lo := (45871767 / 250000000)) (hi := (183487069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600699714809 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600699714809 / 500000000000) = 1/(500000000000 / 600699714809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4405 : Bounds (45871767 / 250000000) (183487069 / 1000000000) (Real.log (600699714809 / 500000000000)) := by
  have h := reflection_log_4405_neg
  have he : Real.log (600699714809 / 500000000000) = -Real.log (500000000000 / 600699714809) := by
    rw [show ((600699714809 / 500000000000) : ℝ) = ((500000000000 / 600699714809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4406_neg : (91818379 / 250000000) ≤ -Real.log (250000000000 / 360948191593) ∧
    -Real.log (250000000000 / 360948191593) ≤ (367273517 / 1000000000) := by
  have h := checkLog_sound (w := (110948191593 / 610948191593)) (n := 12)
    (lo := (91818379 / 250000000)) (hi := (367273517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360948191593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360948191593 / 250000000000) = 1/(250000000000 / 360948191593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4406 : Bounds (91818379 / 250000000) (367273517 / 1000000000) (Real.log (360948191593 / 250000000000)) := by
  have h := reflection_log_4406_neg
  have he : Real.log (360948191593 / 250000000000) = -Real.log (250000000000 / 360948191593) := by
    rw [show ((360948191593 / 250000000000) : ℝ) = ((250000000000 / 360948191593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4407_neg : (367480341 / 1000000000) ≤ -Real.log (50000000000 / 72204570451) ∧
    -Real.log (50000000000 / 72204570451) ≤ (183740171 / 500000000) := by
  have h := checkLog_sound (w := (22204570451 / 122204570451)) (n := 12)
    (lo := (367480341 / 1000000000)) (hi := (183740171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72204570451 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72204570451 / 50000000000) = 1/(50000000000 / 72204570451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4407 : Bounds (367480341 / 1000000000) (183740171 / 500000000) (Real.log (72204570451 / 50000000000)) := by
  have h := reflection_log_4407_neg
  have he : Real.log (72204570451 / 50000000000) = -Real.log (50000000000 / 72204570451) := by
    rw [show ((72204570451 / 50000000000) : ℝ) = ((50000000000 / 72204570451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4408_neg : (167038699 / 1000000000) ≤ -Real.log (5000 / 5909) ∧
    -Real.log (5000 / 5909) ≤ (1670387 / 10000000) := by
  have h := checkLog_sound (w := (909 / 10909)) (n := 12)
    (lo := (167038699 / 1000000000)) (hi := (1670387 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5909 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5909 / 5000) = 1/(5000 / 5909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4408 : Bounds (167038699 / 1000000000) (1670387 / 10000000) (Real.log (5909 / 5000)) := by
  have h := reflection_log_4408_neg
  have he : Real.log (5909 / 5000) = -Real.log (5000 / 5909) := by
    rw [show ((5909 / 5000) : ℝ) = ((5000 / 5909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4409_neg : (200648473 / 1000000000) ≤ -Real.log (4091 / 5000) ∧
    -Real.log (4091 / 5000) ≤ (100324237 / 500000000) := by
  have h := checkLog_sound (w := (909 / 9091)) (n := 12)
    (lo := (200648473 / 1000000000)) (hi := (100324237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4091) = 1/(4091 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4409 : Bounds (-100324237 / 500000000) (-200648473 / 1000000000) (Real.log (4091 / 5000)) := by
  have h := reflection_log_4409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4410_neg : (181783 / 1000000000) ≤ -Real.log (5000000 / 5000909) ∧
    -Real.log (5000000 / 5000909) ≤ (22723 / 125000000) := by
  have h := checkLog_sound (w := (909 / 10000909)) (n := 12)
    (lo := (181783 / 1000000000)) (hi := (22723 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000909 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000909 / 5000000) = 1/(5000000 / 5000909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4410 : Bounds (181783 / 1000000000) (22723 / 125000000) (Real.log (5000909 / 5000000)) := by
  have h := reflection_log_4410_neg
  have he : Real.log (5000909 / 5000000) = -Real.log (5000000 / 5000909) := by
    rw [show ((5000909 / 5000000) : ℝ) = ((5000000 / 5000909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4411_neg : (22727 / 125000000) ≤ -Real.log (4999091 / 5000000) ∧
    -Real.log (4999091 / 5000000) ≤ (181817 / 1000000000) := by
  have h := checkLog_sound (w := (909 / 9999091)) (n := 12)
    (lo := (22727 / 125000000)) (hi := (181817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999091) = 1/(4999091 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4411 : Bounds (-181817 / 1000000000) (-22727 / 125000000) (Real.log (4999091 / 5000000)) := by
  have h := reflection_log_4411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4412_neg : (87374227 / 1000000000) ≤ -Real.log (200000 / 218261) ∧
    -Real.log (200000 / 218261) ≤ (21843557 / 250000000) := by
  have h := checkLog_sound (w := (18261 / 418261)) (n := 12)
    (lo := (87374227 / 1000000000)) (hi := (21843557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218261 / 200000) = 1/(200000 / 218261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4412 : Bounds (87374227 / 1000000000) (21843557 / 250000000) (Real.log (218261 / 200000)) := by
  have h := reflection_log_4412_neg
  have he : Real.log (218261 / 200000) = -Real.log (200000 / 218261) := by
    rw [show ((218261 / 200000) : ℝ) = ((200000 / 218261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4413_neg : (47872887 / 500000000) ≤ -Real.log (181739 / 200000) ∧
    -Real.log (181739 / 200000) ≤ (3829831 / 40000000) := by
  have h := checkLog_sound (w := (18261 / 381739)) (n := 12)
    (lo := (47872887 / 500000000)) (hi := (3829831 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181739) = 1/(181739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4413 : Bounds (-3829831 / 40000000) (-47872887 / 500000000) (Real.log (181739 / 200000)) := by
  have h := reflection_log_4413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4414_neg : (8758771 / 100000000) ≤ -Real.log (500000 / 545769) ∧
    -Real.log (500000 / 545769) ≤ (87587711 / 1000000000) := by
  have h := checkLog_sound (w := (45769 / 1045769)) (n := 12)
    (lo := (8758771 / 100000000)) (hi := (87587711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545769 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545769 / 500000) = 1/(500000 / 545769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4414 : Bounds (8758771 / 100000000) (87587711 / 1000000000) (Real.log (545769 / 500000)) := by
  have h := reflection_log_4414_neg
  have he : Real.log (545769 / 500000) = -Real.log (500000 / 545769) := by
    rw [show ((545769 / 500000) : ℝ) = ((500000 / 545769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4415_neg : (96002219 / 1000000000) ≤ -Real.log (454231 / 500000) ∧
    -Real.log (454231 / 500000) ≤ (4800111 / 50000000) := by
  have h := checkLog_sound (w := (45769 / 954231)) (n := 12)
    (lo := (96002219 / 1000000000)) (hi := (4800111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454231) = 1/(454231 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4415 : Bounds (-4800111 / 50000000) (-96002219 / 1000000000) (Real.log (454231 / 500000)) := by
  have h := reflection_log_4415_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
