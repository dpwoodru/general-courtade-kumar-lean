import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0320
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

theorem reflection_log_1_neg : (219229651 / 1000000000) ≤ -Real.log (1024 / 1275) ∧
    -Real.log (1024 / 1275) ≤ (54807413 / 250000000) := by
  have h := checkLog_sound (w := (251 / 2299)) (n := 12)
    (lo := (219229651 / 1000000000)) (hi := (54807413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275 / 1024) = 1/(1024 / 1275) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (219229651 / 1000000000) (54807413 / 250000000) (Real.log (1275 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1275 / 1024) = -Real.log (1024 / 1275) := by
    rw [show ((1275 / 1024) : ℝ) = ((1024 / 1275) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (281192757 / 1000000000) ≤ -Real.log (773 / 1024) ∧
    -Real.log (773 / 1024) ≤ (140596379 / 500000000) := by
  have h := checkLog_sound (w := (251 / 1797)) (n := 12)
    (lo := (281192757 / 1000000000)) (hi := (140596379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 773) = 1/(773 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140596379 / 500000000) (-281192757 / 1000000000) (Real.log (773 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21899433 / 100000000) ≤ -Real.log (10240 / 12747) ∧
    -Real.log (10240 / 12747) ≤ (218994331 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 22987)) (n := 12)
    (lo := (21899433 / 100000000)) (hi := (218994331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12747 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12747 / 10240) = 1/(10240 / 12747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21899433 / 100000000) (218994331 / 1000000000) (Real.log (12747 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12747 / 10240) = -Real.log (10240 / 12747) := by
    rw [show ((12747 / 10240) : ℝ) = ((10240 / 12747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280804733 / 1000000000) ≤ -Real.log (7733 / 10240) ∧
    -Real.log (7733 / 10240) ≤ (140402367 / 500000000) := by
  have h := checkLog_sound (w := (2507 / 17973)) (n := 12)
    (lo := (280804733 / 1000000000)) (hi := (140402367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7733) = 1/(7733 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140402367 / 500000000) (-280804733 / 1000000000) (Real.log (7733 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199466703 / 500000000) ≤ -Real.log (512 / 763) ∧
    -Real.log (512 / 763) ≤ (398933407 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1275)) (n := 12)
    (lo := (199466703 / 500000000)) (hi := (398933407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763 / 512) = 1/(512 / 763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199466703 / 500000000) (398933407 / 1000000000) (Real.log (763 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (763 / 512) = -Real.log (512 / 763) := by
    rw [show ((763 / 512) : ℝ) = ((512 / 763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (673804217 / 1000000000) ≤ -Real.log (261 / 512) ∧
    -Real.log (261 / 512) ≤ (336902109 / 500000000) := by
  have h := checkLog_sound (w := (251 / 773)) (n := 12)
    (lo := (673804217 / 1000000000)) (hi := (336902109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 261) = 1/(261 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-336902109 / 500000000) (-673804217 / 1000000000) (Real.log (261 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24908759 / 62500000) ≤ -Real.log (5120 / 7627) ∧
    -Real.log (5120 / 7627) ≤ (79708029 / 200000000) := by
  have h := checkLog_sound (w := (2507 / 12747)) (n := 12)
    (lo := (24908759 / 62500000)) (hi := (79708029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7627 / 5120) = 1/(5120 / 7627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24908759 / 62500000) (79708029 / 200000000) (Real.log (7627 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7627 / 5120) = -Real.log (5120 / 7627) := by
    rw [show ((7627 / 5120) : ℝ) = ((5120 / 7627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (168163863 / 250000000) ≤ -Real.log (2613 / 5120) ∧
    -Real.log (2613 / 5120) ≤ (672655453 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 7733)) (n := 12)
    (lo := (168163863 / 250000000)) (hi := (672655453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2613) = 1/(2613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-672655453 / 1000000000) (-168163863 / 250000000) (Real.log (2613 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12006791 / 40000000) ≤ -Real.log (125000 / 168761) ∧
    -Real.log (125000 / 168761) ≤ (18760611 / 62500000) := by
  have h := checkLog_sound (w := (43761 / 293761)) (n := 12)
    (lo := (12006791 / 40000000)) (hi := (18760611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168761 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168761 / 125000) = 1/(125000 / 168761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12006791 / 40000000) (18760611 / 62500000) (Real.log (168761 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (168761 / 125000) = -Real.log (125000 / 168761) := by
    rw [show ((168761 / 125000) : ℝ) = ((125000 / 168761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (430918309 / 1000000000) ≤ -Real.log (81239 / 125000) ∧
    -Real.log (81239 / 125000) ≤ (43091831 / 100000000) := by
  have h := checkLog_sound (w := (43761 / 206239)) (n := 12)
    (lo := (430918309 / 1000000000)) (hi := (43091831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 81239) = 1/(81239 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43091831 / 100000000) (-430918309 / 1000000000) (Real.log (81239 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (300488963 / 1000000000) ≤ -Real.log (1000000 / 1350519) ∧
    -Real.log (1000000 / 1350519) ≤ (75122241 / 250000000) := by
  have h := checkLog_sound (w := (350519 / 2350519)) (n := 12)
    (lo := (300488963 / 1000000000)) (hi := (75122241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350519 / 1000000) = 1/(1000000 / 1350519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (300488963 / 1000000000) (75122241 / 250000000) (Real.log (1350519 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1350519 / 1000000) = -Real.log (1000000 / 1350519) := by
    rw [show ((1350519 / 1000000) : ℝ) = ((1000000 / 1350519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (842933 / 1953125) ≤ -Real.log (649481 / 1000000) ∧
    -Real.log (649481 / 1000000) ≤ (431581697 / 1000000000) := by
  have h := checkLog_sound (w := (350519 / 1649481)) (n := 12)
    (lo := (842933 / 1953125)) (hi := (431581697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649481) = 1/(649481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-431581697 / 1000000000) (-842933 / 1953125) (Real.log (649481 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7128823 / 31250000) ≤ -Real.log (1000000 / 1256239) ∧
    -Real.log (1000000 / 1256239) ≤ (228122337 / 1000000000) := by
  have h := checkLog_sound (w := (256239 / 2256239)) (n := 12)
    (lo := (7128823 / 31250000)) (hi := (228122337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256239 / 1000000) = 1/(1000000 / 1256239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7128823 / 31250000) (228122337 / 1000000000) (Real.log (1256239 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1256239 / 1000000) = -Real.log (1000000 / 1256239) := by
    rw [show ((1256239 / 1000000) : ℝ) = ((1000000 / 1256239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74008883 / 250000000) ≤ -Real.log (743761 / 1000000) ∧
    -Real.log (743761 / 1000000) ≤ (296035533 / 1000000000) := by
  have h := checkLog_sound (w := (256239 / 1743761)) (n := 12)
    (lo := (74008883 / 250000000)) (hi := (296035533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743761) = 1/(743761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296035533 / 1000000000) (-74008883 / 250000000) (Real.log (743761 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (228390561 / 1000000000) ≤ -Real.log (15625 / 19634) ∧
    -Real.log (15625 / 19634) ≤ (114195281 / 500000000) := by
  have h := checkLog_sound (w := (4009 / 35259)) (n := 12)
    (lo := (228390561 / 1000000000)) (hi := (114195281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19634 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19634 / 15625) = 1/(15625 / 19634) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (228390561 / 1000000000) (114195281 / 500000000) (Real.log (19634 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19634 / 15625) = -Real.log (15625 / 19634) := by
    rw [show ((19634 / 15625) : ℝ) = ((15625 / 19634) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (296488737 / 1000000000) ≤ -Real.log (11616 / 15625) ∧
    -Real.log (11616 / 15625) ≤ (148244369 / 500000000) := by
  have h := checkLog_sound (w := (4009 / 27241)) (n := 12)
    (lo := (296488737 / 1000000000)) (hi := (148244369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11616) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11616) = 1/(11616 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-148244369 / 500000000) (-296488737 / 1000000000) (Real.log (11616 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (182772021 / 250000000) ≤ -Real.log (500000000000 / 1038669850687) ∧
    -Real.log (500000000000 / 1038669850687) ≤ (365544043 / 500000000) := by
  have h := checkLog_sound (w := (38669850687 / 2038669850687)) (n := 12)
    (lo := (4742613 / 125000000)) (hi := (7588181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038669850687 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038669850687 / 1000000000000) = 1/(500000000000 / 1038669850687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (182772021 / 250000000) (365544043 / 500000000) (Real.log (1038669850687 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1038669850687 / 500000000000) = -Real.log (500000000000 / 1038669850687) := by
    rw [show ((1038669850687 / 500000000000) : ℝ) = ((500000000000 / 1038669850687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (732070659 / 1000000000) ≤ -Real.log (100000000000 / 207938184489) ∧
    -Real.log (100000000000 / 207938184489) ≤ (732070661 / 1000000000) := by
  have h := checkLog_sound (w := (7938184489 / 407938184489)) (n := 12)
    (lo := (38923479 / 1000000000)) (hi := (973087 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207938184489 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207938184489 / 200000000000) = 1/(100000000000 / 207938184489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (732070659 / 1000000000) (732070661 / 1000000000) (Real.log (207938184489 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (207938184489 / 100000000000) = -Real.log (100000000000 / 207938184489) := by
    rw [show ((207938184489 / 100000000000) : ℝ) = ((100000000000 / 207938184489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (131039467 / 250000000) ≤ -Real.log (250000000000 / 422258964909) ∧
    -Real.log (250000000000 / 422258964909) ≤ (524157869 / 1000000000) := by
  have h := checkLog_sound (w := (172258964909 / 672258964909)) (n := 12)
    (lo := (131039467 / 250000000)) (hi := (524157869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422258964909 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422258964909 / 250000000000) = 1/(250000000000 / 422258964909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (131039467 / 250000000) (524157869 / 1000000000) (Real.log (422258964909 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (422258964909 / 250000000000) = -Real.log (250000000000 / 422258964909) := by
    rw [show ((422258964909 / 250000000000) : ℝ) = ((250000000000 / 422258964909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524879299 / 1000000000) ≤ -Real.log (500000000000 / 845127410469) ∧
    -Real.log (500000000000 / 845127410469) ≤ (5248793 / 10000000) := by
  have h := checkLog_sound (w := (345127410469 / 1345127410469)) (n := 12)
    (lo := (524879299 / 1000000000)) (hi := (5248793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845127410469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845127410469 / 500000000000) = 1/(500000000000 / 845127410469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524879299 / 1000000000) (5248793 / 10000000) (Real.log (845127410469 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (845127410469 / 500000000000) = -Real.log (500000000000 / 845127410469) := by
    rw [show ((845127410469 / 500000000000) : ℝ) = ((500000000000 / 845127410469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0320
