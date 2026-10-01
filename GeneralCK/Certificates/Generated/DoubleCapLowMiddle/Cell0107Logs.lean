import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0107
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

theorem reflection_log_1_neg : (335040221 / 500000000) ≤ -Real.log (10240 / 20013) ∧
    -Real.log (10240 / 20013) ≤ (670080443 / 1000000000) := by
  have h := checkLog_sound (w := (9773 / 30253)) (n := 12)
    (lo := (335040221 / 500000000)) (hi := (670080443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 10240) = 1/(10240 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335040221 / 500000000) (670080443 / 1000000000) (Real.log (20013 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20013 / 10240) = -Real.log (10240 / 20013) := by
    rw [show ((20013 / 10240) : ℝ) = ((10240 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1543863819 / 500000000) ≤ -Real.log (467 / 10240) ∧
    -Real.log (467 / 10240) ≤ (3087727643 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 467) = 1/(467 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3087727643 / 1000000000) (-1543863819 / 500000000) (Real.log (467 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167472637 / 250000000) ≤ -Real.log (25600 / 50023) ∧
    -Real.log (25600 / 50023) ≤ (669890549 / 1000000000) := by
  have h := checkLog_sound (w := (24423 / 75623)) (n := 12)
    (lo := (167472637 / 250000000)) (hi := (669890549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 25600) = 1/(25600 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167472637 / 250000000) (669890549 / 1000000000) (Real.log (50023 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50023 / 25600) = -Real.log (25600 / 50023) := by
    rw [show ((50023 / 25600) : ℝ) = ((25600 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19247647 / 6250000) ≤ -Real.log (1177 / 25600) ∧
    -Real.log (1177 / 25600) ≤ (123184941 / 40000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1177) = 1/(1177 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-123184941 / 40000000) (-19247647 / 6250000) (Real.log (1177 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (323234521 / 500000000) ≤ -Real.log (5120 / 9773) ∧
    -Real.log (5120 / 9773) ≤ (646469043 / 1000000000) := by
  have h := checkLog_sound (w := (4653 / 14893)) (n := 12)
    (lo := (323234521 / 500000000)) (hi := (646469043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9773 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9773 / 5120) = 1/(5120 / 9773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (323234521 / 500000000) (646469043 / 1000000000) (Real.log (9773 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9773 / 5120) = -Real.log (5120 / 9773) := by
    rw [show ((9773 / 5120) : ℝ) = ((5120 / 9773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1197290229 / 500000000) ≤ -Real.log (467 / 5120) ∧
    -Real.log (467 / 5120) ≤ (1197290231 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 467) = 1/(467 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1197290231 / 500000000) (-1197290229 / 500000000) (Real.log (467 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (32304007 / 50000000) ≤ -Real.log (12800 / 24423) ∧
    -Real.log (12800 / 24423) ≤ (646080141 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 37223)) (n := 12)
    (lo := (32304007 / 50000000)) (hi := (646080141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24423 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24423 / 12800) = 1/(12800 / 24423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (32304007 / 50000000) (646080141 / 1000000000) (Real.log (24423 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24423 / 12800) = -Real.log (12800 / 24423) := by
    rw [show ((24423 / 12800) : ℝ) = ((12800 / 24423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119323817 / 50000000) ≤ -Real.log (1177 / 12800) ∧
    -Real.log (1177 / 12800) ≤ (298309543 / 125000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1177) = 1/(1177 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-298309543 / 125000000) (-119323817 / 50000000) (Real.log (1177 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42136851 / 62500000) ≤ -Real.log (500000 / 981221) ∧
    -Real.log (500000 / 981221) ≤ (674189617 / 1000000000) := by
  have h := checkLog_sound (w := (481221 / 1481221)) (n := 12)
    (lo := (42136851 / 62500000)) (hi := (674189617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981221 / 500000) = 1/(500000 / 981221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42136851 / 62500000) (674189617 / 1000000000) (Real.log (981221 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981221 / 500000) = -Real.log (500000 / 981221) := by
    rw [show ((981221 / 500000) : ℝ) = ((500000 / 981221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3281868871 / 1000000000) ≤ -Real.log (18779 / 500000) ∧
    -Real.log (18779 / 500000) ≤ (820467219 / 250000000) := by
  have h := checkLog_sound (w := (12471 / 50029)) (n := 12)
    (lo := (509280151 / 1000000000)) (hi := (63660019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18779) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18779) = 1/(18779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-820467219 / 250000000) (-3281868871 / 1000000000) (Real.log (18779 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (337167671 / 500000000) ≤ -Real.log (125000 / 245341) ∧
    -Real.log (125000 / 245341) ≤ (674335343 / 1000000000) := by
  have h := checkLog_sound (w := (120341 / 370341)) (n := 12)
    (lo := (337167671 / 500000000)) (hi := (674335343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245341 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245341 / 125000) = 1/(125000 / 245341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (337167671 / 500000000) (674335343 / 1000000000) (Real.log (245341 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (245341 / 125000) = -Real.log (125000 / 245341) := by
    rw [show ((245341 / 125000) : ℝ) = ((125000 / 245341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1644756451 / 500000000) ≤ -Real.log (4659 / 125000) ∧
    -Real.log (4659 / 125000) ≤ (3289512907 / 1000000000) := by
  have h := checkLog_sound (w := (6307 / 24943)) (n := 12)
    (lo := (258462091 / 500000000)) (hi := (516924183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9318) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9318) = 1/(4659 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3289512907 / 1000000000) (-1644756451 / 500000000) (Real.log (4659 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21062103 / 31250000) ≤ -Real.log (200000 / 392409) ∧
    -Real.log (200000 / 392409) ≤ (673987297 / 1000000000) := by
  have h := checkLog_sound (w := (192409 / 592409)) (n := 12)
    (lo := (21062103 / 31250000)) (hi := (673987297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392409 / 200000) = 1/(200000 / 392409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21062103 / 31250000) (673987297 / 1000000000) (Real.log (392409 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (392409 / 200000) = -Real.log (200000 / 392409) := by
    rw [show ((392409 / 200000) : ℝ) = ((200000 / 392409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3271354029 / 1000000000) ≤ -Real.log (7591 / 200000) ∧
    -Real.log (7591 / 200000) ≤ (1635677017 / 500000000) := by
  have h := checkLog_sound (w := (4909 / 20091)) (n := 12)
    (lo := (498765309 / 1000000000)) (hi := (49876531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7591) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7591) = 1/(7591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1635677017 / 500000000) (-3271354029 / 1000000000) (Real.log (7591 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674136619 / 1000000000) ≤ -Real.log (500000 / 981169) ∧
    -Real.log (500000 / 981169) ≤ (33706831 / 50000000) := by
  have h := checkLog_sound (w := (481169 / 1481169)) (n := 12)
    (lo := (674136619 / 1000000000)) (hi := (33706831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981169 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981169 / 500000) = 1/(500000 / 981169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674136619 / 1000000000) (33706831 / 50000000) (Real.log (981169 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981169 / 500000) = -Real.log (500000 / 981169) := by
    rw [show ((981169 / 500000) : ℝ) = ((500000 / 981169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (102471989 / 31250000) ≤ -Real.log (18831 / 500000) ∧
    -Real.log (18831 / 500000) ≤ (3279103653 / 1000000000) := by
  have h := checkLog_sound (w := (12419 / 50081)) (n := 12)
    (lo := (31657183 / 62500000)) (hi := (506514929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18831) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18831) = 1/(18831 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3279103653 / 1000000000) (-102471989 / 31250000) (Real.log (18831 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3956058487 / 1000000000) ≤ -Real.log (500000000000 / 26125485915117) ∧
    -Real.log (500000000000 / 26125485915117) ≤ (3956058493 / 1000000000) := by
  have h := checkLog_sound (w := (10125485915117 / 42125485915117)) (n := 12)
    (lo := (490322587 / 1000000000)) (hi := (122580647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26125485915117 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26125485915117 / 16000000000000) = 1/(500000000000 / 26125485915117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3956058487 / 1000000000) (3956058493 / 1000000000) (Real.log (26125485915117 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26125485915117 / 500000000000) = -Real.log (500000000000 / 26125485915117) := by
    rw [show ((26125485915117 / 500000000000) : ℝ) = ((500000000000 / 26125485915117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3963848243 / 1000000000) ≤ -Real.log (31250000000 / 1645611987551) ∧
    -Real.log (31250000000 / 1645611987551) ≤ (3963848249 / 1000000000) := by
  have h := checkLog_sound (w := (645611987551 / 2645611987551)) (n := 12)
    (lo := (498112343 / 1000000000)) (hi := (62264043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645611987551 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1645611987551 / 1000000000000) = 1/(31250000000 / 1645611987551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3963848243 / 1000000000) (3963848249 / 1000000000) (Real.log (1645611987551 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1645611987551 / 31250000000) = -Real.log (31250000000 / 1645611987551) := by
    rw [show ((1645611987551 / 31250000000) : ℝ) = ((31250000000 / 1645611987551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (157813653 / 40000000) ≤ -Real.log (62500000000 / 3230873732051) ∧
    -Real.log (62500000000 / 3230873732051) ≤ (3945341331 / 1000000000) := by
  have h := checkLog_sound (w := (1230873732051 / 5230873732051)) (n := 12)
    (lo := (19184217 / 40000000)) (hi := (239802713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3230873732051 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3230873732051 / 2000000000000) = 1/(62500000000 / 3230873732051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (157813653 / 40000000) (3945341331 / 1000000000) (Real.log (3230873732051 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3230873732051 / 62500000000) = -Real.log (62500000000 / 3230873732051) := by
    rw [show ((3230873732051 / 62500000000) : ℝ) = ((62500000000 / 3230873732051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3953240267 / 1000000000) ≤ -Real.log (250000000000 / 13025981095003) ∧
    -Real.log (250000000000 / 13025981095003) ≤ (3953240273 / 1000000000) := by
  have h := checkLog_sound (w := (5025981095003 / 21025981095003)) (n := 12)
    (lo := (487504367 / 1000000000)) (hi := (30469023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13025981095003 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13025981095003 / 8000000000000) = 1/(250000000000 / 13025981095003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3953240267 / 1000000000) (3953240273 / 1000000000) (Real.log (13025981095003 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13025981095003 / 250000000000) = -Real.log (250000000000 / 13025981095003) := by
    rw [show ((13025981095003 / 250000000000) : ℝ) = ((250000000000 / 13025981095003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0107
