import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7808_neg : (468378933 / 1000000000) ≤ -Real.log (250000000000 / 399350649351) ∧
    -Real.log (250000000000 / 399350649351) ≤ (234189467 / 500000000) := by
  have h := checkLog_sound (w := (149350649351 / 649350649351)) (n := 12)
    (lo := (468378933 / 1000000000)) (hi := (234189467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399350649351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399350649351 / 250000000000) = 1/(250000000000 / 399350649351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7808 : Bounds (468378933 / 1000000000) (234189467 / 500000000) (Real.log (399350649351 / 250000000000)) := by
  have h := reflection_log_7808_neg
  have he : Real.log (399350649351 / 250000000000) = -Real.log (250000000000 / 399350649351) := by
    rw [show ((399350649351 / 250000000000) : ℝ) = ((250000000000 / 399350649351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7809_neg : (20742059 / 100000000) ≤ -Real.log (2000 / 2461) ∧
    -Real.log (2000 / 2461) ≤ (207420591 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 4461)) (n := 12)
    (lo := (20742059 / 100000000)) (hi := (207420591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 2000) = 1/(2000 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7809 : Bounds (20742059 / 100000000) (207420591 / 1000000000) (Real.log (2461 / 2000)) := by
  have h := reflection_log_7809_neg
  have he : Real.log (2461 / 2000) = -Real.log (2000 / 2461) := by
    rw [show ((2461 / 2000) : ℝ) = ((2000 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7810_neg : (10480573 / 40000000) ≤ -Real.log (1539 / 2000) ∧
    -Real.log (1539 / 2000) ≤ (131007163 / 500000000) := by
  have h := checkLog_sound (w := (461 / 3539)) (n := 12)
    (lo := (10480573 / 40000000)) (hi := (131007163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1539) = 1/(1539 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7810 : Bounds (-131007163 / 500000000) (-10480573 / 40000000) (Real.log (1539 / 2000)) := by
  have h := reflection_log_7810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7811_neg : (230473 / 1000000000) ≤ -Real.log (2000000 / 2000461) ∧
    -Real.log (2000000 / 2000461) ≤ (115237 / 500000000) := by
  have h := checkLog_sound (w := (461 / 4000461)) (n := 12)
    (lo := (230473 / 1000000000)) (hi := (115237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000461 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000461 / 2000000) = 1/(2000000 / 2000461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7811 : Bounds (230473 / 1000000000) (115237 / 500000000) (Real.log (2000461 / 2000000)) := by
  have h := reflection_log_7811_neg
  have he : Real.log (2000461 / 2000000) = -Real.log (2000000 / 2000461) := by
    rw [show ((2000461 / 2000000) : ℝ) = ((2000000 / 2000461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7812_neg : (115263 / 500000000) ≤ -Real.log (1999539 / 2000000) ∧
    -Real.log (1999539 / 2000000) ≤ (230527 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3999539)) (n := 12)
    (lo := (115263 / 500000000)) (hi := (230527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999539) = 1/(1999539 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7812 : Bounds (-230527 / 1000000000) (-115263 / 500000000) (Real.log (1999539 / 2000000)) := by
  have h := reflection_log_7812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7813_neg : (109750863 / 1000000000) ≤ -Real.log (250 / 279) ∧
    -Real.log (250 / 279) ≤ (6859429 / 62500000) := by
  have h := checkLog_sound (w := (29 / 529)) (n := 12)
    (lo := (109750863 / 1000000000)) (hi := (6859429 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279 / 250) = 1/(250 / 279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7813 : Bounds (109750863 / 1000000000) (6859429 / 62500000) (Real.log (279 / 250)) := by
  have h := reflection_log_7813_neg
  have he : Real.log (279 / 250) = -Real.log (250 / 279) := by
    rw [show ((279 / 250) : ℝ) = ((250 / 279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7814_neg : (15412277 / 125000000) ≤ -Real.log (221 / 250) ∧
    -Real.log (221 / 250) ≤ (123298217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 471)) (n := 12)
    (lo := (15412277 / 125000000)) (hi := (123298217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 221) = 1/(221 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7814 : Bounds (-123298217 / 1000000000) (-15412277 / 125000000) (Real.log (221 / 250)) := by
  have h := reflection_log_7814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7815_neg : (110186253 / 1000000000) ≤ -Real.log (500000 / 558243) ∧
    -Real.log (500000 / 558243) ≤ (55093127 / 500000000) := by
  have h := checkLog_sound (w := (58243 / 1058243)) (n := 12)
    (lo := (110186253 / 1000000000)) (hi := (55093127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558243 / 500000) = 1/(500000 / 558243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7815 : Bounds (110186253 / 1000000000) (55093127 / 500000000) (Real.log (558243 / 500000)) := by
  have h := reflection_log_7815_neg
  have he : Real.log (558243 / 500000) = -Real.log (500000 / 558243) := by
    rw [show ((558243 / 500000) : ℝ) = ((500000 / 558243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7816_neg : (123848141 / 1000000000) ≤ -Real.log (441757 / 500000) ∧
    -Real.log (441757 / 500000) ≤ (61924071 / 500000000) := by
  have h := checkLog_sound (w := (58243 / 941757)) (n := 12)
    (lo := (123848141 / 1000000000)) (hi := (61924071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441757) = 1/(441757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7816 : Bounds (-61924071 / 500000000) (-123848141 / 1000000000) (Real.log (441757 / 500000)) := by
  have h := reflection_log_7816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7817_neg : (213467 / 15625000) ≤ -Real.log (246607752951 / 250000000000) ∧
    -Real.log (246607752951 / 250000000000) ≤ (13661889 / 1000000000) := by
  have h := checkLog_sound (w := (3392247049 / 496607752951)) (n := 12)
    (lo := (213467 / 15625000)) (hi := (13661889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246607752951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246607752951) = 1/(246607752951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7817 : Bounds (-13661889 / 1000000000) (-213467 / 15625000) (Real.log (246607752951 / 250000000000)) := by
  have h := reflection_log_7817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7818_neg : (1693419 / 125000000) ≤ -Real.log (61659 / 62500) ∧
    -Real.log (61659 / 62500) ≤ (13547353 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 124159)) (n := 12)
    (lo := (1693419 / 125000000)) (hi := (13547353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 61659) = 1/(61659 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7818 : Bounds (-13547353 / 1000000000) (-1693419 / 125000000) (Real.log (61659 / 62500)) := by
  have h := reflection_log_7818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7819_neg : (5826227 / 25000000) ≤ -Real.log (500000000000 / 631221719457) ∧
    -Real.log (500000000000 / 631221719457) ≤ (233049081 / 1000000000) := by
  have h := checkLog_sound (w := (131221719457 / 1131221719457)) (n := 12)
    (lo := (5826227 / 25000000)) (hi := (233049081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631221719457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631221719457 / 500000000000) = 1/(500000000000 / 631221719457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7819 : Bounds (5826227 / 25000000) (233049081 / 1000000000) (Real.log (631221719457 / 500000000000)) := by
  have h := reflection_log_7819_neg
  have he : Real.log (631221719457 / 500000000000) = -Real.log (500000000000 / 631221719457) := by
    rw [show ((631221719457 / 500000000000) : ℝ) = ((500000000000 / 631221719457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7820_neg : (117017197 / 500000000) ≤ -Real.log (125000000000 / 157960994393) ∧
    -Real.log (125000000000 / 157960994393) ≤ (46806879 / 200000000) := by
  have h := checkLog_sound (w := (32960994393 / 282960994393)) (n := 12)
    (lo := (117017197 / 500000000)) (hi := (46806879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157960994393 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157960994393 / 125000000000) = 1/(125000000000 / 157960994393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7820 : Bounds (117017197 / 500000000) (46806879 / 200000000) (Real.log (157960994393 / 125000000000)) := by
  have h := reflection_log_7820_neg
  have he : Real.log (157960994393 / 125000000000) = -Real.log (125000000000 / 157960994393) := by
    rw [show ((157960994393 / 125000000000) : ℝ) = ((125000000000 / 157960994393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7821_neg : (468378933 / 1000000000) ≤ -Real.log (500000000000 / 798701298701) ∧
    -Real.log (500000000000 / 798701298701) ≤ (234189467 / 500000000) := by
  have h := checkLog_sound (w := (298701298701 / 1298701298701)) (n := 12)
    (lo := (468378933 / 1000000000)) (hi := (234189467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798701298701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798701298701 / 500000000000) = 1/(500000000000 / 798701298701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7821 : Bounds (468378933 / 1000000000) (234189467 / 500000000) (Real.log (798701298701 / 500000000000)) := by
  have h := reflection_log_7821_neg
  have he : Real.log (798701298701 / 500000000000) = -Real.log (500000000000 / 798701298701) := by
    rw [show ((798701298701 / 500000000000) : ℝ) = ((500000000000 / 798701298701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7822_neg : (117358729 / 250000000) ≤ -Real.log (100000000000 / 159909031839) ∧
    -Real.log (100000000000 / 159909031839) ≤ (469434917 / 1000000000) := by
  have h := checkLog_sound (w := (59909031839 / 259909031839)) (n := 12)
    (lo := (117358729 / 250000000)) (hi := (469434917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159909031839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159909031839 / 100000000000) = 1/(100000000000 / 159909031839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7822 : Bounds (117358729 / 250000000) (469434917 / 1000000000) (Real.log (159909031839 / 100000000000)) := by
  have h := reflection_log_7822_neg
  have he : Real.log (159909031839 / 100000000000) = -Real.log (100000000000 / 159909031839) := by
    rw [show ((159909031839 / 100000000000) : ℝ) = ((100000000000 / 159909031839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7823_neg : (207826847 / 1000000000) ≤ -Real.log (1000 / 1231) ∧
    -Real.log (1000 / 1231) ≤ (6494589 / 31250000) := by
  have h := checkLog_sound (w := (231 / 2231)) (n := 12)
    (lo := (207826847 / 1000000000)) (hi := (6494589 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231 / 1000) = 1/(1000 / 1231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7823 : Bounds (207826847 / 1000000000) (6494589 / 31250000) (Real.log (1231 / 1000)) := by
  have h := reflection_log_7823_neg
  have he : Real.log (1231 / 1000) = -Real.log (1000 / 1231) := by
    rw [show ((1231 / 1000) : ℝ) = ((1000 / 1231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7824_neg : (262664309 / 1000000000) ≤ -Real.log (769 / 1000) ∧
    -Real.log (769 / 1000) ≤ (26266431 / 100000000) := by
  have h := checkLog_sound (w := (231 / 1769)) (n := 12)
    (lo := (262664309 / 1000000000)) (hi := (26266431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 769) = 1/(769 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7824 : Bounds (-26266431 / 100000000) (-262664309 / 1000000000) (Real.log (769 / 1000)) := by
  have h := reflection_log_7824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7825_neg : (230973 / 1000000000) ≤ -Real.log (1000000 / 1000231) ∧
    -Real.log (1000000 / 1000231) ≤ (115487 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2000231)) (n := 12)
    (lo := (230973 / 1000000000)) (hi := (115487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000231 / 1000000) = 1/(1000000 / 1000231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7825 : Bounds (230973 / 1000000000) (115487 / 500000000) (Real.log (1000231 / 1000000)) := by
  have h := reflection_log_7825_neg
  have he : Real.log (1000231 / 1000000) = -Real.log (1000000 / 1000231) := by
    rw [show ((1000231 / 1000000) : ℝ) = ((1000000 / 1000231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7826_neg : (115513 / 500000000) ≤ -Real.log (999769 / 1000000) ∧
    -Real.log (999769 / 1000000) ≤ (231027 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 1999769)) (n := 12)
    (lo := (115513 / 500000000)) (hi := (231027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999769) = 1/(999769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7826 : Bounds (-231027 / 1000000000) (-115513 / 500000000) (Real.log (999769 / 1000000)) := by
  have h := reflection_log_7826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7827_neg : (27495281 / 250000000) ≤ -Real.log (1000000 / 1116257) ∧
    -Real.log (1000000 / 1116257) ≤ (879849 / 8000000) := by
  have h := checkLog_sound (w := (116257 / 2116257)) (n := 12)
    (lo := (27495281 / 250000000)) (hi := (879849 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116257 / 1000000) = 1/(1000000 / 1116257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7827 : Bounds (27495281 / 250000000) (879849 / 8000000) (Real.log (1116257 / 1000000)) := by
  have h := reflection_log_7827_neg
  have he : Real.log (1116257 / 1000000) = -Real.log (1000000 / 1116257) := by
    rw [show ((1116257 / 1000000) : ℝ) = ((1000000 / 1116257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7828_neg : (61794491 / 500000000) ≤ -Real.log (883743 / 1000000) ∧
    -Real.log (883743 / 1000000) ≤ (123588983 / 1000000000) := by
  have h := checkLog_sound (w := (116257 / 1883743)) (n := 12)
    (lo := (61794491 / 500000000)) (hi := (123588983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883743) = 1/(883743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7828 : Bounds (-123588983 / 1000000000) (-61794491 / 500000000) (Real.log (883743 / 1000000)) := by
  have h := reflection_log_7828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7829_neg : (27604327 / 250000000) ≤ -Real.log (125000 / 139593) ∧
    -Real.log (125000 / 139593) ≤ (110417309 / 1000000000) := by
  have h := checkLog_sound (w := (14593 / 264593)) (n := 12)
    (lo := (27604327 / 250000000)) (hi := (110417309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139593 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139593 / 125000) = 1/(125000 / 139593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7829 : Bounds (27604327 / 250000000) (110417309 / 1000000000) (Real.log (139593 / 125000)) := by
  have h := reflection_log_7829_neg
  have he : Real.log (139593 / 125000) = -Real.log (125000 / 139593) := by
    rw [show ((139593 / 125000) : ℝ) = ((125000 / 139593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7830_neg : (124140199 / 1000000000) ≤ -Real.log (110407 / 125000) ∧
    -Real.log (110407 / 125000) ≤ (620701 / 5000000) := by
  have h := checkLog_sound (w := (14593 / 235407)) (n := 12)
    (lo := (124140199 / 1000000000)) (hi := (620701 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110407) = 1/(110407 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7830 : Bounds (-620701 / 5000000) (-124140199 / 1000000000) (Real.log (110407 / 125000)) := by
  have h := reflection_log_7830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7831_neg : (13722891 / 1000000000) ≤ -Real.log (15412044351 / 15625000000) ∧
    -Real.log (15412044351 / 15625000000) ≤ (3430723 / 250000000) := by
  have h := checkLog_sound (w := (212955649 / 31037044351)) (n := 12)
    (lo := (13722891 / 1000000000)) (hi := (3430723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15412044351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15412044351) = 1/(15412044351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7831 : Bounds (-3430723 / 250000000) (-13722891 / 1000000000) (Real.log (15412044351 / 15625000000)) := by
  have h := reflection_log_7831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7832_neg : (6803929 / 500000000) ≤ -Real.log (986484309951 / 1000000000000) ∧
    -Real.log (986484309951 / 1000000000000) ≤ (13607859 / 1000000000) := by
  have h := checkLog_sound (w := (13515690049 / 1986484309951)) (n := 12)
    (lo := (6803929 / 500000000)) (hi := (13607859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986484309951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986484309951) = 1/(986484309951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7832 : Bounds (-13607859 / 1000000000) (-6803929 / 500000000) (Real.log (986484309951 / 1000000000000)) := by
  have h := reflection_log_7832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7833_neg : (116785053 / 500000000) ≤ -Real.log (250000000000 / 315775344189) ∧
    -Real.log (250000000000 / 315775344189) ≤ (233570107 / 1000000000) := by
  have h := checkLog_sound (w := (65775344189 / 565775344189)) (n := 12)
    (lo := (116785053 / 500000000)) (hi := (233570107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315775344189 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315775344189 / 250000000000) = 1/(250000000000 / 315775344189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7833 : Bounds (116785053 / 500000000) (233570107 / 1000000000) (Real.log (315775344189 / 250000000000)) := by
  have h := reflection_log_7833_neg
  have he : Real.log (315775344189 / 250000000000) = -Real.log (250000000000 / 315775344189) := by
    rw [show ((315775344189 / 250000000000) : ℝ) = ((250000000000 / 315775344189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7834_neg : (58639377 / 250000000) ≤ -Real.log (25000000000 / 31608729519) ∧
    -Real.log (25000000000 / 31608729519) ≤ (234557509 / 1000000000) := by
  have h := checkLog_sound (w := (6608729519 / 56608729519)) (n := 12)
    (lo := (58639377 / 250000000)) (hi := (234557509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31608729519 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31608729519 / 25000000000) = 1/(25000000000 / 31608729519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7834 : Bounds (58639377 / 250000000) (234557509 / 1000000000) (Real.log (31608729519 / 25000000000)) := by
  have h := reflection_log_7834_neg
  have he : Real.log (31608729519 / 25000000000) = -Real.log (25000000000 / 31608729519) := by
    rw [show ((31608729519 / 25000000000) : ℝ) = ((25000000000 / 31608729519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7835_neg : (117358729 / 250000000) ≤ -Real.log (250000000000 / 399772579597) ∧
    -Real.log (250000000000 / 399772579597) ≤ (469434917 / 1000000000) := by
  have h := checkLog_sound (w := (149772579597 / 649772579597)) (n := 12)
    (lo := (117358729 / 250000000)) (hi := (469434917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399772579597 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399772579597 / 250000000000) = 1/(250000000000 / 399772579597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7835 : Bounds (117358729 / 250000000) (469434917 / 1000000000) (Real.log (399772579597 / 250000000000)) := by
  have h := reflection_log_7835_neg
  have he : Real.log (399772579597 / 250000000000) = -Real.log (250000000000 / 399772579597) := by
    rw [show ((399772579597 / 250000000000) : ℝ) = ((250000000000 / 399772579597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7836_neg : (117622789 / 250000000) ≤ -Real.log (125000000000 / 200097529259) ∧
    -Real.log (125000000000 / 200097529259) ≤ (470491157 / 1000000000) := by
  have h := checkLog_sound (w := (75097529259 / 325097529259)) (n := 12)
    (lo := (117622789 / 250000000)) (hi := (470491157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200097529259 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200097529259 / 125000000000) = 1/(125000000000 / 200097529259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7836 : Bounds (117622789 / 250000000) (470491157 / 1000000000) (Real.log (200097529259 / 125000000000)) := by
  have h := reflection_log_7836_neg
  have he : Real.log (200097529259 / 125000000000) = -Real.log (125000000000 / 200097529259) := by
    rw [show ((200097529259 / 125000000000) : ℝ) = ((125000000000 / 200097529259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7837_neg : (104116469 / 500000000) ≤ -Real.log (2000 / 2463) ∧
    -Real.log (2000 / 2463) ≤ (208232939 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4463)) (n := 12)
    (lo := (104116469 / 500000000)) (hi := (208232939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2000) = 1/(2000 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7837 : Bounds (104116469 / 500000000) (208232939 / 1000000000) (Real.log (2463 / 2000)) := by
  have h := reflection_log_7837_neg
  have he : Real.log (2463 / 2000) = -Real.log (2000 / 2463) := by
    rw [show ((2463 / 2000) : ℝ) = ((2000 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7838_neg : (65828679 / 250000000) ≤ -Real.log (1537 / 2000) ∧
    -Real.log (1537 / 2000) ≤ (263314717 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3537)) (n := 12)
    (lo := (65828679 / 250000000)) (hi := (263314717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1537) = 1/(1537 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7838 : Bounds (-263314717 / 1000000000) (-65828679 / 250000000) (Real.log (1537 / 2000)) := by
  have h := reflection_log_7838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7839_neg : (231473 / 1000000000) ≤ -Real.log (2000000 / 2000463) ∧
    -Real.log (2000000 / 2000463) ≤ (115737 / 500000000) := by
  have h := checkLog_sound (w := (463 / 4000463)) (n := 12)
    (lo := (231473 / 1000000000)) (hi := (115737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000463 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000463 / 2000000) = 1/(2000000 / 2000463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7839 : Bounds (231473 / 1000000000) (115737 / 500000000) (Real.log (2000463 / 2000000)) := by
  have h := reflection_log_7839_neg
  have he : Real.log (2000463 / 2000000) = -Real.log (2000000 / 2000463) := by
    rw [show ((2000463 / 2000000) : ℝ) = ((2000000 / 2000463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7840_neg : (115763 / 500000000) ≤ -Real.log (1999537 / 2000000) ∧
    -Real.log (1999537 / 2000000) ≤ (231527 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 3999537)) (n := 12)
    (lo := (115763 / 500000000)) (hi := (231527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999537) = 1/(1999537 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7840 : Bounds (-231527 / 1000000000) (-115763 / 500000000) (Real.log (1999537 / 2000000)) := by
  have h := reflection_log_7840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7841_neg : (110211331 / 1000000000) ≤ -Real.log (500000 / 558257) ∧
    -Real.log (500000 / 558257) ≤ (27552833 / 250000000) := by
  have h := checkLog_sound (w := (58257 / 1058257)) (n := 12)
    (lo := (110211331 / 1000000000)) (hi := (27552833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558257 / 500000) = 1/(500000 / 558257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7841 : Bounds (110211331 / 1000000000) (27552833 / 250000000) (Real.log (558257 / 500000)) := by
  have h := reflection_log_7841_neg
  have he : Real.log (558257 / 500000) = -Real.log (500000 / 558257) := by
    rw [show ((558257 / 500000) : ℝ) = ((500000 / 558257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7842_neg : (123879833 / 1000000000) ≤ -Real.log (441743 / 500000) ∧
    -Real.log (441743 / 500000) ≤ (61939917 / 500000000) := by
  have h := checkLog_sound (w := (58257 / 941743)) (n := 12)
    (lo := (123879833 / 1000000000)) (hi := (61939917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441743) = 1/(441743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7842 : Bounds (-61939917 / 500000000) (-123879833 / 1000000000) (Real.log (441743 / 500000)) := by
  have h := reflection_log_7842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7843_neg : (11064831 / 100000000) ≤ -Real.log (500000 / 558501) ∧
    -Real.log (500000 / 558501) ≤ (110648311 / 1000000000) := by
  have h := checkLog_sound (w := (58501 / 1058501)) (n := 12)
    (lo := (11064831 / 100000000)) (hi := (110648311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558501 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(558501 / 500000) = 1/(500000 / 558501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7843 : Bounds (11064831 / 100000000) (110648311 / 1000000000) (Real.log (558501 / 500000)) := by
  have h := reflection_log_7843_neg
  have he : Real.log (558501 / 500000) = -Real.log (500000 / 558501) := by
    rw [show ((558501 / 500000) : ℝ) = ((500000 / 558501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7844_neg : (124432343 / 1000000000) ≤ -Real.log (441499 / 500000) ∧
    -Real.log (441499 / 500000) ≤ (15554043 / 125000000) := by
  have h := checkLog_sound (w := (58501 / 941499)) (n := 12)
    (lo := (124432343 / 1000000000)) (hi := (15554043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 441499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 441499) = 1/(441499 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7844 : Bounds (-15554043 / 125000000) (-124432343 / 1000000000) (Real.log (441499 / 500000)) := by
  have h := reflection_log_7844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7845_neg : (430751 / 31250000) ≤ -Real.log (246577632999 / 250000000000) ∧
    -Real.log (246577632999 / 250000000000) ≤ (13784033 / 1000000000) := by
  have h := checkLog_sound (w := (3422367001 / 496577632999)) (n := 12)
    (lo := (430751 / 31250000)) (hi := (13784033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246577632999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246577632999) = 1/(246577632999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7845 : Bounds (-13784033 / 1000000000) (-430751 / 31250000) (Real.log (246577632999 / 250000000000)) := by
  have h := reflection_log_7845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7846_neg : (6834251 / 500000000) ≤ -Real.log (246606121951 / 250000000000) ∧
    -Real.log (246606121951 / 250000000000) ≤ (13668503 / 1000000000) := by
  have h := checkLog_sound (w := (3393878049 / 496606121951)) (n := 12)
    (lo := (6834251 / 500000000)) (hi := (13668503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246606121951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246606121951) = 1/(246606121951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7846 : Bounds (-13668503 / 1000000000) (-6834251 / 500000000) (Real.log (246606121951 / 250000000000)) := by
  have h := reflection_log_7846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7847_neg : (58522791 / 250000000) ≤ -Real.log (50000000000 / 63187984869) ∧
    -Real.log (50000000000 / 63187984869) ≤ (46818233 / 200000000) := by
  have h := checkLog_sound (w := (13187984869 / 113187984869)) (n := 12)
    (lo := (58522791 / 250000000)) (hi := (46818233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63187984869 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63187984869 / 50000000000) = 1/(50000000000 / 63187984869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7847 : Bounds (58522791 / 250000000) (46818233 / 200000000) (Real.log (63187984869 / 50000000000)) := by
  have h := reflection_log_7847_neg
  have he : Real.log (63187984869 / 50000000000) = -Real.log (50000000000 / 63187984869) := by
    rw [show ((63187984869 / 50000000000) : ℝ) = ((50000000000 / 63187984869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7848_neg : (235080653 / 1000000000) ≤ -Real.log (500000000000 / 632505396389) ∧
    -Real.log (500000000000 / 632505396389) ≤ (117540327 / 500000000) := by
  have h := checkLog_sound (w := (132505396389 / 1132505396389)) (n := 12)
    (lo := (235080653 / 1000000000)) (hi := (117540327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632505396389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632505396389 / 500000000000) = 1/(500000000000 / 632505396389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7848 : Bounds (235080653 / 1000000000) (117540327 / 500000000) (Real.log (632505396389 / 500000000000)) := by
  have h := reflection_log_7848_neg
  have he : Real.log (632505396389 / 500000000000) = -Real.log (500000000000 / 632505396389) := by
    rw [show ((632505396389 / 500000000000) : ℝ) = ((500000000000 / 632505396389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7849_neg : (117622789 / 250000000) ≤ -Real.log (100000000000 / 160078023407) ∧
    -Real.log (100000000000 / 160078023407) ≤ (470491157 / 1000000000) := by
  have h := checkLog_sound (w := (60078023407 / 260078023407)) (n := 12)
    (lo := (117622789 / 250000000)) (hi := (470491157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160078023407 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160078023407 / 100000000000) = 1/(100000000000 / 160078023407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7849 : Bounds (117622789 / 250000000) (470491157 / 1000000000) (Real.log (160078023407 / 100000000000)) := by
  have h := reflection_log_7849_neg
  have he : Real.log (160078023407 / 100000000000) = -Real.log (100000000000 / 160078023407) := by
    rw [show ((160078023407 / 100000000000) : ℝ) = ((100000000000 / 160078023407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7850_neg : (235773827 / 500000000) ≤ -Real.log (250000000000 / 400618087183) ∧
    -Real.log (250000000000 / 400618087183) ≤ (94309531 / 200000000) := by
  have h := checkLog_sound (w := (150618087183 / 650618087183)) (n := 12)
    (lo := (235773827 / 500000000)) (hi := (94309531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400618087183 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400618087183 / 250000000000) = 1/(250000000000 / 400618087183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7850 : Bounds (235773827 / 500000000) (94309531 / 200000000) (Real.log (400618087183 / 250000000000)) := by
  have h := reflection_log_7850_neg
  have he : Real.log (400618087183 / 250000000000) = -Real.log (250000000000 / 400618087183) := by
    rw [show ((400618087183 / 250000000000) : ℝ) = ((250000000000 / 400618087183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7851_neg : (41727773 / 200000000) ≤ -Real.log (125 / 154) ∧
    -Real.log (125 / 154) ≤ (104319433 / 500000000) := by
  have h := checkLog_sound (w := (29 / 279)) (n := 12)
    (lo := (41727773 / 200000000)) (hi := (104319433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154 / 125) = 1/(125 / 154) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7851 : Bounds (41727773 / 200000000) (104319433 / 500000000) (Real.log (154 / 125)) := by
  have h := reflection_log_7851_neg
  have he : Real.log (154 / 125) = -Real.log (125 / 154) := by
    rw [show ((154 / 125) : ℝ) = ((125 / 154) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7852_neg : (52793109 / 200000000) ≤ -Real.log (96 / 125) ∧
    -Real.log (96 / 125) ≤ (131982773 / 500000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 96) = 1/(96 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7852 : Bounds (-131982773 / 500000000) (-52793109 / 200000000) (Real.log (96 / 125)) := by
  have h := reflection_log_7852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7853_neg : (231973 / 1000000000) ≤ -Real.log (125000 / 125029) ∧
    -Real.log (125000 / 125029) ≤ (115987 / 500000000) := by
  have h := checkLog_sound (w := (29 / 250029)) (n := 12)
    (lo := (231973 / 1000000000)) (hi := (115987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125029 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125029 / 125000) = 1/(125000 / 125029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7853 : Bounds (231973 / 1000000000) (115987 / 500000000) (Real.log (125029 / 125000)) := by
  have h := reflection_log_7853_neg
  have he : Real.log (125029 / 125000) = -Real.log (125000 / 125029) := by
    rw [show ((125029 / 125000) : ℝ) = ((125000 / 125029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7854_neg : (116013 / 500000000) ≤ -Real.log (124971 / 125000) ∧
    -Real.log (124971 / 125000) ≤ (232027 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 249971)) (n := 12)
    (lo := (116013 / 500000000)) (hi := (232027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124971) = 1/(124971 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7854 : Bounds (-232027 / 1000000000) (-116013 / 500000000) (Real.log (124971 / 125000)) := by
  have h := reflection_log_7854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7855_neg : (22088297 / 200000000) ≤ -Real.log (1000000 / 1116771) ∧
    -Real.log (1000000 / 1116771) ≤ (55220743 / 500000000) := by
  have h := checkLog_sound (w := (116771 / 2116771)) (n := 12)
    (lo := (22088297 / 200000000)) (hi := (55220743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116771 / 1000000) = 1/(1000000 / 1116771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7855 : Bounds (22088297 / 200000000) (55220743 / 500000000) (Real.log (1116771 / 1000000)) := by
  have h := reflection_log_7855_neg
  have he : Real.log (1116771 / 1000000) = -Real.log (1000000 / 1116771) := by
    rw [show ((1116771 / 1000000) : ℝ) = ((1000000 / 1116771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7856_neg : (7760673 / 62500000) ≤ -Real.log (883229 / 1000000) ∧
    -Real.log (883229 / 1000000) ≤ (124170769 / 1000000000) := by
  have h := checkLog_sound (w := (116771 / 1883229)) (n := 12)
    (lo := (7760673 / 62500000)) (hi := (124170769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883229) = 1/(883229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7856 : Bounds (-124170769 / 1000000000) (-7760673 / 62500000) (Real.log (883229 / 1000000)) := by
  have h := reflection_log_7856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7857_neg : (27719591 / 250000000) ≤ -Real.log (1000000 / 1117259) ∧
    -Real.log (1000000 / 1117259) ≤ (22175673 / 200000000) := by
  have h := checkLog_sound (w := (117259 / 2117259)) (n := 12)
    (lo := (27719591 / 250000000)) (hi := (22175673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117259 / 1000000) = 1/(1000000 / 1117259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7857 : Bounds (27719591 / 250000000) (22175673 / 200000000) (Real.log (1117259 / 1000000)) := by
  have h := reflection_log_7857_neg
  have he : Real.log (1117259 / 1000000) = -Real.log (1000000 / 1117259) := by
    rw [show ((1117259 / 1000000) : ℝ) = ((1000000 / 1117259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7858_neg : (124723439 / 1000000000) ≤ -Real.log (882741 / 1000000) ∧
    -Real.log (882741 / 1000000) ≤ (1559043 / 12500000) := by
  have h := checkLog_sound (w := (117259 / 1882741)) (n := 12)
    (lo := (124723439 / 1000000000)) (hi := (1559043 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882741) = 1/(882741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7858 : Bounds (-1559043 / 12500000) (-124723439 / 1000000000) (Real.log (882741 / 1000000)) := by
  have h := reflection_log_7858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7859_neg : (553803 / 40000000) ≤ -Real.log (986250326919 / 1000000000000) ∧
    -Real.log (986250326919 / 1000000000000) ≤ (3461269 / 250000000) := by
  have h := checkLog_sound (w := (13749673081 / 1986250326919)) (n := 12)
    (lo := (553803 / 40000000)) (hi := (3461269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986250326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986250326919) = 1/(986250326919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7859 : Bounds (-3461269 / 250000000) (-553803 / 40000000) (Real.log (986250326919 / 1000000000000)) := by
  have h := reflection_log_7859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7860_neg : (13729283 / 1000000000) ≤ -Real.log (986364533559 / 1000000000000) ∧
    -Real.log (986364533559 / 1000000000000) ≤ (3432321 / 250000000) := by
  have h := checkLog_sound (w := (13635466441 / 1986364533559)) (n := 12)
    (lo := (13729283 / 1000000000)) (hi := (3432321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986364533559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986364533559) = 1/(986364533559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7860 : Bounds (-3432321 / 250000000) (-13729283 / 1000000000) (Real.log (986364533559 / 1000000000000)) := by
  have h := reflection_log_7860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7861_neg : (117306127 / 500000000) ≤ -Real.log (250000000000 / 316104600279) ∧
    -Real.log (250000000000 / 316104600279) ≤ (46922451 / 200000000) := by
  have h := checkLog_sound (w := (66104600279 / 566104600279)) (n := 12)
    (lo := (117306127 / 500000000)) (hi := (46922451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316104600279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316104600279 / 250000000000) = 1/(250000000000 / 316104600279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7861 : Bounds (117306127 / 500000000) (46922451 / 200000000) (Real.log (316104600279 / 250000000000)) := by
  have h := reflection_log_7861_neg
  have he : Real.log (316104600279 / 250000000000) = -Real.log (250000000000 / 316104600279) := by
    rw [show ((316104600279 / 250000000000) : ℝ) = ((250000000000 / 316104600279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7862_neg : (235601803 / 1000000000) ≤ -Real.log (500000000000 / 632835112451) ∧
    -Real.log (500000000000 / 632835112451) ≤ (58900451 / 250000000) := by
  have h := checkLog_sound (w := (132835112451 / 1132835112451)) (n := 12)
    (lo := (235601803 / 1000000000)) (hi := (58900451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632835112451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632835112451 / 500000000000) = 1/(500000000000 / 632835112451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7862 : Bounds (235601803 / 1000000000) (58900451 / 250000000) (Real.log (632835112451 / 500000000000)) := by
  have h := reflection_log_7862_neg
  have he : Real.log (632835112451 / 500000000000) = -Real.log (500000000000 / 632835112451) := by
    rw [show ((632835112451 / 500000000000) : ℝ) = ((500000000000 / 632835112451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7863_neg : (235773827 / 500000000) ≤ -Real.log (100000000000 / 160247234873) ∧
    -Real.log (100000000000 / 160247234873) ≤ (94309531 / 200000000) := by
  have h := checkLog_sound (w := (60247234873 / 260247234873)) (n := 12)
    (lo := (235773827 / 500000000)) (hi := (94309531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160247234873 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160247234873 / 100000000000) = 1/(100000000000 / 160247234873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7863 : Bounds (235773827 / 500000000) (94309531 / 200000000) (Real.log (160247234873 / 100000000000)) := by
  have h := reflection_log_7863_neg
  have he : Real.log (160247234873 / 100000000000) = -Real.log (100000000000 / 160247234873) := by
    rw [show ((160247234873 / 100000000000) : ℝ) = ((100000000000 / 160247234873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7864_neg : (47260441 / 100000000) ≤ -Real.log (250000000000 / 401041666667) ∧
    -Real.log (250000000000 / 401041666667) ≤ (472604411 / 1000000000) := by
  have h := checkLog_sound (w := (151041666667 / 651041666667)) (n := 12)
    (lo := (47260441 / 100000000)) (hi := (472604411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401041666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401041666667 / 250000000000) = 1/(250000000000 / 401041666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7864 : Bounds (47260441 / 100000000) (472604411 / 1000000000) (Real.log (401041666667 / 250000000000)) := by
  have h := reflection_log_7864_neg
  have he : Real.log (401041666667 / 250000000000) = -Real.log (250000000000 / 401041666667) := by
    rw [show ((401041666667 / 250000000000) : ℝ) = ((250000000000 / 401041666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7865_neg : (104522313 / 500000000) ≤ -Real.log (400 / 493) ∧
    -Real.log (400 / 493) ≤ (209044627 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 893)) (n := 12)
    (lo := (104522313 / 500000000)) (hi := (209044627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 400) = 1/(400 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7865 : Bounds (104522313 / 500000000) (209044627 / 1000000000) (Real.log (493 / 400)) := by
  have h := reflection_log_7865_neg
  have he : Real.log (493 / 400) = -Real.log (400 / 493) := by
    rw [show ((493 / 400) : ℝ) = ((400 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7866_neg : (264616799 / 1000000000) ≤ -Real.log (307 / 400) ∧
    -Real.log (307 / 400) ≤ (330771 / 1250000) := by
  have h := checkLog_sound (w := (93 / 707)) (n := 12)
    (lo := (264616799 / 1000000000)) (hi := (330771 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 307) = 1/(307 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7866 : Bounds (-330771 / 1250000) (-264616799 / 1000000000) (Real.log (307 / 400)) := by
  have h := reflection_log_7866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7867_neg : (29059 / 125000000) ≤ -Real.log (400000 / 400093) ∧
    -Real.log (400000 / 400093) ≤ (232473 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 800093)) (n := 12)
    (lo := (29059 / 125000000)) (hi := (232473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400093 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400093 / 400000) = 1/(400000 / 400093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7867 : Bounds (29059 / 125000000) (232473 / 1000000000) (Real.log (400093 / 400000)) := by
  have h := reflection_log_7867_neg
  have he : Real.log (400093 / 400000) = -Real.log (400000 / 400093) := by
    rw [show ((400093 / 400000) : ℝ) = ((400000 / 400093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7868_neg : (232527 / 1000000000) ≤ -Real.log (399907 / 400000) ∧
    -Real.log (399907 / 400000) ≤ (14533 / 62500000) := by
  have h := checkLog_sound (w := (93 / 799907)) (n := 12)
    (lo := (232527 / 1000000000)) (hi := (14533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399907) = 1/(399907 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7868 : Bounds (-14533 / 62500000) (-232527 / 1000000000) (Real.log (399907 / 400000)) := by
  have h := reflection_log_7868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7869_neg : (55336241 / 500000000) ≤ -Real.log (1000000 / 1117029) ∧
    -Real.log (1000000 / 1117029) ≤ (110672483 / 1000000000) := by
  have h := checkLog_sound (w := (117029 / 2117029)) (n := 12)
    (lo := (55336241 / 500000000)) (hi := (110672483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117029 / 1000000) = 1/(1000000 / 1117029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7869 : Bounds (55336241 / 500000000) (110672483 / 1000000000) (Real.log (1117029 / 1000000)) := by
  have h := reflection_log_7869_neg
  have he : Real.log (1117029 / 1000000) = -Real.log (1000000 / 1117029) := by
    rw [show ((1117029 / 1000000) : ℝ) = ((1000000 / 1117029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7870_neg : (124462921 / 1000000000) ≤ -Real.log (882971 / 1000000) ∧
    -Real.log (882971 / 1000000) ≤ (62231461 / 500000000) := by
  have h := checkLog_sound (w := (117029 / 1882971)) (n := 12)
    (lo := (124462921 / 1000000000)) (hi := (62231461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 882971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 882971) = 1/(882971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7870 : Bounds (-62231461 / 500000000) (-124462921 / 1000000000) (Real.log (882971 / 1000000)) := by
  have h := reflection_log_7870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7871_neg : (111109259 / 1000000000) ≤ -Real.log (1000000 / 1117517) ∧
    -Real.log (1000000 / 1117517) ≤ (5555463 / 50000000) := by
  have h := checkLog_sound (w := (117517 / 2117517)) (n := 12)
    (lo := (111109259 / 1000000000)) (hi := (5555463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1117517 / 1000000) = 1/(1000000 / 1117517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7871 : Bounds (111109259 / 1000000000) (5555463 / 50000000) (Real.log (1117517 / 1000000)) := by
  have h := reflection_log_7871_neg
  have he : Real.log (1117517 / 1000000) = -Real.log (1000000 / 1117517) := by
    rw [show ((1117517 / 1000000) : ℝ) = ((1000000 / 1117517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
