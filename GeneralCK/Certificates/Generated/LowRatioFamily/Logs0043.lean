import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2752_neg : (7295817 / 1000000000) ≤ -Real.log (2481826831 / 2500000000) ∧
    -Real.log (2481826831 / 2500000000) ≤ (3647909 / 500000000) := by
  have h := checkLog_sound (w := (18173169 / 4981826831)) (n := 12)
    (lo := (7295817 / 1000000000)) (hi := (3647909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2481826831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2481826831) = 1/(2481826831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2752 : Bounds (-3647909 / 500000000) (-7295817 / 1000000000) (Real.log (2481826831 / 2500000000)) := by
  have h := reflection_log_2752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2753_neg : (42733749 / 250000000) ≤ -Real.log (7812500000 / 9268856451) ∧
    -Real.log (7812500000 / 9268856451) ≤ (170934997 / 1000000000) := by
  have h := checkLog_sound (w := (1456356451 / 17081356451)) (n := 12)
    (lo := (42733749 / 250000000)) (hi := (170934997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9268856451 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9268856451 / 7812500000) = 1/(7812500000 / 9268856451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2753 : Bounds (42733749 / 250000000) (170934997 / 1000000000) (Real.log (9268856451 / 7812500000)) := by
  have h := reflection_log_2753_neg
  have he : Real.log (9268856451 / 7812500000) = -Real.log (7812500000 / 9268856451) := by
    rw [show ((9268856451 / 7812500000) : ℝ) = ((7812500000 / 9268856451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2754_neg : (171380241 / 1000000000) ≤ -Real.log (250000000000 / 296735497021) ∧
    -Real.log (250000000000 / 296735497021) ≤ (85690121 / 500000000) := by
  have h := checkLog_sound (w := (46735497021 / 546735497021)) (n := 12)
    (lo := (171380241 / 1000000000)) (hi := (85690121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296735497021 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296735497021 / 250000000000) = 1/(250000000000 / 296735497021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2754 : Bounds (171380241 / 1000000000) (85690121 / 500000000) (Real.log (296735497021 / 250000000000)) := by
  have h := reflection_log_2754_neg
  have he : Real.log (296735497021 / 250000000000) = -Real.log (250000000000 / 296735497021) := by
    rw [show ((296735497021 / 250000000000) : ℝ) = ((250000000000 / 296735497021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2755_neg : (342921437 / 1000000000) ≤ -Real.log (500000000000 / 704529029149) ∧
    -Real.log (500000000000 / 704529029149) ≤ (171460719 / 500000000) := by
  have h := checkLog_sound (w := (204529029149 / 1204529029149)) (n := 12)
    (lo := (342921437 / 1000000000)) (hi := (171460719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704529029149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704529029149 / 500000000000) = 1/(500000000000 / 704529029149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2755 : Bounds (342921437 / 1000000000) (171460719 / 500000000) (Real.log (704529029149 / 500000000000)) := by
  have h := reflection_log_2755_neg
  have he : Real.log (704529029149 / 500000000000) = -Real.log (500000000000 / 704529029149) := by
    rw [show ((704529029149 / 500000000000) : ℝ) = ((500000000000 / 704529029149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2756_neg : (171563689 / 500000000) ≤ -Real.log (500000000000 / 704674135647) ∧
    -Real.log (500000000000 / 704674135647) ≤ (343127379 / 1000000000) := by
  have h := checkLog_sound (w := (204674135647 / 1204674135647)) (n := 12)
    (lo := (171563689 / 500000000)) (hi := (343127379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704674135647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704674135647 / 500000000000) = 1/(500000000000 / 704674135647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2756 : Bounds (171563689 / 500000000) (343127379 / 1000000000) (Real.log (704674135647 / 500000000000)) := by
  have h := reflection_log_2756_neg
  have he : Real.log (704674135647 / 500000000000) = -Real.log (500000000000 / 704674135647) := by
    rw [show ((704674135647 / 500000000000) : ℝ) = ((500000000000 / 704674135647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2757_neg : (39250937 / 250000000) ≤ -Real.log (100 / 117) ∧
    -Real.log (100 / 117) ≤ (157003749 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 217)) (n := 12)
    (lo := (39250937 / 250000000)) (hi := (157003749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 100) = 1/(100 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2757 : Bounds (39250937 / 250000000) (157003749 / 1000000000) (Real.log (117 / 100)) := by
  have h := reflection_log_2757_neg
  have he : Real.log (117 / 100) = -Real.log (100 / 117) := by
    rw [show ((117 / 100) : ℝ) = ((100 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2758_neg : (93164789 / 500000000) ≤ -Real.log (83 / 100) ∧
    -Real.log (83 / 100) ≤ (186329579 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 83) = 1/(83 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2758 : Bounds (-186329579 / 1000000000) (-93164789 / 500000000) (Real.log (83 / 100)) := by
  have h := reflection_log_2758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2759_neg : (33997 / 200000000) ≤ -Real.log (100000 / 100017) ∧
    -Real.log (100000 / 100017) ≤ (84993 / 500000000) := by
  have h := checkLog_sound (w := (17 / 200017)) (n := 12)
    (lo := (33997 / 200000000)) (hi := (84993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100017 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100017 / 100000) = 1/(100000 / 100017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2759 : Bounds (33997 / 200000000) (84993 / 500000000) (Real.log (100017 / 100000)) := by
  have h := reflection_log_2759_neg
  have he : Real.log (100017 / 100000) = -Real.log (100000 / 100017) := by
    rw [show ((100017 / 100000) : ℝ) = ((100000 / 100017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2760_neg : (85007 / 500000000) ≤ -Real.log (99983 / 100000) ∧
    -Real.log (99983 / 100000) ≤ (34003 / 200000000) := by
  have h := checkLog_sound (w := (17 / 199983)) (n := 12)
    (lo := (85007 / 500000000)) (hi := (34003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99983) = 1/(99983 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2760 : Bounds (-34003 / 200000000) (-85007 / 500000000) (Real.log (99983 / 100000)) := by
  have h := reflection_log_2760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2761_neg : (81866581 / 1000000000) ≤ -Real.log (1000000 / 1085311) ∧
    -Real.log (1000000 / 1085311) ≤ (40933291 / 500000000) := by
  have h := checkLog_sound (w := (85311 / 2085311)) (n := 12)
    (lo := (81866581 / 1000000000)) (hi := (40933291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085311 / 1000000) = 1/(1000000 / 1085311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2761 : Bounds (81866581 / 1000000000) (40933291 / 500000000) (Real.log (1085311 / 1000000)) := by
  have h := reflection_log_2761_neg
  have he : Real.log (1085311 / 1000000) = -Real.log (1000000 / 1085311) := by
    rw [show ((1085311 / 1000000) : ℝ) = ((1000000 / 1085311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2762_neg : (44585581 / 500000000) ≤ -Real.log (914689 / 1000000) ∧
    -Real.log (914689 / 1000000) ≤ (89171163 / 1000000000) := by
  have h := checkLog_sound (w := (85311 / 1914689)) (n := 12)
    (lo := (44585581 / 500000000)) (hi := (89171163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914689) = 1/(914689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2762 : Bounds (-89171163 / 1000000000) (-44585581 / 500000000) (Real.log (914689 / 1000000)) := by
  have h := reflection_log_2762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2763_neg : (82070189 / 1000000000) ≤ -Real.log (250000 / 271383) ∧
    -Real.log (250000 / 271383) ≤ (8207019 / 100000000) := by
  have h := checkLog_sound (w := (21383 / 521383)) (n := 12)
    (lo := (82070189 / 1000000000)) (hi := (8207019 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271383 / 250000) = 1/(250000 / 271383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2763 : Bounds (82070189 / 1000000000) (8207019 / 100000000) (Real.log (271383 / 250000)) := by
  have h := reflection_log_2763_neg
  have he : Real.log (271383 / 250000) = -Real.log (250000 / 271383) := by
    rw [show ((271383 / 250000) : ℝ) = ((250000 / 271383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2764_neg : (89412803 / 1000000000) ≤ -Real.log (228617 / 250000) ∧
    -Real.log (228617 / 250000) ≤ (22353201 / 250000000) := by
  have h := checkLog_sound (w := (21383 / 478617)) (n := 12)
    (lo := (89412803 / 1000000000)) (hi := (22353201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228617) = 1/(228617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2764 : Bounds (-22353201 / 250000000) (-89412803 / 1000000000) (Real.log (228617 / 250000)) := by
  have h := reflection_log_2764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2765_neg : (3671307 / 500000000) ≤ -Real.log (62042767311 / 62500000000) ∧
    -Real.log (62042767311 / 62500000000) ≤ (1468523 / 200000000) := by
  have h := checkLog_sound (w := (457232689 / 124542767311)) (n := 12)
    (lo := (3671307 / 500000000)) (hi := (1468523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62042767311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62042767311) = 1/(62042767311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2765 : Bounds (-1468523 / 200000000) (-3671307 / 500000000) (Real.log (62042767311 / 62500000000)) := by
  have h := reflection_log_2765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2766_neg : (365229 / 50000000) ≤ -Real.log (992722033279 / 1000000000000) ∧
    -Real.log (992722033279 / 1000000000000) ≤ (7304581 / 1000000000) := by
  have h := checkLog_sound (w := (7277966721 / 1992722033279)) (n := 12)
    (lo := (365229 / 50000000)) (hi := (7304581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992722033279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992722033279) = 1/(992722033279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2766 : Bounds (-7304581 / 1000000000) (-365229 / 50000000) (Real.log (992722033279 / 1000000000000)) := by
  have h := reflection_log_2766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2767_neg : (10689859 / 62500000) ≤ -Real.log (500000000000 / 593267766421) ∧
    -Real.log (500000000000 / 593267766421) ≤ (34207549 / 200000000) := by
  have h := checkLog_sound (w := (93267766421 / 1093267766421)) (n := 12)
    (lo := (10689859 / 62500000)) (hi := (34207549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593267766421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593267766421 / 500000000000) = 1/(500000000000 / 593267766421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2767 : Bounds (10689859 / 62500000) (34207549 / 200000000) (Real.log (593267766421 / 500000000000)) := by
  have h := reflection_log_2767_neg
  have he : Real.log (593267766421 / 500000000000) = -Real.log (500000000000 / 593267766421) := by
    rw [show ((593267766421 / 500000000000) : ℝ) = ((500000000000 / 593267766421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2768_neg : (10717687 / 62500000) ≤ -Real.log (500000000000 / 593531977063) ∧
    -Real.log (500000000000 / 593531977063) ≤ (171482993 / 1000000000) := by
  have h := checkLog_sound (w := (93531977063 / 1093531977063)) (n := 12)
    (lo := (10717687 / 62500000)) (hi := (171482993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593531977063 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593531977063 / 500000000000) = 1/(500000000000 / 593531977063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2768 : Bounds (10717687 / 62500000) (171482993 / 1000000000) (Real.log (593531977063 / 500000000000)) := by
  have h := reflection_log_2768_neg
  have he : Real.log (593531977063 / 500000000000) = -Real.log (500000000000 / 593531977063) := by
    rw [show ((593531977063 / 500000000000) : ℝ) = ((500000000000 / 593531977063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2769_neg : (171563689 / 500000000) ≤ -Real.log (250000000000 / 352337067823) ∧
    -Real.log (250000000000 / 352337067823) ≤ (343127379 / 1000000000) := by
  have h := checkLog_sound (w := (102337067823 / 602337067823)) (n := 12)
    (lo := (171563689 / 500000000)) (hi := (343127379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352337067823 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352337067823 / 250000000000) = 1/(250000000000 / 352337067823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2769 : Bounds (171563689 / 500000000) (343127379 / 1000000000) (Real.log (352337067823 / 250000000000)) := by
  have h := reflection_log_2769_neg
  have he : Real.log (352337067823 / 250000000000) = -Real.log (250000000000 / 352337067823) := by
    rw [show ((352337067823 / 250000000000) : ℝ) = ((250000000000 / 352337067823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2770_neg : (343333327 / 1000000000) ≤ -Real.log (500000000000 / 704819277109) ∧
    -Real.log (500000000000 / 704819277109) ≤ (21458333 / 62500000) := by
  have h := checkLog_sound (w := (204819277109 / 1204819277109)) (n := 12)
    (lo := (343333327 / 1000000000)) (hi := (21458333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704819277109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704819277109 / 500000000000) = 1/(500000000000 / 704819277109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2770 : Bounds (343333327 / 1000000000) (21458333 / 62500000) (Real.log (704819277109 / 500000000000)) := by
  have h := reflection_log_2770_neg
  have he : Real.log (704819277109 / 500000000000) = -Real.log (500000000000 / 704819277109) := by
    rw [show ((704819277109 / 500000000000) : ℝ) = ((500000000000 / 704819277109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2771_neg : (31417843 / 200000000) ≤ -Real.log (10000 / 11701) ∧
    -Real.log (10000 / 11701) ≤ (2454519 / 15625000) := by
  have h := checkLog_sound (w := (1701 / 21701)) (n := 12)
    (lo := (31417843 / 200000000)) (hi := (2454519 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11701 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11701 / 10000) = 1/(10000 / 11701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2771 : Bounds (31417843 / 200000000) (2454519 / 15625000) (Real.log (11701 / 10000)) := by
  have h := reflection_log_2771_neg
  have he : Real.log (11701 / 10000) = -Real.log (10000 / 11701) := by
    rw [show ((11701 / 10000) : ℝ) = ((10000 / 11701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2772_neg : (186450067 / 1000000000) ≤ -Real.log (8299 / 10000) ∧
    -Real.log (8299 / 10000) ≤ (46612517 / 250000000) := by
  have h := checkLog_sound (w := (1701 / 18299)) (n := 12)
    (lo := (186450067 / 1000000000)) (hi := (46612517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8299) = 1/(8299 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2772 : Bounds (-46612517 / 250000000) (-186450067 / 1000000000) (Real.log (8299 / 10000)) := by
  have h := reflection_log_2772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2773_neg : (34017 / 200000000) ≤ -Real.log (10000000 / 10001701) ∧
    -Real.log (10000000 / 10001701) ≤ (85043 / 500000000) := by
  have h := checkLog_sound (w := (1701 / 20001701)) (n := 12)
    (lo := (34017 / 200000000)) (hi := (85043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001701 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001701 / 10000000) = 1/(10000000 / 10001701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2773 : Bounds (34017 / 200000000) (85043 / 500000000) (Real.log (10001701 / 10000000)) := by
  have h := reflection_log_2773_neg
  have he : Real.log (10001701 / 10000000) = -Real.log (10000000 / 10001701) := by
    rw [show ((10001701 / 10000000) : ℝ) = ((10000000 / 10001701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2774_neg : (85057 / 500000000) ≤ -Real.log (9998299 / 10000000) ∧
    -Real.log (9998299 / 10000000) ≤ (34023 / 200000000) := by
  have h := checkLog_sound (w := (1701 / 19998299)) (n := 12)
    (lo := (85057 / 500000000)) (hi := (34023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998299) = 1/(9998299 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2774 : Bounds (-34023 / 200000000) (-85057 / 500000000) (Real.log (9998299 / 10000000)) := by
  have h := reflection_log_2774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2775_neg : (81913571 / 1000000000) ≤ -Real.log (500000 / 542681) ∧
    -Real.log (500000 / 542681) ≤ (20478393 / 250000000) := by
  have h := checkLog_sound (w := (42681 / 1042681)) (n := 12)
    (lo := (81913571 / 1000000000)) (hi := (20478393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542681 / 500000) = 1/(500000 / 542681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2775 : Bounds (81913571 / 1000000000) (20478393 / 250000000) (Real.log (542681 / 500000)) := by
  have h := reflection_log_2775_neg
  have he : Real.log (542681 / 500000) = -Real.log (500000 / 542681) := by
    rw [show ((542681 / 500000) : ℝ) = ((500000 / 542681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2776_neg : (2230673 / 25000000) ≤ -Real.log (457319 / 500000) ∧
    -Real.log (457319 / 500000) ≤ (89226921 / 1000000000) := by
  have h := checkLog_sound (w := (42681 / 957319)) (n := 12)
    (lo := (2230673 / 25000000)) (hi := (89226921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457319) = 1/(457319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2776 : Bounds (-89226921 / 1000000000) (-2230673 / 25000000) (Real.log (457319 / 500000)) := by
  have h := reflection_log_2776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2777_neg : (82117169 / 1000000000) ≤ -Real.log (1000000 / 1085583) ∧
    -Real.log (1000000 / 1085583) ≤ (8211717 / 100000000) := by
  have h := checkLog_sound (w := (85583 / 2085583)) (n := 12)
    (lo := (82117169 / 1000000000)) (hi := (8211717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085583 / 1000000) = 1/(1000000 / 1085583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2777 : Bounds (82117169 / 1000000000) (8211717 / 100000000) (Real.log (1085583 / 1000000)) := by
  have h := reflection_log_2777_neg
  have he : Real.log (1085583 / 1000000) = -Real.log (1000000 / 1085583) := by
    rw [show ((1085583 / 1000000) : ℝ) = ((1000000 / 1085583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2778_neg : (3578743 / 40000000) ≤ -Real.log (914417 / 1000000) ∧
    -Real.log (914417 / 1000000) ≤ (2795893 / 31250000) := by
  have h := checkLog_sound (w := (85583 / 1914417)) (n := 12)
    (lo := (3578743 / 40000000)) (hi := (2795893 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914417) = 1/(914417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2778 : Bounds (-2795893 / 31250000) (-3578743 / 40000000) (Real.log (914417 / 1000000)) := by
  have h := reflection_log_2778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2779_neg : (1470281 / 200000000) ≤ -Real.log (992675550111 / 1000000000000) ∧
    -Real.log (992675550111 / 1000000000000) ≤ (3675703 / 500000000) := by
  have h := checkLog_sound (w := (7324449889 / 1992675550111)) (n := 12)
    (lo := (1470281 / 200000000)) (hi := (3675703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992675550111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992675550111) = 1/(992675550111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2779 : Bounds (-3675703 / 500000000) (-1470281 / 200000000) (Real.log (992675550111 / 1000000000000)) := by
  have h := reflection_log_2779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2780_neg : (1828337 / 250000000) ≤ -Real.log (248178332239 / 250000000000) ∧
    -Real.log (248178332239 / 250000000000) ≤ (7313349 / 1000000000) := by
  have h := checkLog_sound (w := (1821667761 / 498178332239)) (n := 12)
    (lo := (1828337 / 250000000)) (hi := (7313349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248178332239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248178332239) = 1/(248178332239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2780 : Bounds (-7313349 / 1000000000) (-1828337 / 250000000) (Real.log (248178332239 / 250000000000)) := by
  have h := reflection_log_2780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2781_neg : (42785123 / 250000000) ≤ -Real.log (250000000000 / 296664363387) ∧
    -Real.log (250000000000 / 296664363387) ≤ (171140493 / 1000000000) := by
  have h := checkLog_sound (w := (46664363387 / 546664363387)) (n := 12)
    (lo := (42785123 / 250000000)) (hi := (171140493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296664363387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296664363387 / 250000000000) = 1/(250000000000 / 296664363387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2781 : Bounds (42785123 / 250000000) (171140493 / 1000000000) (Real.log (296664363387 / 250000000000)) := by
  have h := reflection_log_2781_neg
  have he : Real.log (296664363387 / 250000000000) = -Real.log (250000000000 / 296664363387) := by
    rw [show ((296664363387 / 250000000000) : ℝ) = ((250000000000 / 296664363387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2782_neg : (34317149 / 200000000) ≤ -Real.log (100000000000 / 118718593377) ∧
    -Real.log (100000000000 / 118718593377) ≤ (85792873 / 500000000) := by
  have h := checkLog_sound (w := (18718593377 / 218718593377)) (n := 12)
    (lo := (34317149 / 200000000)) (hi := (85792873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118718593377 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118718593377 / 100000000000) = 1/(100000000000 / 118718593377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2782 : Bounds (34317149 / 200000000) (85792873 / 500000000) (Real.log (118718593377 / 100000000000)) := by
  have h := reflection_log_2782_neg
  have he : Real.log (118718593377 / 100000000000) = -Real.log (100000000000 / 118718593377) := by
    rw [show ((118718593377 / 100000000000) : ℝ) = ((100000000000 / 118718593377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2783_neg : (343333327 / 1000000000) ≤ -Real.log (125000000000 / 176204819277) ∧
    -Real.log (125000000000 / 176204819277) ≤ (21458333 / 62500000) := by
  have h := checkLog_sound (w := (51204819277 / 301204819277)) (n := 12)
    (lo := (343333327 / 1000000000)) (hi := (21458333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176204819277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176204819277 / 125000000000) = 1/(125000000000 / 176204819277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2783 : Bounds (343333327 / 1000000000) (21458333 / 62500000) (Real.log (176204819277 / 125000000000)) := by
  have h := reflection_log_2783_neg
  have he : Real.log (176204819277 / 125000000000) = -Real.log (125000000000 / 176204819277) := by
    rw [show ((176204819277 / 125000000000) : ℝ) = ((125000000000 / 176204819277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2784_neg : (171769641 / 500000000) ≤ -Real.log (500000000000 / 704964453549) ∧
    -Real.log (500000000000 / 704964453549) ≤ (343539283 / 1000000000) := by
  have h := checkLog_sound (w := (204964453549 / 1204964453549)) (n := 12)
    (lo := (171769641 / 500000000)) (hi := (343539283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704964453549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704964453549 / 500000000000) = 1/(500000000000 / 704964453549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2784 : Bounds (171769641 / 500000000) (343539283 / 1000000000) (Real.log (704964453549 / 500000000000)) := by
  have h := reflection_log_2784_neg
  have he : Real.log (704964453549 / 500000000000) = -Real.log (500000000000 / 704964453549) := by
    rw [show ((704964453549 / 500000000000) : ℝ) = ((500000000000 / 704964453549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2785_neg : (78587337 / 500000000) ≤ -Real.log (5000 / 5851) ∧
    -Real.log (5000 / 5851) ≤ (6286987 / 40000000) := by
  have h := checkLog_sound (w := (851 / 10851)) (n := 12)
    (lo := (78587337 / 500000000)) (hi := (6286987 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5851 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5851 / 5000) = 1/(5000 / 5851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2785 : Bounds (78587337 / 500000000) (6286987 / 40000000) (Real.log (5851 / 5000)) := by
  have h := reflection_log_2785_neg
  have he : Real.log (5851 / 5000) = -Real.log (5000 / 5851) := by
    rw [show ((5851 / 5000) : ℝ) = ((5000 / 5851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2786_neg : (186570571 / 1000000000) ≤ -Real.log (4149 / 5000) ∧
    -Real.log (4149 / 5000) ≤ (46642643 / 250000000) := by
  have h := checkLog_sound (w := (851 / 9149)) (n := 12)
    (lo := (186570571 / 1000000000)) (hi := (46642643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4149) = 1/(4149 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2786 : Bounds (-46642643 / 250000000) (-186570571 / 1000000000) (Real.log (4149 / 5000)) := by
  have h := reflection_log_2786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2787_neg : (34037 / 200000000) ≤ -Real.log (5000000 / 5000851) ∧
    -Real.log (5000000 / 5000851) ≤ (85093 / 500000000) := by
  have h := checkLog_sound (w := (851 / 10000851)) (n := 12)
    (lo := (34037 / 200000000)) (hi := (85093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000851 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000851 / 5000000) = 1/(5000000 / 5000851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2787 : Bounds (34037 / 200000000) (85093 / 500000000) (Real.log (5000851 / 5000000)) := by
  have h := reflection_log_2787_neg
  have he : Real.log (5000851 / 5000000) = -Real.log (5000000 / 5000851) := by
    rw [show ((5000851 / 5000000) : ℝ) = ((5000000 / 5000851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2788_neg : (85107 / 500000000) ≤ -Real.log (4999149 / 5000000) ∧
    -Real.log (4999149 / 5000000) ≤ (34043 / 200000000) := by
  have h := checkLog_sound (w := (851 / 9999149)) (n := 12)
    (lo := (85107 / 500000000)) (hi := (34043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999149) = 1/(4999149 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2788 : Bounds (-34043 / 200000000) (-85107 / 500000000) (Real.log (4999149 / 5000000)) := by
  have h := reflection_log_2788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2789_neg : (40979819 / 500000000) ≤ -Real.log (250000 / 271353) ∧
    -Real.log (250000 / 271353) ≤ (81959639 / 1000000000) := by
  have h := checkLog_sound (w := (21353 / 521353)) (n := 12)
    (lo := (40979819 / 500000000)) (hi := (81959639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271353 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271353 / 250000) = 1/(250000 / 271353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2789 : Bounds (40979819 / 500000000) (81959639 / 1000000000) (Real.log (271353 / 250000)) := by
  have h := reflection_log_2789_neg
  have he : Real.log (271353 / 250000) = -Real.log (250000 / 271353) := by
    rw [show ((271353 / 250000) : ℝ) = ((250000 / 271353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2790_neg : (22320397 / 250000000) ≤ -Real.log (228647 / 250000) ∧
    -Real.log (228647 / 250000) ≤ (89281589 / 1000000000) := by
  have h := checkLog_sound (w := (21353 / 478647)) (n := 12)
    (lo := (22320397 / 250000000)) (hi := (89281589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228647) = 1/(228647 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2790 : Bounds (-89281589 / 1000000000) (-22320397 / 250000000) (Real.log (228647 / 250000)) := by
  have h := reflection_log_2790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2791_neg : (20541037 / 250000000) ≤ -Real.log (500000 / 542817) ∧
    -Real.log (500000 / 542817) ≤ (82164149 / 1000000000) := by
  have h := checkLog_sound (w := (42817 / 1042817)) (n := 12)
    (lo := (20541037 / 250000000)) (hi := (82164149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542817 / 500000) = 1/(500000 / 542817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2791 : Bounds (20541037 / 250000000) (82164149 / 1000000000) (Real.log (542817 / 500000)) := by
  have h := reflection_log_2791_neg
  have he : Real.log (542817 / 500000) = -Real.log (500000 / 542817) := by
    rw [show ((542817 / 500000) : ℝ) = ((500000 / 542817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2792_neg : (1790487 / 20000000) ≤ -Real.log (457183 / 500000) ∧
    -Real.log (457183 / 500000) ≤ (89524351 / 1000000000) := by
  have h := checkLog_sound (w := (42817 / 957183)) (n := 12)
    (lo := (1790487 / 20000000)) (hi := (89524351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457183) = 1/(457183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2792 : Bounds (-89524351 / 1000000000) (-1790487 / 20000000) (Real.log (457183 / 500000)) := by
  have h := reflection_log_2792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2793_neg : (7360201 / 1000000000) ≤ -Real.log (248166704511 / 250000000000) ∧
    -Real.log (248166704511 / 250000000000) ≤ (3680101 / 500000000) := by
  have h := checkLog_sound (w := (1833295489 / 498166704511)) (n := 12)
    (lo := (7360201 / 1000000000)) (hi := (3680101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248166704511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248166704511) = 1/(248166704511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2793 : Bounds (-3680101 / 500000000) (-7360201 / 1000000000) (Real.log (248166704511 / 250000000000)) := by
  have h := reflection_log_2793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2794_neg : (7321949 / 1000000000) ≤ -Real.log (62044049391 / 62500000000) ∧
    -Real.log (62044049391 / 62500000000) ≤ (146439 / 20000000) := by
  have h := checkLog_sound (w := (455950609 / 124544049391)) (n := 12)
    (lo := (7321949 / 1000000000)) (hi := (146439 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62044049391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62044049391) = 1/(62044049391 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2794 : Bounds (-146439 / 20000000) (-7321949 / 1000000000) (Real.log (62044049391 / 62500000000)) := by
  have h := reflection_log_2794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2795_neg : (85620613 / 500000000) ≤ -Real.log (500000000000 / 593388498427) ∧
    -Real.log (500000000000 / 593388498427) ≤ (171241227 / 1000000000) := by
  have h := checkLog_sound (w := (93388498427 / 1093388498427)) (n := 12)
    (lo := (85620613 / 500000000)) (hi := (171241227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593388498427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593388498427 / 500000000000) = 1/(500000000000 / 593388498427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2795 : Bounds (85620613 / 500000000) (171241227 / 1000000000) (Real.log (593388498427 / 500000000000)) := by
  have h := reflection_log_2795_neg
  have he : Real.log (593388498427 / 500000000000) = -Real.log (500000000000 / 593388498427) := by
    rw [show ((593388498427 / 500000000000) : ℝ) = ((500000000000 / 593388498427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2796_neg : (85844249 / 500000000) ≤ -Real.log (62500000000 / 74206745439) ∧
    -Real.log (62500000000 / 74206745439) ≤ (171688499 / 1000000000) := by
  have h := checkLog_sound (w := (11706745439 / 136706745439)) (n := 12)
    (lo := (85844249 / 500000000)) (hi := (171688499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74206745439 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74206745439 / 62500000000) = 1/(62500000000 / 74206745439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2796 : Bounds (85844249 / 500000000) (171688499 / 1000000000) (Real.log (74206745439 / 62500000000)) := by
  have h := reflection_log_2796_neg
  have he : Real.log (74206745439 / 62500000000) = -Real.log (62500000000 / 74206745439) := by
    rw [show ((74206745439 / 62500000000) : ℝ) = ((62500000000 / 74206745439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2797_neg : (171769641 / 500000000) ≤ -Real.log (125000000000 / 176241113387) ∧
    -Real.log (125000000000 / 176241113387) ≤ (343539283 / 1000000000) := by
  have h := checkLog_sound (w := (51241113387 / 301241113387)) (n := 12)
    (lo := (171769641 / 500000000)) (hi := (343539283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176241113387 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176241113387 / 125000000000) = 1/(125000000000 / 176241113387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2797 : Bounds (171769641 / 500000000) (343539283 / 1000000000) (Real.log (176241113387 / 125000000000)) := by
  have h := reflection_log_2797_neg
  have he : Real.log (176241113387 / 125000000000) = -Real.log (125000000000 / 176241113387) := by
    rw [show ((176241113387 / 125000000000) : ℝ) = ((125000000000 / 176241113387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2798_neg : (68749049 / 200000000) ≤ -Real.log (25000000000 / 35255483249) ∧
    -Real.log (25000000000 / 35255483249) ≤ (171872623 / 500000000) := by
  have h := checkLog_sound (w := (10255483249 / 60255483249)) (n := 12)
    (lo := (68749049 / 200000000)) (hi := (171872623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35255483249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35255483249 / 25000000000) = 1/(25000000000 / 35255483249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2798 : Bounds (68749049 / 200000000) (171872623 / 500000000) (Real.log (35255483249 / 25000000000)) := by
  have h := reflection_log_2798_neg
  have he : Real.log (35255483249 / 25000000000) = -Real.log (25000000000 / 35255483249) := by
    rw [show ((35255483249 / 25000000000) : ℝ) = ((25000000000 / 35255483249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2799_neg : (78630063 / 500000000) ≤ -Real.log (10000 / 11703) ∧
    -Real.log (10000 / 11703) ≤ (157260127 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 21703)) (n := 12)
    (lo := (78630063 / 500000000)) (hi := (157260127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 10000) = 1/(10000 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2799 : Bounds (78630063 / 500000000) (157260127 / 1000000000) (Real.log (11703 / 10000)) := by
  have h := reflection_log_2799_neg
  have he : Real.log (11703 / 10000) = -Real.log (10000 / 11703) := by
    rw [show ((11703 / 10000) : ℝ) = ((10000 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2800_neg : (186691089 / 1000000000) ≤ -Real.log (8297 / 10000) ∧
    -Real.log (8297 / 10000) ≤ (18669109 / 100000000) := by
  have h := checkLog_sound (w := (1703 / 18297)) (n := 12)
    (lo := (186691089 / 1000000000)) (hi := (18669109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8297) = 1/(8297 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2800 : Bounds (-18669109 / 100000000) (-186691089 / 1000000000) (Real.log (8297 / 10000)) := by
  have h := reflection_log_2800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2801_neg : (34057 / 200000000) ≤ -Real.log (10000000 / 10001703) ∧
    -Real.log (10000000 / 10001703) ≤ (85143 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 20001703)) (n := 12)
    (lo := (34057 / 200000000)) (hi := (85143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001703 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001703 / 10000000) = 1/(10000000 / 10001703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2801 : Bounds (34057 / 200000000) (85143 / 500000000) (Real.log (10001703 / 10000000)) := by
  have h := reflection_log_2801_neg
  have he : Real.log (10001703 / 10000000) = -Real.log (10000000 / 10001703) := by
    rw [show ((10001703 / 10000000) : ℝ) = ((10000000 / 10001703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2802_neg : (85157 / 500000000) ≤ -Real.log (9998297 / 10000000) ∧
    -Real.log (9998297 / 10000000) ≤ (34063 / 200000000) := by
  have h := checkLog_sound (w := (1703 / 19998297)) (n := 12)
    (lo := (85157 / 500000000)) (hi := (34063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998297) = 1/(9998297 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2802 : Bounds (-34063 / 200000000) (-85157 / 500000000) (Real.log (9998297 / 10000000)) := by
  have h := reflection_log_2802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2803_neg : (2562707 / 31250000) ≤ -Real.log (1000000 / 1085463) ∧
    -Real.log (1000000 / 1085463) ≤ (656053 / 8000000) := by
  have h := checkLog_sound (w := (85463 / 2085463)) (n := 12)
    (lo := (2562707 / 31250000)) (hi := (656053 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085463 / 1000000) = 1/(1000000 / 1085463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2803 : Bounds (2562707 / 31250000) (656053 / 8000000) (Real.log (1085463 / 1000000)) := by
  have h := reflection_log_2803_neg
  have he : Real.log (1085463 / 1000000) = -Real.log (1000000 / 1085463) := by
    rw [show ((1085463 / 1000000) : ℝ) = ((1000000 / 1085463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2804_neg : (11167169 / 125000000) ≤ -Real.log (914537 / 1000000) ∧
    -Real.log (914537 / 1000000) ≤ (89337353 / 1000000000) := by
  have h := checkLog_sound (w := (85463 / 1914537)) (n := 12)
    (lo := (11167169 / 125000000)) (hi := (89337353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914537) = 1/(914537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2804 : Bounds (-89337353 / 1000000000) (-11167169 / 125000000) (Real.log (914537 / 1000000)) := by
  have h := reflection_log_2804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2805_neg : (82210203 / 1000000000) ≤ -Real.log (250000 / 271421) ∧
    -Real.log (250000 / 271421) ≤ (20552551 / 250000000) := by
  have h := checkLog_sound (w := (21421 / 521421)) (n := 12)
    (lo := (82210203 / 1000000000)) (hi := (20552551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271421 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271421 / 250000) = 1/(250000 / 271421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2805 : Bounds (82210203 / 1000000000) (20552551 / 250000000) (Real.log (271421 / 250000)) := by
  have h := reflection_log_2805_neg
  have he : Real.log (271421 / 250000) = -Real.log (250000 / 271421) := by
    rw [show ((271421 / 250000) : ℝ) = ((250000 / 271421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2806_neg : (44789517 / 500000000) ≤ -Real.log (228579 / 250000) ∧
    -Real.log (228579 / 250000) ≤ (17915807 / 200000000) := by
  have h := checkLog_sound (w := (21421 / 478579)) (n := 12)
    (lo := (44789517 / 500000000)) (hi := (17915807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228579) = 1/(228579 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2806 : Bounds (-17915807 / 200000000) (-44789517 / 500000000) (Real.log (228579 / 250000)) := by
  have h := reflection_log_2806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2807_neg : (7368831 / 1000000000) ≤ -Real.log (62041140759 / 62500000000) ∧
    -Real.log (62041140759 / 62500000000) ≤ (57569 / 7812500) := by
  have h := checkLog_sound (w := (458859241 / 124541140759)) (n := 12)
    (lo := (7368831 / 1000000000)) (hi := (57569 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62041140759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62041140759) = 1/(62041140759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2807 : Bounds (-57569 / 7812500) (-7368831 / 1000000000) (Real.log (62041140759 / 62500000000)) := by
  have h := reflection_log_2807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2808_neg : (916341 / 125000000) ≤ -Real.log (992696075631 / 1000000000000) ∧
    -Real.log (992696075631 / 1000000000000) ≤ (7330729 / 1000000000) := by
  have h := checkLog_sound (w := (7303924369 / 1992696075631)) (n := 12)
    (lo := (916341 / 125000000)) (hi := (7330729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992696075631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992696075631) = 1/(992696075631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2808 : Bounds (-7330729 / 1000000000) (-916341 / 125000000) (Real.log (992696075631 / 1000000000000)) := by
  have h := reflection_log_2808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2809_neg : (21417997 / 125000000) ≤ -Real.log (250000000000 / 296724736123) ∧
    -Real.log (250000000000 / 296724736123) ≤ (171343977 / 1000000000) := by
  have h := checkLog_sound (w := (46724736123 / 546724736123)) (n := 12)
    (lo := (21417997 / 125000000)) (hi := (171343977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296724736123 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296724736123 / 250000000000) = 1/(250000000000 / 296724736123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2809 : Bounds (21417997 / 125000000) (171343977 / 1000000000) (Real.log (296724736123 / 250000000000)) := by
  have h := reflection_log_2809_neg
  have he : Real.log (296724736123 / 250000000000) = -Real.log (250000000000 / 296724736123) := by
    rw [show ((296724736123 / 250000000000) : ℝ) = ((250000000000 / 296724736123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2810_neg : (171789237 / 1000000000) ≤ -Real.log (125000000000 / 148428442683) ∧
    -Real.log (125000000000 / 148428442683) ≤ (85894619 / 500000000) := by
  have h := checkLog_sound (w := (23428442683 / 273428442683)) (n := 12)
    (lo := (171789237 / 1000000000)) (hi := (85894619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148428442683 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148428442683 / 125000000000) = 1/(125000000000 / 148428442683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2810 : Bounds (171789237 / 1000000000) (85894619 / 500000000) (Real.log (148428442683 / 125000000000)) := by
  have h := reflection_log_2810_neg
  have he : Real.log (148428442683 / 125000000000) = -Real.log (125000000000 / 148428442683) := by
    rw [show ((148428442683 / 125000000000) : ℝ) = ((125000000000 / 148428442683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2811_neg : (68749049 / 200000000) ≤ -Real.log (500000000000 / 705109664979) ∧
    -Real.log (500000000000 / 705109664979) ≤ (171872623 / 500000000) := by
  have h := checkLog_sound (w := (205109664979 / 1205109664979)) (n := 12)
    (lo := (68749049 / 200000000)) (hi := (171872623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705109664979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705109664979 / 500000000000) = 1/(500000000000 / 705109664979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2811 : Bounds (68749049 / 200000000) (171872623 / 500000000) (Real.log (705109664979 / 500000000000)) := by
  have h := reflection_log_2811_neg
  have he : Real.log (705109664979 / 500000000000) = -Real.log (500000000000 / 705109664979) := by
    rw [show ((705109664979 / 500000000000) : ℝ) = ((500000000000 / 705109664979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2812_neg : (68790243 / 200000000) ≤ -Real.log (250000000000 / 352627455707) ∧
    -Real.log (250000000000 / 352627455707) ≤ (21496951 / 62500000) := by
  have h := checkLog_sound (w := (102627455707 / 602627455707)) (n := 12)
    (lo := (68790243 / 200000000)) (hi := (21496951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352627455707 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352627455707 / 250000000000) = 1/(250000000000 / 352627455707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2812 : Bounds (68790243 / 200000000) (21496951 / 62500000) (Real.log (352627455707 / 250000000000)) := by
  have h := reflection_log_2812_neg
  have he : Real.log (352627455707 / 250000000000) = -Real.log (250000000000 / 352627455707) := by
    rw [show ((352627455707 / 250000000000) : ℝ) = ((250000000000 / 352627455707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2813_neg : (15734557 / 100000000) ≤ -Real.log (1250 / 1463) ∧
    -Real.log (1250 / 1463) ≤ (157345571 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 2713)) (n := 12)
    (lo := (15734557 / 100000000)) (hi := (157345571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1250) = 1/(1250 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2813 : Bounds (15734557 / 100000000) (157345571 / 1000000000) (Real.log (1463 / 1250)) := by
  have h := reflection_log_2813_neg
  have he : Real.log (1463 / 1250) = -Real.log (1250 / 1463) := by
    rw [show ((1463 / 1250) : ℝ) = ((1250 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2814_neg : (93405811 / 500000000) ≤ -Real.log (1037 / 1250) ∧
    -Real.log (1037 / 1250) ≤ (186811623 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 2287)) (n := 12)
    (lo := (93405811 / 500000000)) (hi := (186811623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1037) = 1/(1037 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2814 : Bounds (-186811623 / 1000000000) (-93405811 / 500000000) (Real.log (1037 / 1250)) := by
  have h := reflection_log_2814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2815_neg : (34077 / 200000000) ≤ -Real.log (1250000 / 1250213) ∧
    -Real.log (1250000 / 1250213) ≤ (85193 / 500000000) := by
  have h := checkLog_sound (w := (213 / 2500213)) (n := 12)
    (lo := (34077 / 200000000)) (hi := (85193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250213 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250213 / 1250000) = 1/(1250000 / 1250213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2815 : Bounds (34077 / 200000000) (85193 / 500000000) (Real.log (1250213 / 1250000)) := by
  have h := reflection_log_2815_neg
  have he : Real.log (1250213 / 1250000) = -Real.log (1250000 / 1250213) := by
    rw [show ((1250213 / 1250000) : ℝ) = ((1250000 / 1250213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
