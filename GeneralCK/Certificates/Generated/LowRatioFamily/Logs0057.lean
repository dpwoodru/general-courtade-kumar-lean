import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3648_neg : (7864867 / 1000000000) ≤ -Real.log (9921659799 / 10000000000) ∧
    -Real.log (9921659799 / 10000000000) ≤ (1966217 / 250000000) := by
  have h := checkLog_sound (w := (78340201 / 19921659799)) (n := 12)
    (lo := (7864867 / 1000000000)) (hi := (1966217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9921659799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9921659799) = 1/(9921659799 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3648 : Bounds (-1966217 / 250000000) (-7864867 / 1000000000) (Real.log (9921659799 / 10000000000)) := by
  have h := reflection_log_3648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3649_neg : (44371111 / 250000000) ≤ -Real.log (500000000000 / 597104740589) ∧
    -Real.log (500000000000 / 597104740589) ≤ (35496889 / 200000000) := by
  have h := checkLog_sound (w := (97104740589 / 1097104740589)) (n := 12)
    (lo := (44371111 / 250000000)) (hi := (35496889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597104740589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597104740589 / 500000000000) = 1/(500000000000 / 597104740589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3649 : Bounds (44371111 / 250000000) (35496889 / 200000000) (Real.log (597104740589 / 500000000000)) := by
  have h := reflection_log_3649_neg
  have he : Real.log (597104740589 / 500000000000) = -Real.log (500000000000 / 597104740589) := by
    rw [show ((597104740589 / 500000000000) : ℝ) = ((500000000000 / 597104740589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3650_neg : (88971019 / 500000000) ≤ -Real.log (250000000000 / 298689017331) ∧
    -Real.log (250000000000 / 298689017331) ≤ (177942039 / 1000000000) := by
  have h := checkLog_sound (w := (48689017331 / 548689017331)) (n := 12)
    (lo := (88971019 / 500000000)) (hi := (177942039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298689017331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298689017331 / 250000000000) = 1/(250000000000 / 298689017331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3650 : Bounds (88971019 / 500000000) (177942039 / 1000000000) (Real.log (298689017331 / 250000000000)) := by
  have h := reflection_log_3650_neg
  have he : Real.log (298689017331 / 250000000000) = -Real.log (250000000000 / 298689017331) := by
    rw [show ((298689017331 / 250000000000) : ℝ) = ((250000000000 / 298689017331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3651_neg : (890291 / 2500000) ≤ -Real.log (31250000000 / 44617929109) ∧
    -Real.log (31250000000 / 44617929109) ≤ (356116401 / 1000000000) := by
  have h := checkLog_sound (w := (13367929109 / 75867929109)) (n := 12)
    (lo := (890291 / 2500000)) (hi := (356116401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44617929109 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44617929109 / 31250000000) = 1/(31250000000 / 44617929109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3651 : Bounds (890291 / 2500000) (356116401 / 1000000000) (Real.log (44617929109 / 31250000000)) := by
  have h := reflection_log_3651_neg
  have he : Real.log (44617929109 / 31250000000) = -Real.log (31250000000 / 44617929109) := by
    rw [show ((44617929109 / 31250000000) : ℝ) = ((31250000000 / 44617929109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3652_neg : (89080703 / 250000000) ≤ -Real.log (250000000000 / 357017117883) ∧
    -Real.log (250000000000 / 357017117883) ≤ (356322813 / 1000000000) := by
  have h := checkLog_sound (w := (107017117883 / 607017117883)) (n := 12)
    (lo := (89080703 / 250000000)) (hi := (356322813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357017117883 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357017117883 / 250000000000) = 1/(250000000000 / 357017117883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3652 : Bounds (89080703 / 250000000) (356322813 / 1000000000) (Real.log (357017117883 / 250000000000)) := by
  have h := reflection_log_3652_neg
  have he : Real.log (357017117883 / 250000000000) = -Real.log (250000000000 / 357017117883) := by
    rw [show ((357017117883 / 250000000000) : ℝ) = ((250000000000 / 357017117883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3653_neg : (162458927 / 1000000000) ≤ -Real.log (2500 / 2941) ∧
    -Real.log (2500 / 2941) ≤ (10153683 / 62500000) := by
  have h := checkLog_sound (w := (441 / 5441)) (n := 12)
    (lo := (162458927 / 1000000000)) (hi := (10153683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2941 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2941 / 2500) = 1/(2500 / 2941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3653 : Bounds (162458927 / 1000000000) (10153683 / 62500000) (Real.log (2941 / 2500)) := by
  have h := reflection_log_3653_neg
  have he : Real.log (2941 / 2500) = -Real.log (2500 / 2941) := by
    rw [show ((2941 / 2500) : ℝ) = ((2500 / 2941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3654_neg : (194070303 / 1000000000) ≤ -Real.log (2059 / 2500) ∧
    -Real.log (2059 / 2500) ≤ (6064697 / 31250000) := by
  have h := checkLog_sound (w := (441 / 4559)) (n := 12)
    (lo := (194070303 / 1000000000)) (hi := (6064697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2059) = 1/(2059 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3654 : Bounds (-6064697 / 31250000) (-194070303 / 1000000000) (Real.log (2059 / 2500)) := by
  have h := reflection_log_3654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3655_neg : (689 / 3906250) ≤ -Real.log (2500000 / 2500441) ∧
    -Real.log (2500000 / 2500441) ≤ (35277 / 200000000) := by
  have h := checkLog_sound (w := (441 / 5000441)) (n := 12)
    (lo := (689 / 3906250)) (hi := (35277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500441 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500441 / 2500000) = 1/(2500000 / 2500441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3655 : Bounds (689 / 3906250) (35277 / 200000000) (Real.log (2500441 / 2500000)) := by
  have h := reflection_log_3655_neg
  have he : Real.log (2500441 / 2500000) = -Real.log (2500000 / 2500441) := by
    rw [show ((2500441 / 2500000) : ℝ) = ((2500000 / 2500441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3656_neg : (35283 / 200000000) ≤ -Real.log (2499559 / 2500000) ∧
    -Real.log (2499559 / 2500000) ≤ (5513 / 31250000) := by
  have h := checkLog_sound (w := (441 / 4999559)) (n := 12)
    (lo := (35283 / 200000000)) (hi := (5513 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499559) = 1/(2499559 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3656 : Bounds (-5513 / 31250000) (-35283 / 200000000) (Real.log (2499559 / 2500000)) := by
  have h := reflection_log_3656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3657_neg : (84855721 / 1000000000) ≤ -Real.log (12500 / 13607) ∧
    -Real.log (12500 / 13607) ≤ (42427861 / 500000000) := by
  have h := checkLog_sound (w := (1107 / 26107)) (n := 12)
    (lo := (84855721 / 1000000000)) (hi := (42427861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13607 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13607 / 12500) = 1/(12500 / 13607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3657 : Bounds (84855721 / 1000000000) (42427861 / 500000000) (Real.log (13607 / 12500)) := by
  have h := reflection_log_3657_neg
  have he : Real.log (13607 / 12500) = -Real.log (12500 / 13607) := by
    rw [show ((13607 / 12500) : ℝ) = ((12500 / 13607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3658_neg : (11591189 / 125000000) ≤ -Real.log (11393 / 12500) ∧
    -Real.log (11393 / 12500) ≤ (92729513 / 1000000000) := by
  have h := checkLog_sound (w := (1107 / 23893)) (n := 12)
    (lo := (11591189 / 125000000)) (hi := (92729513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11393) = 1/(11393 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3658 : Bounds (-92729513 / 1000000000) (-11591189 / 125000000) (Real.log (11393 / 12500)) := by
  have h := reflection_log_3658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3659_neg : (1701303 / 20000000) ≤ -Real.log (250000 / 272197) ∧
    -Real.log (250000 / 272197) ≤ (85065151 / 1000000000) := by
  have h := checkLog_sound (w := (22197 / 522197)) (n := 12)
    (lo := (1701303 / 20000000)) (hi := (85065151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272197 / 250000) = 1/(250000 / 272197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3659 : Bounds (1701303 / 20000000) (85065151 / 1000000000) (Real.log (272197 / 250000)) := by
  have h := reflection_log_3659_neg
  have he : Real.log (272197 / 250000) = -Real.log (250000 / 272197) := by
    rw [show ((272197 / 250000) : ℝ) = ((250000 / 272197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3660_neg : (92979697 / 1000000000) ≤ -Real.log (227803 / 250000) ∧
    -Real.log (227803 / 250000) ≤ (46489849 / 500000000) := by
  have h := checkLog_sound (w := (22197 / 477803)) (n := 12)
    (lo := (92979697 / 1000000000)) (hi := (46489849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227803) = 1/(227803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3660 : Bounds (-46489849 / 500000000) (-92979697 / 1000000000) (Real.log (227803 / 250000)) := by
  have h := reflection_log_3660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3661_neg : (3957273 / 500000000) ≤ -Real.log (62007293191 / 62500000000) ∧
    -Real.log (62007293191 / 62500000000) ≤ (7914547 / 1000000000) := by
  have h := checkLog_sound (w := (492706809 / 124507293191)) (n := 12)
    (lo := (3957273 / 500000000)) (hi := (7914547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62007293191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62007293191) = 1/(62007293191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3661 : Bounds (-7914547 / 1000000000) (-3957273 / 500000000) (Real.log (62007293191 / 62500000000)) := by
  have h := reflection_log_3661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3662_neg : (787379 / 100000000) ≤ -Real.log (155024551 / 156250000) ∧
    -Real.log (155024551 / 156250000) ≤ (7873791 / 1000000000) := by
  have h := checkLog_sound (w := (1225449 / 311274551)) (n := 12)
    (lo := (787379 / 100000000)) (hi := (7873791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 155024551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 155024551) = 1/(155024551 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3662 : Bounds (-7873791 / 1000000000) (-787379 / 100000000) (Real.log (155024551 / 156250000)) := by
  have h := reflection_log_3662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3663_neg : (88792617 / 500000000) ≤ -Real.log (500000000000 / 597164925831) ∧
    -Real.log (500000000000 / 597164925831) ≤ (35517047 / 200000000) := by
  have h := checkLog_sound (w := (97164925831 / 1097164925831)) (n := 12)
    (lo := (88792617 / 500000000)) (hi := (35517047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597164925831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597164925831 / 500000000000) = 1/(500000000000 / 597164925831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3663 : Bounds (88792617 / 500000000) (35517047 / 200000000) (Real.log (597164925831 / 500000000000)) := by
  have h := reflection_log_3663_neg
  have he : Real.log (597164925831 / 500000000000) = -Real.log (500000000000 / 597164925831) := by
    rw [show ((597164925831 / 500000000000) : ℝ) = ((500000000000 / 597164925831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3664_neg : (11127803 / 62500000) ≤ -Real.log (250000000000 / 298719727133) ∧
    -Real.log (250000000000 / 298719727133) ≤ (178044849 / 1000000000) := by
  have h := checkLog_sound (w := (48719727133 / 548719727133)) (n := 12)
    (lo := (11127803 / 62500000)) (hi := (178044849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298719727133 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298719727133 / 250000000000) = 1/(250000000000 / 298719727133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3664 : Bounds (11127803 / 62500000) (178044849 / 1000000000) (Real.log (298719727133 / 250000000000)) := by
  have h := reflection_log_3664_neg
  have he : Real.log (298719727133 / 250000000000) = -Real.log (250000000000 / 298719727133) := by
    rw [show ((298719727133 / 250000000000) : ℝ) = ((250000000000 / 298719727133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3665_neg : (89080703 / 250000000) ≤ -Real.log (100000000000 / 142806847153) ∧
    -Real.log (100000000000 / 142806847153) ≤ (356322813 / 1000000000) := by
  have h := checkLog_sound (w := (42806847153 / 242806847153)) (n := 12)
    (lo := (89080703 / 250000000)) (hi := (356322813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142806847153 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142806847153 / 100000000000) = 1/(100000000000 / 142806847153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3665 : Bounds (89080703 / 250000000) (356322813 / 1000000000) (Real.log (142806847153 / 100000000000)) := by
  have h := reflection_log_3665_neg
  have he : Real.log (142806847153 / 100000000000) = -Real.log (100000000000 / 142806847153) := by
    rw [show ((142806847153 / 100000000000) : ℝ) = ((100000000000 / 142806847153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3666_neg : (356529231 / 1000000000) ≤ -Real.log (250000000000 / 357090820787) ∧
    -Real.log (250000000000 / 357090820787) ≤ (22283077 / 62500000) := by
  have h := checkLog_sound (w := (107090820787 / 607090820787)) (n := 12)
    (lo := (356529231 / 1000000000)) (hi := (22283077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357090820787 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357090820787 / 250000000000) = 1/(250000000000 / 357090820787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3666 : Bounds (356529231 / 1000000000) (22283077 / 62500000) (Real.log (357090820787 / 250000000000)) := by
  have h := reflection_log_3666_neg
  have he : Real.log (357090820787 / 250000000000) = -Real.log (250000000000 / 357090820787) := by
    rw [show ((357090820787 / 250000000000) : ℝ) = ((250000000000 / 357090820787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3667_neg : (162543929 / 1000000000) ≤ -Real.log (2000 / 2353) ∧
    -Real.log (2000 / 2353) ≤ (16254393 / 100000000) := by
  have h := checkLog_sound (w := (353 / 4353)) (n := 12)
    (lo := (162543929 / 1000000000)) (hi := (16254393 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 2000) = 1/(2000 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3667 : Bounds (162543929 / 1000000000) (16254393 / 100000000) (Real.log (2353 / 2000)) := by
  have h := reflection_log_3667_neg
  have he : Real.log (2353 / 2000) = -Real.log (2000 / 2353) := by
    rw [show ((2353 / 2000) : ℝ) = ((2000 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3668_neg : (194191729 / 1000000000) ≤ -Real.log (1647 / 2000) ∧
    -Real.log (1647 / 2000) ≤ (19419173 / 100000000) := by
  have h := checkLog_sound (w := (353 / 3647)) (n := 12)
    (lo := (194191729 / 1000000000)) (hi := (19419173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1647) = 1/(1647 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3668 : Bounds (-19419173 / 100000000) (-194191729 / 1000000000) (Real.log (1647 / 2000)) := by
  have h := reflection_log_3668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3669_neg : (44121 / 250000000) ≤ -Real.log (2000000 / 2000353) ∧
    -Real.log (2000000 / 2000353) ≤ (35297 / 200000000) := by
  have h := checkLog_sound (w := (353 / 4000353)) (n := 12)
    (lo := (44121 / 250000000)) (hi := (35297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000353 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000353 / 2000000) = 1/(2000000 / 2000353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3669 : Bounds (44121 / 250000000) (35297 / 200000000) (Real.log (2000353 / 2000000)) := by
  have h := reflection_log_3669_neg
  have he : Real.log (2000353 / 2000000) = -Real.log (2000000 / 2000353) := by
    rw [show ((2000353 / 2000000) : ℝ) = ((2000000 / 2000353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3670_neg : (35303 / 200000000) ≤ -Real.log (1999647 / 2000000) ∧
    -Real.log (1999647 / 2000000) ≤ (44129 / 250000000) := by
  have h := checkLog_sound (w := (353 / 3999647)) (n := 12)
    (lo := (35303 / 200000000)) (hi := (44129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999647) = 1/(1999647 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3670 : Bounds (-44129 / 250000000) (-35303 / 200000000) (Real.log (1999647 / 2000000)) := by
  have h := reflection_log_3670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3671_neg : (84902571 / 1000000000) ≤ -Real.log (1000000 / 1088611) ∧
    -Real.log (1000000 / 1088611) ≤ (21225643 / 250000000) := by
  have h := checkLog_sound (w := (88611 / 2088611)) (n := 12)
    (lo := (84902571 / 1000000000)) (hi := (21225643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088611 / 1000000) = 1/(1000000 / 1088611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3671 : Bounds (84902571 / 1000000000) (21225643 / 250000000) (Real.log (1088611 / 1000000)) := by
  have h := reflection_log_3671_neg
  have he : Real.log (1088611 / 1000000) = -Real.log (1000000 / 1088611) := by
    rw [show ((1088611 / 1000000) : ℝ) = ((1000000 / 1088611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3672_neg : (92785469 / 1000000000) ≤ -Real.log (911389 / 1000000) ∧
    -Real.log (911389 / 1000000) ≤ (9278547 / 100000000) := by
  have h := checkLog_sound (w := (88611 / 1911389)) (n := 12)
    (lo := (92785469 / 1000000000)) (hi := (9278547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911389) = 1/(911389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3672 : Bounds (-9278547 / 100000000) (-92785469 / 1000000000) (Real.log (911389 / 1000000)) := by
  have h := reflection_log_3672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3673_neg : (8511199 / 100000000) ≤ -Real.log (1000000 / 1088839) ∧
    -Real.log (1000000 / 1088839) ≤ (85111991 / 1000000000) := by
  have h := checkLog_sound (w := (88839 / 2088839)) (n := 12)
    (lo := (8511199 / 100000000)) (hi := (85111991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088839 / 1000000) = 1/(1000000 / 1088839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3673 : Bounds (8511199 / 100000000) (85111991 / 1000000000) (Real.log (1088839 / 1000000)) := by
  have h := reflection_log_3673_neg
  have he : Real.log (1088839 / 1000000) = -Real.log (1000000 / 1088839) := by
    rw [show ((1088839 / 1000000) : ℝ) = ((1000000 / 1088839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3674_neg : (23258917 / 250000000) ≤ -Real.log (911161 / 1000000) ∧
    -Real.log (911161 / 1000000) ≤ (93035669 / 1000000000) := by
  have h := checkLog_sound (w := (88839 / 1911161)) (n := 12)
    (lo := (23258917 / 250000000)) (hi := (93035669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911161) = 1/(911161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3674 : Bounds (-93035669 / 1000000000) (-23258917 / 250000000) (Real.log (911161 / 1000000)) := by
  have h := reflection_log_3674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3675_neg : (7923677 / 1000000000) ≤ -Real.log (992107632079 / 1000000000000) ∧
    -Real.log (992107632079 / 1000000000000) ≤ (3961839 / 500000000) := by
  have h := checkLog_sound (w := (7892367921 / 1992107632079)) (n := 12)
    (lo := (7923677 / 1000000000)) (hi := (3961839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992107632079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992107632079) = 1/(992107632079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3675 : Bounds (-3961839 / 500000000) (-7923677 / 1000000000) (Real.log (992107632079 / 1000000000000)) := by
  have h := reflection_log_3675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3676_neg : (7882897 / 1000000000) ≤ -Real.log (992148090679 / 1000000000000) ∧
    -Real.log (992148090679 / 1000000000000) ≤ (3941449 / 500000000) := by
  have h := checkLog_sound (w := (7851909321 / 1992148090679)) (n := 12)
    (lo := (7882897 / 1000000000)) (hi := (3941449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992148090679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992148090679) = 1/(992148090679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3676 : Bounds (-3941449 / 500000000) (-7882897 / 1000000000) (Real.log (992148090679 / 1000000000000)) := by
  have h := reflection_log_3676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3677_neg : (177688041 / 1000000000) ≤ -Real.log (500000000000 / 597226321581) ∧
    -Real.log (500000000000 / 597226321581) ≤ (88844021 / 500000000) := by
  have h := checkLog_sound (w := (97226321581 / 1097226321581)) (n := 12)
    (lo := (177688041 / 1000000000)) (hi := (88844021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597226321581 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597226321581 / 500000000000) = 1/(500000000000 / 597226321581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3677 : Bounds (177688041 / 1000000000) (88844021 / 500000000) (Real.log (597226321581 / 500000000000)) := by
  have h := reflection_log_3677_neg
  have he : Real.log (597226321581 / 500000000000) = -Real.log (500000000000 / 597226321581) := by
    rw [show ((597226321581 / 500000000000) : ℝ) = ((500000000000 / 597226321581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3678_neg : (178147659 / 1000000000) ≤ -Real.log (100000000000 / 119500176149) ∧
    -Real.log (100000000000 / 119500176149) ≤ (8907383 / 50000000) := by
  have h := checkLog_sound (w := (19500176149 / 219500176149)) (n := 12)
    (lo := (178147659 / 1000000000)) (hi := (8907383 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119500176149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119500176149 / 100000000000) = 1/(100000000000 / 119500176149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3678 : Bounds (178147659 / 1000000000) (8907383 / 50000000) (Real.log (119500176149 / 100000000000)) := by
  have h := reflection_log_3678_neg
  have he : Real.log (119500176149 / 100000000000) = -Real.log (100000000000 / 119500176149) := by
    rw [show ((119500176149 / 100000000000) : ℝ) = ((100000000000 / 119500176149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3679_neg : (356529231 / 1000000000) ≤ -Real.log (500000000000 / 714181641573) ∧
    -Real.log (500000000000 / 714181641573) ≤ (22283077 / 62500000) := by
  have h := checkLog_sound (w := (214181641573 / 1214181641573)) (n := 12)
    (lo := (356529231 / 1000000000)) (hi := (22283077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714181641573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714181641573 / 500000000000) = 1/(500000000000 / 714181641573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3679 : Bounds (356529231 / 1000000000) (22283077 / 62500000) (Real.log (714181641573 / 500000000000)) := by
  have h := reflection_log_3679_neg
  have he : Real.log (714181641573 / 500000000000) = -Real.log (500000000000 / 714181641573) := by
    rw [show ((714181641573 / 500000000000) : ℝ) = ((500000000000 / 714181641573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3680_neg : (178367829 / 500000000) ≤ -Real.log (250000000000 / 357164541591) ∧
    -Real.log (250000000000 / 357164541591) ≤ (356735659 / 1000000000) := by
  have h := checkLog_sound (w := (107164541591 / 607164541591)) (n := 12)
    (lo := (178367829 / 500000000)) (hi := (356735659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357164541591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357164541591 / 250000000000) = 1/(250000000000 / 357164541591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3680 : Bounds (178367829 / 500000000) (356735659 / 1000000000) (Real.log (357164541591 / 250000000000)) := by
  have h := reflection_log_3680_neg
  have he : Real.log (357164541591 / 250000000000) = -Real.log (250000000000 / 357164541591) := by
    rw [show ((357164541591 / 250000000000) : ℝ) = ((250000000000 / 357164541591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3681_neg : (162628923 / 1000000000) ≤ -Real.log (5000 / 5883) ∧
    -Real.log (5000 / 5883) ≤ (40657231 / 250000000) := by
  have h := checkLog_sound (w := (883 / 10883)) (n := 12)
    (lo := (162628923 / 1000000000)) (hi := (40657231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5883 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5883 / 5000) = 1/(5000 / 5883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3681 : Bounds (162628923 / 1000000000) (40657231 / 250000000) (Real.log (5883 / 5000)) := by
  have h := reflection_log_3681_neg
  have he : Real.log (5883 / 5000) = -Real.log (5000 / 5883) := by
    rw [show ((5883 / 5000) : ℝ) = ((5000 / 5883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3682_neg : (194313169 / 1000000000) ≤ -Real.log (4117 / 5000) ∧
    -Real.log (4117 / 5000) ≤ (19431317 / 100000000) := by
  have h := checkLog_sound (w := (883 / 9117)) (n := 12)
    (lo := (194313169 / 1000000000)) (hi := (19431317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4117) = 1/(4117 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3682 : Bounds (-19431317 / 100000000) (-194313169 / 1000000000) (Real.log (4117 / 5000)) := by
  have h := reflection_log_3682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3683_neg : (22073 / 125000000) ≤ -Real.log (5000000 / 5000883) ∧
    -Real.log (5000000 / 5000883) ≤ (35317 / 200000000) := by
  have h := checkLog_sound (w := (883 / 10000883)) (n := 12)
    (lo := (22073 / 125000000)) (hi := (35317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000883 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000883 / 5000000) = 1/(5000000 / 5000883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3683 : Bounds (22073 / 125000000) (35317 / 200000000) (Real.log (5000883 / 5000000)) := by
  have h := reflection_log_3683_neg
  have he : Real.log (5000883 / 5000000) = -Real.log (5000000 / 5000883) := by
    rw [show ((5000883 / 5000000) : ℝ) = ((5000000 / 5000883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3684_neg : (35323 / 200000000) ≤ -Real.log (4999117 / 5000000) ∧
    -Real.log (4999117 / 5000000) ≤ (22077 / 125000000) := by
  have h := checkLog_sound (w := (883 / 9999117)) (n := 12)
    (lo := (35323 / 200000000)) (hi := (22077 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999117) = 1/(4999117 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3684 : Bounds (-22077 / 125000000) (-35323 / 200000000) (Real.log (4999117 / 5000000)) := by
  have h := reflection_log_3684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3685_neg : (84949419 / 1000000000) ≤ -Real.log (500000 / 544331) ∧
    -Real.log (500000 / 544331) ≤ (4247471 / 50000000) := by
  have h := checkLog_sound (w := (44331 / 1044331)) (n := 12)
    (lo := (84949419 / 1000000000)) (hi := (4247471 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544331 / 500000) = 1/(500000 / 544331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3685 : Bounds (84949419 / 1000000000) (4247471 / 50000000) (Real.log (544331 / 500000)) := by
  have h := reflection_log_3685_neg
  have he : Real.log (544331 / 500000) = -Real.log (500000 / 544331) := by
    rw [show ((544331 / 500000) : ℝ) = ((500000 / 544331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3686_neg : (92841429 / 1000000000) ≤ -Real.log (455669 / 500000) ∧
    -Real.log (455669 / 500000) ≤ (9284143 / 100000000) := by
  have h := checkLog_sound (w := (44331 / 955669)) (n := 12)
    (lo := (92841429 / 1000000000)) (hi := (9284143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455669) = 1/(455669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3686 : Bounds (-9284143 / 100000000) (-92841429 / 1000000000) (Real.log (455669 / 500000)) := by
  have h := reflection_log_3686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3687_neg : (8515791 / 100000000) ≤ -Real.log (1000000 / 1088889) ∧
    -Real.log (1000000 / 1088889) ≤ (85157911 / 1000000000) := by
  have h := checkLog_sound (w := (88889 / 2088889)) (n := 12)
    (lo := (8515791 / 100000000)) (hi := (85157911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088889 / 1000000) = 1/(1000000 / 1088889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3687 : Bounds (8515791 / 100000000) (85157911 / 1000000000) (Real.log (1088889 / 1000000)) := by
  have h := reflection_log_3687_neg
  have he : Real.log (1088889 / 1000000) = -Real.log (1000000 / 1088889) := by
    rw [show ((1088889 / 1000000) : ℝ) = ((1000000 / 1088889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3688_neg : (18618109 / 200000000) ≤ -Real.log (911111 / 1000000) ∧
    -Real.log (911111 / 1000000) ≤ (46545273 / 500000000) := by
  have h := checkLog_sound (w := (88889 / 1911111)) (n := 12)
    (lo := (18618109 / 200000000)) (hi := (46545273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911111) = 1/(911111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3688 : Bounds (-46545273 / 500000000) (-18618109 / 200000000) (Real.log (911111 / 1000000)) := by
  have h := reflection_log_3688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3689_neg : (3966317 / 500000000) ≤ -Real.log (992098745679 / 1000000000000) ∧
    -Real.log (992098745679 / 1000000000000) ≤ (1586527 / 200000000) := by
  have h := checkLog_sound (w := (7901254321 / 1992098745679)) (n := 12)
    (lo := (3966317 / 500000000)) (hi := (1586527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992098745679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992098745679) = 1/(992098745679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3689 : Bounds (-1586527 / 200000000) (-3966317 / 500000000) (Real.log (992098745679 / 1000000000000)) := by
  have h := reflection_log_3689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3690_neg : (789201 / 100000000) ≤ -Real.log (248034762439 / 250000000000) ∧
    -Real.log (248034762439 / 250000000000) ≤ (7892011 / 1000000000) := by
  have h := checkLog_sound (w := (1965237561 / 498034762439)) (n := 12)
    (lo := (789201 / 100000000)) (hi := (7892011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248034762439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248034762439) = 1/(248034762439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3690 : Bounds (-7892011 / 1000000000) (-789201 / 100000000) (Real.log (248034762439 / 250000000000)) := by
  have h := reflection_log_3690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3691_neg : (1388991 / 7812500) ≤ -Real.log (500000000000 / 597287724203) ∧
    -Real.log (500000000000 / 597287724203) ≤ (177790849 / 1000000000) := by
  have h := checkLog_sound (w := (97287724203 / 1097287724203)) (n := 12)
    (lo := (1388991 / 7812500)) (hi := (177790849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597287724203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597287724203 / 500000000000) = 1/(500000000000 / 597287724203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3691 : Bounds (1388991 / 7812500) (177790849 / 1000000000) (Real.log (597287724203 / 500000000000)) := by
  have h := reflection_log_3691_neg
  have he : Real.log (597287724203 / 500000000000) = -Real.log (500000000000 / 597287724203) := by
    rw [show ((597287724203 / 500000000000) : ℝ) = ((500000000000 / 597287724203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3692_neg : (35649691 / 200000000) ≤ -Real.log (500000000000 / 597561109459) ∧
    -Real.log (500000000000 / 597561109459) ≤ (22281057 / 125000000) := by
  have h := checkLog_sound (w := (97561109459 / 1097561109459)) (n := 12)
    (lo := (35649691 / 200000000)) (hi := (22281057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597561109459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597561109459 / 500000000000) = 1/(500000000000 / 597561109459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3692 : Bounds (35649691 / 200000000) (22281057 / 125000000) (Real.log (597561109459 / 500000000000)) := by
  have h := reflection_log_3692_neg
  have he : Real.log (597561109459 / 500000000000) = -Real.log (500000000000 / 597561109459) := by
    rw [show ((597561109459 / 500000000000) : ℝ) = ((500000000000 / 597561109459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3693_neg : (178367829 / 500000000) ≤ -Real.log (500000000000 / 714329083181) ∧
    -Real.log (500000000000 / 714329083181) ≤ (356735659 / 1000000000) := by
  have h := checkLog_sound (w := (214329083181 / 1214329083181)) (n := 12)
    (lo := (178367829 / 500000000)) (hi := (356735659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714329083181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714329083181 / 500000000000) = 1/(500000000000 / 714329083181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3693 : Bounds (178367829 / 500000000) (356735659 / 1000000000) (Real.log (714329083181 / 500000000000)) := by
  have h := reflection_log_3693_neg
  have he : Real.log (714329083181 / 500000000000) = -Real.log (500000000000 / 714329083181) := by
    rw [show ((714329083181 / 500000000000) : ℝ) = ((500000000000 / 714329083181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3694_neg : (356942093 / 1000000000) ≤ -Real.log (500000000000 / 714476560603) ∧
    -Real.log (500000000000 / 714476560603) ≤ (178471047 / 500000000) := by
  have h := checkLog_sound (w := (214476560603 / 1214476560603)) (n := 12)
    (lo := (356942093 / 1000000000)) (hi := (178471047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714476560603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714476560603 / 500000000000) = 1/(500000000000 / 714476560603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3694 : Bounds (356942093 / 1000000000) (178471047 / 500000000) (Real.log (714476560603 / 500000000000)) := by
  have h := reflection_log_3694_neg
  have he : Real.log (714476560603 / 500000000000) = -Real.log (500000000000 / 714476560603) := by
    rw [show ((714476560603 / 500000000000) : ℝ) = ((500000000000 / 714476560603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3695_neg : (16271391 / 100000000) ≤ -Real.log (10000 / 11767) ∧
    -Real.log (10000 / 11767) ≤ (162713911 / 1000000000) := by
  have h := checkLog_sound (w := (1767 / 21767)) (n := 12)
    (lo := (16271391 / 100000000)) (hi := (162713911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11767 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11767 / 10000) = 1/(10000 / 11767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3695 : Bounds (16271391 / 100000000) (162713911 / 1000000000) (Real.log (11767 / 10000)) := by
  have h := reflection_log_3695_neg
  have he : Real.log (11767 / 10000) = -Real.log (10000 / 11767) := by
    rw [show ((11767 / 10000) : ℝ) = ((10000 / 11767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3696_neg : (3038041 / 15625000) ≤ -Real.log (8233 / 10000) ∧
    -Real.log (8233 / 10000) ≤ (1555477 / 8000000) := by
  have h := checkLog_sound (w := (1767 / 18233)) (n := 12)
    (lo := (3038041 / 15625000)) (hi := (1555477 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8233) = 1/(8233 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3696 : Bounds (-1555477 / 8000000) (-3038041 / 15625000) (Real.log (8233 / 10000)) := by
  have h := reflection_log_3696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3697_neg : (44171 / 250000000) ≤ -Real.log (10000000 / 10001767) ∧
    -Real.log (10000000 / 10001767) ≤ (35337 / 200000000) := by
  have h := checkLog_sound (w := (1767 / 20001767)) (n := 12)
    (lo := (44171 / 250000000)) (hi := (35337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001767 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001767 / 10000000) = 1/(10000000 / 10001767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3697 : Bounds (44171 / 250000000) (35337 / 200000000) (Real.log (10001767 / 10000000)) := by
  have h := reflection_log_3697_neg
  have he : Real.log (10001767 / 10000000) = -Real.log (10000000 / 10001767) := by
    rw [show ((10001767 / 10000000) : ℝ) = ((10000000 / 10001767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3698_neg : (35343 / 200000000) ≤ -Real.log (9998233 / 10000000) ∧
    -Real.log (9998233 / 10000000) ≤ (44179 / 250000000) := by
  have h := checkLog_sound (w := (1767 / 19998233)) (n := 12)
    (lo := (35343 / 200000000)) (hi := (44179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998233) = 1/(9998233 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3698 : Bounds (-44179 / 250000000) (-35343 / 200000000) (Real.log (9998233 / 10000000)) := by
  have h := reflection_log_3698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3699_neg : (10624533 / 125000000) ≤ -Real.log (1000000 / 1088713) ∧
    -Real.log (1000000 / 1088713) ≤ (16999253 / 200000000) := by
  have h := checkLog_sound (w := (88713 / 2088713)) (n := 12)
    (lo := (10624533 / 125000000)) (hi := (16999253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088713 / 1000000) = 1/(1000000 / 1088713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3699 : Bounds (10624533 / 125000000) (16999253 / 200000000) (Real.log (1088713 / 1000000)) := by
  have h := reflection_log_3699_neg
  have he : Real.log (1088713 / 1000000) = -Real.log (1000000 / 1088713) := by
    rw [show ((1088713 / 1000000) : ℝ) = ((1000000 / 1088713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3700_neg : (5806087 / 62500000) ≤ -Real.log (911287 / 1000000) ∧
    -Real.log (911287 / 1000000) ≤ (92897393 / 1000000000) := by
  have h := checkLog_sound (w := (88713 / 1911287)) (n := 12)
    (lo := (5806087 / 62500000)) (hi := (92897393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911287) = 1/(911287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3700 : Bounds (-92897393 / 1000000000) (-5806087 / 62500000) (Real.log (911287 / 1000000)) := by
  have h := reflection_log_3700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3701_neg : (42602373 / 500000000) ≤ -Real.log (50000 / 54447) ∧
    -Real.log (50000 / 54447) ≤ (85204747 / 1000000000) := by
  have h := checkLog_sound (w := (4447 / 104447)) (n := 12)
    (lo := (42602373 / 500000000)) (hi := (85204747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54447 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54447 / 50000) = 1/(50000 / 54447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3701 : Bounds (42602373 / 500000000) (85204747 / 1000000000) (Real.log (54447 / 50000)) := by
  have h := reflection_log_3701_neg
  have he : Real.log (54447 / 50000) = -Real.log (50000 / 54447) := by
    rw [show ((54447 / 50000) : ℝ) = ((50000 / 54447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3702_neg : (46573261 / 500000000) ≤ -Real.log (45553 / 50000) ∧
    -Real.log (45553 / 50000) ≤ (93146523 / 1000000000) := by
  have h := checkLog_sound (w := (4447 / 95553)) (n := 12)
    (lo := (46573261 / 500000000)) (hi := (93146523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45553) = 1/(45553 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3702 : Bounds (-93146523 / 1000000000) (-46573261 / 500000000) (Real.log (45553 / 50000)) := by
  have h := reflection_log_3702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3703_neg : (496361 / 62500000) ≤ -Real.log (2480224191 / 2500000000) ∧
    -Real.log (2480224191 / 2500000000) ≤ (7941777 / 1000000000) := by
  have h := checkLog_sound (w := (19775809 / 4980224191)) (n := 12)
    (lo := (496361 / 62500000)) (hi := (7941777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2480224191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2480224191) = 1/(2480224191 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3703 : Bounds (-7941777 / 1000000000) (-496361 / 62500000) (Real.log (2480224191 / 2500000000)) := by
  have h := reflection_log_3703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3704_neg : (987641 / 125000000) ≤ -Real.log (992130003631 / 1000000000000) ∧
    -Real.log (992130003631 / 1000000000000) ≤ (7901129 / 1000000000) := by
  have h := checkLog_sound (w := (7869996369 / 1992130003631)) (n := 12)
    (lo := (987641 / 125000000)) (hi := (7901129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992130003631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992130003631) = 1/(992130003631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3704 : Bounds (-7901129 / 1000000000) (-987641 / 125000000) (Real.log (992130003631 / 1000000000000)) := by
  have h := reflection_log_3704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3705_neg : (177893657 / 1000000000) ≤ -Real.log (500000000000 / 597349133697) ∧
    -Real.log (500000000000 / 597349133697) ≤ (88946829 / 500000000) := by
  have h := checkLog_sound (w := (97349133697 / 1097349133697)) (n := 12)
    (lo := (177893657 / 1000000000)) (hi := (88946829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597349133697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597349133697 / 500000000000) = 1/(500000000000 / 597349133697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3705 : Bounds (177893657 / 1000000000) (88946829 / 500000000) (Real.log (597349133697 / 500000000000)) := by
  have h := reflection_log_3705_neg
  have he : Real.log (597349133697 / 500000000000) = -Real.log (500000000000 / 597349133697) := by
    rw [show ((597349133697 / 500000000000) : ℝ) = ((500000000000 / 597349133697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3706_neg : (44587817 / 250000000) ≤ -Real.log (250000000000 / 298811274779) ∧
    -Real.log (250000000000 / 298811274779) ≤ (178351269 / 1000000000) := by
  have h := checkLog_sound (w := (48811274779 / 548811274779)) (n := 12)
    (lo := (44587817 / 250000000)) (hi := (178351269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298811274779 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298811274779 / 250000000000) = 1/(250000000000 / 298811274779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3706 : Bounds (44587817 / 250000000) (178351269 / 1000000000) (Real.log (298811274779 / 250000000000)) := by
  have h := reflection_log_3706_neg
  have he : Real.log (298811274779 / 250000000000) = -Real.log (250000000000 / 298811274779) := by
    rw [show ((298811274779 / 250000000000) : ℝ) = ((250000000000 / 298811274779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3707_neg : (356942093 / 1000000000) ≤ -Real.log (250000000000 / 357238280301) ∧
    -Real.log (250000000000 / 357238280301) ≤ (178471047 / 500000000) := by
  have h := checkLog_sound (w := (107238280301 / 607238280301)) (n := 12)
    (lo := (356942093 / 1000000000)) (hi := (178471047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357238280301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357238280301 / 250000000000) = 1/(250000000000 / 357238280301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3707 : Bounds (356942093 / 1000000000) (178471047 / 500000000) (Real.log (357238280301 / 250000000000)) := by
  have h := reflection_log_3707_neg
  have he : Real.log (357238280301 / 250000000000) = -Real.log (250000000000 / 357238280301) := by
    rw [show ((357238280301 / 250000000000) : ℝ) = ((250000000000 / 357238280301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3708_neg : (71429707 / 200000000) ≤ -Real.log (10000000000 / 14292481477) ∧
    -Real.log (10000000000 / 14292481477) ≤ (44643567 / 125000000) := by
  have h := checkLog_sound (w := (4292481477 / 24292481477)) (n := 12)
    (lo := (71429707 / 200000000)) (hi := (44643567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14292481477 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14292481477 / 10000000000) = 1/(10000000000 / 14292481477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3708 : Bounds (71429707 / 200000000) (44643567 / 125000000) (Real.log (14292481477 / 10000000000)) := by
  have h := reflection_log_3708_neg
  have he : Real.log (14292481477 / 10000000000) = -Real.log (10000000000 / 14292481477) := by
    rw [show ((14292481477 / 10000000000) : ℝ) = ((10000000000 / 14292481477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3709_neg : (16279889 / 100000000) ≤ -Real.log (1250 / 1471) ∧
    -Real.log (1250 / 1471) ≤ (162798891 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2721)) (n := 12)
    (lo := (16279889 / 100000000)) (hi := (162798891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471 / 1250) = 1/(1250 / 1471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3709 : Bounds (16279889 / 100000000) (162798891 / 1000000000) (Real.log (1471 / 1250)) := by
  have h := reflection_log_3709_neg
  have he : Real.log (1471 / 1250) = -Real.log (1250 / 1471) := by
    rw [show ((1471 / 1250) : ℝ) = ((1250 / 1471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3710_neg : (97278047 / 500000000) ≤ -Real.log (1029 / 1250) ∧
    -Real.log (1029 / 1250) ≤ (38911219 / 200000000) := by
  have h := checkLog_sound (w := (221 / 2279)) (n := 12)
    (lo := (97278047 / 500000000)) (hi := (38911219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1029) = 1/(1029 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3710 : Bounds (-38911219 / 200000000) (-97278047 / 500000000) (Real.log (1029 / 1250)) := by
  have h := reflection_log_3710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3711_neg : (11049 / 62500000) ≤ -Real.log (1250000 / 1250221) ∧
    -Real.log (1250000 / 1250221) ≤ (35357 / 200000000) := by
  have h := checkLog_sound (w := (221 / 2500221)) (n := 12)
    (lo := (11049 / 62500000)) (hi := (35357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250221 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250221 / 1250000) = 1/(1250000 / 1250221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3711 : Bounds (11049 / 62500000) (35357 / 200000000) (Real.log (1250221 / 1250000)) := by
  have h := reflection_log_3711_neg
  have he : Real.log (1250221 / 1250000) = -Real.log (1250000 / 1250221) := by
    rw [show ((1250221 / 1250000) : ℝ) = ((1250000 / 1250221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
