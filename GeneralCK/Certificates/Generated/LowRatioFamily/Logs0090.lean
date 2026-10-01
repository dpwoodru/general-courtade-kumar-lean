import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5760_neg : (9343221 / 1000000000) ≤ -Real.log (39628011631 / 40000000000) ∧
    -Real.log (39628011631 / 40000000000) ≤ (4671611 / 500000000) := by
  have h := checkLog_sound (w := (371988369 / 79628011631)) (n := 12)
    (lo := (9343221 / 1000000000)) (hi := (4671611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39628011631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39628011631) = 1/(39628011631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5760 : Bounds (-4671611 / 500000000) (-9343221 / 1000000000) (Real.log (39628011631 / 40000000000)) := by
  have h := reflection_log_5760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5761_neg : (9296169 / 1000000000) ≤ -Real.log (990746906751 / 1000000000000) ∧
    -Real.log (990746906751 / 1000000000000) ≤ (929617 / 100000000) := by
  have h := checkLog_sound (w := (9253093249 / 1990746906751)) (n := 12)
    (lo := (9296169 / 1000000000)) (hi := (929617 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990746906751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990746906751) = 1/(990746906751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5761 : Bounds (-929617 / 100000000) (-9296169 / 1000000000) (Real.log (990746906751 / 1000000000000)) := by
  have h := reflection_log_5761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5762_neg : (12061419 / 62500000) ≤ -Real.log (31250000000 / 37901931773) ∧
    -Real.log (31250000000 / 37901931773) ≤ (38596541 / 200000000) := by
  have h := checkLog_sound (w := (6651931773 / 69151931773)) (n := 12)
    (lo := (12061419 / 62500000)) (hi := (38596541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37901931773 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37901931773 / 31250000000) = 1/(31250000000 / 37901931773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5762 : Bounds (12061419 / 62500000) (38596541 / 200000000) (Real.log (37901931773 / 31250000000)) := by
  have h := reflection_log_5762_neg
  have he : Real.log (37901931773 / 31250000000) = -Real.log (31250000000 / 37901931773) := by
    rw [show ((37901931773 / 31250000000) : ℝ) = ((31250000000 / 37901931773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5763_neg : (48367809 / 250000000) ≤ -Real.log (250000000000 / 303363620769) ∧
    -Real.log (250000000000 / 303363620769) ≤ (193471237 / 1000000000) := by
  have h := checkLog_sound (w := (53363620769 / 553363620769)) (n := 12)
    (lo := (48367809 / 250000000)) (hi := (193471237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303363620769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303363620769 / 250000000000) = 1/(250000000000 / 303363620769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5763 : Bounds (48367809 / 250000000) (193471237 / 1000000000) (Real.log (303363620769 / 250000000000)) := by
  have h := reflection_log_5763_neg
  have he : Real.log (303363620769 / 250000000000) = -Real.log (250000000000 / 303363620769) := by
    rw [show ((303363620769 / 250000000000) : ℝ) = ((250000000000 / 303363620769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5764_neg : (193686203 / 500000000) ≤ -Real.log (500000000000 / 736552491653) ∧
    -Real.log (500000000000 / 736552491653) ≤ (387372407 / 1000000000) := by
  have h := checkLog_sound (w := (236552491653 / 1236552491653)) (n := 12)
    (lo := (193686203 / 500000000)) (hi := (387372407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736552491653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736552491653 / 500000000000) = 1/(500000000000 / 736552491653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5764 : Bounds (193686203 / 500000000) (387372407 / 1000000000) (Real.log (736552491653 / 500000000000)) := by
  have h := reflection_log_5764_neg
  have he : Real.log (736552491653 / 500000000000) = -Real.log (500000000000 / 736552491653) := by
    rw [show ((736552491653 / 500000000000) : ℝ) = ((500000000000 / 736552491653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5765_neg : (387580007 / 1000000000) ≤ -Real.log (50000000000 / 73670541677) ∧
    -Real.log (50000000000 / 73670541677) ≤ (48447501 / 125000000) := by
  have h := checkLog_sound (w := (23670541677 / 123670541677)) (n := 12)
    (lo := (387580007 / 1000000000)) (hi := (48447501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73670541677 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73670541677 / 50000000000) = 1/(50000000000 / 73670541677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5765 : Bounds (387580007 / 1000000000) (48447501 / 125000000) (Real.log (73670541677 / 50000000000)) := by
  have h := reflection_log_5765_neg
  have he : Real.log (73670541677 / 50000000000) = -Real.log (50000000000 / 73670541677) := by
    rw [show ((73670541677 / 50000000000) : ℝ) = ((50000000000 / 73670541677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5766_neg : (175213017 / 1000000000) ≤ -Real.log (2000 / 2383) ∧
    -Real.log (2000 / 2383) ≤ (87606509 / 500000000) := by
  have h := checkLog_sound (w := (383 / 4383)) (n := 12)
    (lo := (175213017 / 1000000000)) (hi := (87606509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 2000) = 1/(2000 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5766 : Bounds (175213017 / 1000000000) (87606509 / 500000000) (Real.log (2383 / 2000)) := by
  have h := reflection_log_5766_neg
  have he : Real.log (2383 / 2000) = -Real.log (2000 / 2383) := by
    rw [show ((2383 / 2000) : ℝ) = ((2000 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5767_neg : (212574599 / 1000000000) ≤ -Real.log (1617 / 2000) ∧
    -Real.log (1617 / 2000) ≤ (1062873 / 5000000) := by
  have h := checkLog_sound (w := (383 / 3617)) (n := 12)
    (lo := (212574599 / 1000000000)) (hi := (1062873 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1617) = 1/(1617 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5767 : Bounds (-1062873 / 5000000) (-212574599 / 1000000000) (Real.log (1617 / 2000)) := by
  have h := reflection_log_5767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5768_neg : (191481 / 1000000000) ≤ -Real.log (2000000 / 2000383) ∧
    -Real.log (2000000 / 2000383) ≤ (95741 / 500000000) := by
  have h := checkLog_sound (w := (383 / 4000383)) (n := 12)
    (lo := (191481 / 1000000000)) (hi := (95741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000383 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000383 / 2000000) = 1/(2000000 / 2000383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5768 : Bounds (191481 / 1000000000) (95741 / 500000000) (Real.log (2000383 / 2000000)) := by
  have h := reflection_log_5768_neg
  have he : Real.log (2000383 / 2000000) = -Real.log (2000000 / 2000383) := by
    rw [show ((2000383 / 2000000) : ℝ) = ((2000000 / 2000383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5769_neg : (95759 / 500000000) ≤ -Real.log (1999617 / 2000000) ∧
    -Real.log (1999617 / 2000000) ≤ (191519 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 3999617)) (n := 12)
    (lo := (95759 / 500000000)) (hi := (191519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999617) = 1/(1999617 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5769 : Bounds (-191519 / 1000000000) (-95759 / 500000000) (Real.log (1999617 / 2000000)) := by
  have h := reflection_log_5769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5770_neg : (91889791 / 1000000000) ≤ -Real.log (250000 / 274061) ∧
    -Real.log (250000 / 274061) ≤ (717889 / 7812500) := by
  have h := checkLog_sound (w := (24061 / 524061)) (n := 12)
    (lo := (91889791 / 1000000000)) (hi := (717889 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274061 / 250000) = 1/(250000 / 274061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5770 : Bounds (91889791 / 1000000000) (717889 / 7812500) (Real.log (274061 / 250000)) := by
  have h := reflection_log_5770_neg
  have he : Real.log (274061 / 250000) = -Real.log (250000 / 274061) := by
    rw [show ((274061 / 250000) : ℝ) = ((250000 / 274061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5771_neg : (50597933 / 500000000) ≤ -Real.log (225939 / 250000) ∧
    -Real.log (225939 / 250000) ≤ (101195867 / 1000000000) := by
  have h := checkLog_sound (w := (24061 / 475939)) (n := 12)
    (lo := (50597933 / 500000000)) (hi := (101195867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225939) = 1/(225939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5771 : Bounds (-101195867 / 1000000000) (-50597933 / 500000000) (Real.log (225939 / 250000)) := by
  have h := reflection_log_5771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5772_neg : (2302763 / 25000000) ≤ -Real.log (500000 / 548243) ∧
    -Real.log (500000 / 548243) ≤ (92110521 / 1000000000) := by
  have h := checkLog_sound (w := (48243 / 1048243)) (n := 12)
    (lo := (2302763 / 25000000)) (hi := (92110521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548243 / 500000) = 1/(500000 / 548243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5772 : Bounds (2302763 / 25000000) (92110521 / 1000000000) (Real.log (548243 / 500000)) := by
  have h := reflection_log_5772_neg
  have he : Real.log (548243 / 500000) = -Real.log (500000 / 548243) := by
    rw [show ((548243 / 500000) : ℝ) = ((500000 / 548243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5773_neg : (101463673 / 1000000000) ≤ -Real.log (451757 / 500000) ∧
    -Real.log (451757 / 500000) ≤ (50731837 / 500000000) := by
  have h := checkLog_sound (w := (48243 / 951757)) (n := 12)
    (lo := (101463673 / 1000000000)) (hi := (50731837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451757) = 1/(451757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5773 : Bounds (-50731837 / 500000000) (-101463673 / 1000000000) (Real.log (451757 / 500000)) := by
  have h := reflection_log_5773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5774_neg : (146143 / 15625000) ≤ -Real.log (247672612951 / 250000000000) ∧
    -Real.log (247672612951 / 250000000000) ≤ (9353153 / 1000000000) := by
  have h := checkLog_sound (w := (2327387049 / 497672612951)) (n := 12)
    (lo := (146143 / 15625000)) (hi := (9353153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247672612951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247672612951) = 1/(247672612951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5774 : Bounds (-9353153 / 1000000000) (-146143 / 15625000) (Real.log (247672612951 / 250000000000)) := by
  have h := reflection_log_5774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5775_neg : (372243 / 40000000) ≤ -Real.log (61921068279 / 62500000000) ∧
    -Real.log (61921068279 / 62500000000) ≤ (2326519 / 250000000) := by
  have h := checkLog_sound (w := (578931721 / 124421068279)) (n := 12)
    (lo := (372243 / 40000000)) (hi := (2326519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61921068279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61921068279) = 1/(61921068279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5775 : Bounds (-2326519 / 250000000) (-372243 / 40000000) (Real.log (61921068279 / 62500000000)) := by
  have h := reflection_log_5775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5776_neg : (96542829 / 500000000) ≤ -Real.log (500000000000 / 606493345549) ∧
    -Real.log (500000000000 / 606493345549) ≤ (193085659 / 1000000000) := by
  have h := checkLog_sound (w := (106493345549 / 1106493345549)) (n := 12)
    (lo := (96542829 / 500000000)) (hi := (193085659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606493345549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606493345549 / 500000000000) = 1/(500000000000 / 606493345549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5776 : Bounds (96542829 / 500000000) (193085659 / 1000000000) (Real.log (606493345549 / 500000000000)) := by
  have h := reflection_log_5776_neg
  have he : Real.log (606493345549 / 500000000000) = -Real.log (500000000000 / 606493345549) := by
    rw [show ((606493345549 / 500000000000) : ℝ) = ((500000000000 / 606493345549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5777_neg : (96787097 / 500000000) ≤ -Real.log (500000000000 / 606789712169) ∧
    -Real.log (500000000000 / 606789712169) ≤ (38714839 / 200000000) := by
  have h := checkLog_sound (w := (106789712169 / 1106789712169)) (n := 12)
    (lo := (96787097 / 500000000)) (hi := (38714839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606789712169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606789712169 / 500000000000) = 1/(500000000000 / 606789712169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5777 : Bounds (96787097 / 500000000) (38714839 / 200000000) (Real.log (606789712169 / 500000000000)) := by
  have h := reflection_log_5777_neg
  have he : Real.log (606789712169 / 500000000000) = -Real.log (500000000000 / 606789712169) := by
    rw [show ((606789712169 / 500000000000) : ℝ) = ((500000000000 / 606789712169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5778_neg : (387580007 / 1000000000) ≤ -Real.log (500000000000 / 736705416769) ∧
    -Real.log (500000000000 / 736705416769) ≤ (48447501 / 125000000) := by
  have h := checkLog_sound (w := (236705416769 / 1236705416769)) (n := 12)
    (lo := (387580007 / 1000000000)) (hi := (48447501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736705416769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736705416769 / 500000000000) = 1/(500000000000 / 736705416769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5778 : Bounds (387580007 / 1000000000) (48447501 / 125000000) (Real.log (736705416769 / 500000000000)) := by
  have h := reflection_log_5778_neg
  have he : Real.log (736705416769 / 500000000000) = -Real.log (500000000000 / 736705416769) := by
    rw [show ((736705416769 / 500000000000) : ℝ) = ((500000000000 / 736705416769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5779_neg : (387787617 / 1000000000) ≤ -Real.log (125000000000 / 184214594929) ∧
    -Real.log (125000000000 / 184214594929) ≤ (193893809 / 500000000) := by
  have h := checkLog_sound (w := (59214594929 / 309214594929)) (n := 12)
    (lo := (387787617 / 1000000000)) (hi := (193893809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184214594929 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184214594929 / 125000000000) = 1/(125000000000 / 184214594929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5779 : Bounds (387787617 / 1000000000) (193893809 / 500000000) (Real.log (184214594929 / 125000000000)) := by
  have h := reflection_log_5779_neg
  have he : Real.log (184214594929 / 125000000000) = -Real.log (125000000000 / 184214594929) := by
    rw [show ((184214594929 / 125000000000) : ℝ) = ((125000000000 / 184214594929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5780_neg : (175296941 / 1000000000) ≤ -Real.log (2500 / 2979) ∧
    -Real.log (2500 / 2979) ≤ (87648471 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5479)) (n := 12)
    (lo := (175296941 / 1000000000)) (hi := (87648471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2979 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2979 / 2500) = 1/(2500 / 2979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5780 : Bounds (175296941 / 1000000000) (87648471 / 500000000) (Real.log (2979 / 2500)) := by
  have h := reflection_log_5780_neg
  have he : Real.log (2979 / 2500) = -Real.log (2500 / 2979) := by
    rw [show ((2979 / 2500) : ℝ) = ((2500 / 2979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5781_neg : (212698293 / 1000000000) ≤ -Real.log (2021 / 2500) ∧
    -Real.log (2021 / 2500) ≤ (106349147 / 500000000) := by
  have h := checkLog_sound (w := (479 / 4521)) (n := 12)
    (lo := (212698293 / 1000000000)) (hi := (106349147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2021) = 1/(2021 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5781 : Bounds (-106349147 / 500000000) (-212698293 / 1000000000) (Real.log (2021 / 2500)) := by
  have h := reflection_log_5781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5782_neg : (191581 / 1000000000) ≤ -Real.log (2500000 / 2500479) ∧
    -Real.log (2500000 / 2500479) ≤ (95791 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5000479)) (n := 12)
    (lo := (191581 / 1000000000)) (hi := (95791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500479 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500479 / 2500000) = 1/(2500000 / 2500479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5782 : Bounds (191581 / 1000000000) (95791 / 500000000) (Real.log (2500479 / 2500000)) := by
  have h := reflection_log_5782_neg
  have he : Real.log (2500479 / 2500000) = -Real.log (2500000 / 2500479) := by
    rw [show ((2500479 / 2500000) : ℝ) = ((2500000 / 2500479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5783_neg : (95809 / 500000000) ≤ -Real.log (2499521 / 2500000) ∧
    -Real.log (2499521 / 2500000) ≤ (191619 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 4999521)) (n := 12)
    (lo := (95809 / 500000000)) (hi := (191619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499521) = 1/(2499521 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5783 : Bounds (-191619 / 1000000000) (-95809 / 500000000) (Real.log (2499521 / 2500000)) := by
  have h := reflection_log_5783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5784_neg : (11492039 / 125000000) ≤ -Real.log (200000 / 219259) ∧
    -Real.log (200000 / 219259) ≤ (91936313 / 1000000000) := by
  have h := checkLog_sound (w := (19259 / 419259)) (n := 12)
    (lo := (11492039 / 125000000)) (hi := (91936313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219259 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219259 / 200000) = 1/(200000 / 219259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5784 : Bounds (11492039 / 125000000) (91936313 / 1000000000) (Real.log (219259 / 200000)) := by
  have h := reflection_log_5784_neg
  have he : Real.log (219259 / 200000) = -Real.log (200000 / 219259) := by
    rw [show ((219259 / 200000) : ℝ) = ((200000 / 219259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5785_neg : (101252299 / 1000000000) ≤ -Real.log (180741 / 200000) ∧
    -Real.log (180741 / 200000) ≤ (1012523 / 10000000) := by
  have h := checkLog_sound (w := (19259 / 380741)) (n := 12)
    (lo := (101252299 / 1000000000)) (hi := (1012523 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180741) = 1/(180741 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5785 : Bounds (-1012523 / 10000000) (-101252299 / 1000000000) (Real.log (180741 / 200000)) := by
  have h := reflection_log_5785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5786_neg : (11519629 / 125000000) ≤ -Real.log (1000000 / 1096537) ∧
    -Real.log (1000000 / 1096537) ≤ (92157033 / 1000000000) := by
  have h := checkLog_sound (w := (96537 / 2096537)) (n := 12)
    (lo := (11519629 / 125000000)) (hi := (92157033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096537 / 1000000) = 1/(1000000 / 1096537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5786 : Bounds (11519629 / 125000000) (92157033 / 1000000000) (Real.log (1096537 / 1000000)) := by
  have h := reflection_log_5786_neg
  have he : Real.log (1096537 / 1000000) = -Real.log (1000000 / 1096537) := by
    rw [show ((1096537 / 1000000) : ℝ) = ((1000000 / 1096537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5787_neg : (101520121 / 1000000000) ≤ -Real.log (903463 / 1000000) ∧
    -Real.log (903463 / 1000000) ≤ (50760061 / 500000000) := by
  have h := checkLog_sound (w := (96537 / 1903463)) (n := 12)
    (lo := (101520121 / 1000000000)) (hi := (50760061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903463) = 1/(903463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5787 : Bounds (-50760061 / 500000000) (-101520121 / 1000000000) (Real.log (903463 / 1000000)) := by
  have h := reflection_log_5787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5788_neg : (9363089 / 1000000000) ≤ -Real.log (990680607631 / 1000000000000) ∧
    -Real.log (990680607631 / 1000000000000) ≤ (936309 / 100000000) := by
  have h := checkLog_sound (w := (9319392369 / 1990680607631)) (n := 12)
    (lo := (9363089 / 1000000000)) (hi := (936309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990680607631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990680607631) = 1/(990680607631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5788 : Bounds (-936309 / 100000000) (-9363089 / 1000000000) (Real.log (990680607631 / 1000000000000)) := by
  have h := reflection_log_5788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5789_neg : (4657993 / 500000000) ≤ -Real.log (39629090919 / 40000000000) ∧
    -Real.log (39629090919 / 40000000000) ≤ (9315987 / 1000000000) := by
  have h := checkLog_sound (w := (370909081 / 79629090919)) (n := 12)
    (lo := (4657993 / 500000000)) (hi := (9315987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39629090919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39629090919) = 1/(39629090919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5789 : Bounds (-9315987 / 1000000000) (-4657993 / 500000000) (Real.log (39629090919 / 40000000000)) := by
  have h := reflection_log_5789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5790_neg : (48297153 / 250000000) ≤ -Real.log (31250000000 / 37909736861) ∧
    -Real.log (31250000000 / 37909736861) ≤ (193188613 / 1000000000) := by
  have h := checkLog_sound (w := (6659736861 / 69159736861)) (n := 12)
    (lo := (48297153 / 250000000)) (hi := (193188613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37909736861 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37909736861 / 31250000000) = 1/(31250000000 / 37909736861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5790 : Bounds (48297153 / 250000000) (193188613 / 1000000000) (Real.log (37909736861 / 31250000000)) := by
  have h := reflection_log_5790_neg
  have he : Real.log (37909736861 / 31250000000) = -Real.log (31250000000 / 37909736861) := by
    rw [show ((37909736861 / 31250000000) : ℝ) = ((31250000000 / 37909736861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5791_neg : (193677153 / 1000000000) ≤ -Real.log (125000000000 / 151713047463) ∧
    -Real.log (125000000000 / 151713047463) ≤ (96838577 / 500000000) := by
  have h := checkLog_sound (w := (26713047463 / 276713047463)) (n := 12)
    (lo := (193677153 / 1000000000)) (hi := (96838577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151713047463 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151713047463 / 125000000000) = 1/(125000000000 / 151713047463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5791 : Bounds (193677153 / 1000000000) (96838577 / 500000000) (Real.log (151713047463 / 125000000000)) := by
  have h := reflection_log_5791_neg
  have he : Real.log (151713047463 / 125000000000) = -Real.log (125000000000 / 151713047463) := by
    rw [show ((151713047463 / 125000000000) : ℝ) = ((125000000000 / 151713047463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5792_neg : (387787617 / 1000000000) ≤ -Real.log (100000000000 / 147371675943) ∧
    -Real.log (100000000000 / 147371675943) ≤ (193893809 / 500000000) := by
  have h := checkLog_sound (w := (47371675943 / 247371675943)) (n := 12)
    (lo := (387787617 / 1000000000)) (hi := (193893809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147371675943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147371675943 / 100000000000) = 1/(100000000000 / 147371675943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5792 : Bounds (387787617 / 1000000000) (193893809 / 500000000) (Real.log (147371675943 / 100000000000)) := by
  have h := reflection_log_5792_neg
  have he : Real.log (147371675943 / 100000000000) = -Real.log (100000000000 / 147371675943) := by
    rw [show ((147371675943 / 100000000000) : ℝ) = ((100000000000 / 147371675943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5793_neg : (77599047 / 200000000) ≤ -Real.log (100000000000 / 147402276101) ∧
    -Real.log (100000000000 / 147402276101) ≤ (96998809 / 250000000) := by
  have h := checkLog_sound (w := (47402276101 / 247402276101)) (n := 12)
    (lo := (77599047 / 200000000)) (hi := (96998809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147402276101 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147402276101 / 100000000000) = 1/(100000000000 / 147402276101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5793 : Bounds (77599047 / 200000000) (96998809 / 250000000) (Real.log (147402276101 / 100000000000)) := by
  have h := reflection_log_5793_neg
  have he : Real.log (147402276101 / 100000000000) = -Real.log (100000000000 / 147402276101) := by
    rw [show ((147402276101 / 100000000000) : ℝ) = ((100000000000 / 147402276101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5794_neg : (175380859 / 1000000000) ≤ -Real.log (10000 / 11917) ∧
    -Real.log (10000 / 11917) ≤ (8769043 / 50000000) := by
  have h := checkLog_sound (w := (1917 / 21917)) (n := 12)
    (lo := (175380859 / 1000000000)) (hi := (8769043 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 10000) = 1/(10000 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5794 : Bounds (175380859 / 1000000000) (8769043 / 50000000) (Real.log (11917 / 10000)) := by
  have h := reflection_log_5794_neg
  have he : Real.log (11917 / 10000) = -Real.log (10000 / 11917) := by
    rw [show ((11917 / 10000) : ℝ) = ((10000 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5795_neg : (106411001 / 500000000) ≤ -Real.log (8083 / 10000) ∧
    -Real.log (8083 / 10000) ≤ (212822003 / 1000000000) := by
  have h := checkLog_sound (w := (1917 / 18083)) (n := 12)
    (lo := (106411001 / 500000000)) (hi := (212822003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8083) = 1/(8083 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5795 : Bounds (-212822003 / 1000000000) (-106411001 / 500000000) (Real.log (8083 / 10000)) := by
  have h := reflection_log_5795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5796_neg : (191681 / 1000000000) ≤ -Real.log (10000000 / 10001917) ∧
    -Real.log (10000000 / 10001917) ≤ (95841 / 500000000) := by
  have h := checkLog_sound (w := (1917 / 20001917)) (n := 12)
    (lo := (191681 / 1000000000)) (hi := (95841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001917 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001917 / 10000000) = 1/(10000000 / 10001917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5796 : Bounds (191681 / 1000000000) (95841 / 500000000) (Real.log (10001917 / 10000000)) := by
  have h := reflection_log_5796_neg
  have he : Real.log (10001917 / 10000000) = -Real.log (10000000 / 10001917) := by
    rw [show ((10001917 / 10000000) : ℝ) = ((10000000 / 10001917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5797_neg : (95859 / 500000000) ≤ -Real.log (9998083 / 10000000) ∧
    -Real.log (9998083 / 10000000) ≤ (191719 / 1000000000) := by
  have h := checkLog_sound (w := (1917 / 19998083)) (n := 12)
    (lo := (95859 / 500000000)) (hi := (191719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998083) = 1/(9998083 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5797 : Bounds (-191719 / 1000000000) (-95859 / 500000000) (Real.log (9998083 / 10000000)) := by
  have h := reflection_log_5797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5798_neg : (574887 / 6250000) ≤ -Real.log (200000 / 219269) ∧
    -Real.log (200000 / 219269) ≤ (91981921 / 1000000000) := by
  have h := checkLog_sound (w := (19269 / 419269)) (n := 12)
    (lo := (574887 / 6250000)) (hi := (91981921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219269 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219269 / 200000) = 1/(200000 / 219269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5798 : Bounds (574887 / 6250000) (91981921 / 1000000000) (Real.log (219269 / 200000)) := by
  have h := reflection_log_5798_neg
  have he : Real.log (219269 / 200000) = -Real.log (200000 / 219269) := by
    rw [show ((219269 / 200000) : ℝ) = ((200000 / 219269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5799_neg : (25326907 / 250000000) ≤ -Real.log (180731 / 200000) ∧
    -Real.log (180731 / 200000) ≤ (101307629 / 1000000000) := by
  have h := checkLog_sound (w := (19269 / 380731)) (n := 12)
    (lo := (25326907 / 250000000)) (hi := (101307629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180731) = 1/(180731 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5799 : Bounds (-101307629 / 1000000000) (-25326907 / 250000000) (Real.log (180731 / 200000)) := by
  have h := reflection_log_5799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5800_neg : (92203541 / 1000000000) ≤ -Real.log (250000 / 274147) ∧
    -Real.log (250000 / 274147) ≤ (46101771 / 500000000) := by
  have h := checkLog_sound (w := (24147 / 524147)) (n := 12)
    (lo := (92203541 / 1000000000)) (hi := (46101771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274147 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274147 / 250000) = 1/(250000 / 274147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5800 : Bounds (92203541 / 1000000000) (46101771 / 500000000) (Real.log (274147 / 250000)) := by
  have h := reflection_log_5800_neg
  have he : Real.log (274147 / 250000) = -Real.log (250000 / 274147) := by
    rw [show ((274147 / 250000) : ℝ) = ((250000 / 274147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5801_neg : (25394143 / 250000000) ≤ -Real.log (225853 / 250000) ∧
    -Real.log (225853 / 250000) ≤ (101576573 / 1000000000) := by
  have h := checkLog_sound (w := (24147 / 475853)) (n := 12)
    (lo := (25394143 / 250000000)) (hi := (101576573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225853) = 1/(225853 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5801 : Bounds (-101576573 / 1000000000) (-25394143 / 250000000) (Real.log (225853 / 250000)) := by
  have h := reflection_log_5801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5802_neg : (9373031 / 1000000000) ≤ -Real.log (61916922391 / 62500000000) ∧
    -Real.log (61916922391 / 62500000000) ≤ (1171629 / 125000000) := by
  have h := checkLog_sound (w := (583077609 / 124416922391)) (n := 12)
    (lo := (9373031 / 1000000000)) (hi := (1171629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61916922391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61916922391) = 1/(61916922391 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5802 : Bounds (-1171629 / 125000000) (-9373031 / 1000000000) (Real.log (61916922391 / 62500000000)) := by
  have h := reflection_log_5802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5803_neg : (2331427 / 250000000) ≤ -Real.log (39628705639 / 40000000000) ∧
    -Real.log (39628705639 / 40000000000) ≤ (9325709 / 1000000000) := by
  have h := checkLog_sound (w := (371294361 / 79628705639)) (n := 12)
    (lo := (2331427 / 250000000)) (hi := (9325709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39628705639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39628705639) = 1/(39628705639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5803 : Bounds (-9325709 / 1000000000) (-2331427 / 250000000) (Real.log (39628705639 / 40000000000)) := by
  have h := reflection_log_5803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5804_neg : (48322387 / 250000000) ≤ -Real.log (500000000000 / 606617016449) ∧
    -Real.log (500000000000 / 606617016449) ≤ (193289549 / 1000000000) := by
  have h := checkLog_sound (w := (106617016449 / 1106617016449)) (n := 12)
    (lo := (48322387 / 250000000)) (hi := (193289549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606617016449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606617016449 / 500000000000) = 1/(500000000000 / 606617016449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5804 : Bounds (48322387 / 250000000) (193289549 / 1000000000) (Real.log (606617016449 / 500000000000)) := by
  have h := reflection_log_5804_neg
  have he : Real.log (606617016449 / 500000000000) = -Real.log (500000000000 / 606617016449) := by
    rw [show ((606617016449 / 500000000000) : ℝ) = ((500000000000 / 606617016449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5805_neg : (193780113 / 1000000000) ≤ -Real.log (50000000000 / 60691467459) ∧
    -Real.log (50000000000 / 60691467459) ≤ (96890057 / 500000000) := by
  have h := checkLog_sound (w := (10691467459 / 110691467459)) (n := 12)
    (lo := (193780113 / 1000000000)) (hi := (96890057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60691467459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60691467459 / 50000000000) = 1/(50000000000 / 60691467459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5805 : Bounds (193780113 / 1000000000) (96890057 / 500000000) (Real.log (60691467459 / 50000000000)) := by
  have h := reflection_log_5805_neg
  have he : Real.log (60691467459 / 50000000000) = -Real.log (50000000000 / 60691467459) := by
    rw [show ((60691467459 / 50000000000) : ℝ) = ((50000000000 / 60691467459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5806_neg : (77599047 / 200000000) ≤ -Real.log (62500000000 / 92126422563) ∧
    -Real.log (62500000000 / 92126422563) ≤ (96998809 / 250000000) := by
  have h := checkLog_sound (w := (29626422563 / 154626422563)) (n := 12)
    (lo := (77599047 / 200000000)) (hi := (96998809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92126422563 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92126422563 / 62500000000) = 1/(62500000000 / 92126422563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5806 : Bounds (77599047 / 200000000) (96998809 / 250000000) (Real.log (92126422563 / 62500000000)) := by
  have h := reflection_log_5806_neg
  have he : Real.log (92126422563 / 62500000000) = -Real.log (62500000000 / 92126422563) := by
    rw [show ((92126422563 / 62500000000) : ℝ) = ((62500000000 / 92126422563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5807_neg : (388202861 / 1000000000) ≤ -Real.log (31250000000 / 46072776197) ∧
    -Real.log (31250000000 / 46072776197) ≤ (194101431 / 500000000) := by
  have h := checkLog_sound (w := (14822776197 / 77322776197)) (n := 12)
    (lo := (388202861 / 1000000000)) (hi := (194101431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46072776197 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46072776197 / 31250000000) = 1/(31250000000 / 46072776197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5807 : Bounds (388202861 / 1000000000) (194101431 / 500000000) (Real.log (46072776197 / 31250000000)) := by
  have h := reflection_log_5807_neg
  have he : Real.log (46072776197 / 31250000000) = -Real.log (31250000000 / 46072776197) := by
    rw [show ((46072776197 / 31250000000) : ℝ) = ((31250000000 / 46072776197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5808_neg : (175464769 / 1000000000) ≤ -Real.log (5000 / 5959) ∧
    -Real.log (5000 / 5959) ≤ (17546477 / 100000000) := by
  have h := checkLog_sound (w := (959 / 10959)) (n := 12)
    (lo := (175464769 / 1000000000)) (hi := (17546477 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5959 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5959 / 5000) = 1/(5000 / 5959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5808 : Bounds (175464769 / 1000000000) (17546477 / 100000000) (Real.log (5959 / 5000)) := by
  have h := reflection_log_5808_neg
  have he : Real.log (5959 / 5000) = -Real.log (5000 / 5959) := by
    rw [show ((5959 / 5000) : ℝ) = ((5000 / 5959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5809_neg : (106472863 / 500000000) ≤ -Real.log (4041 / 5000) ∧
    -Real.log (4041 / 5000) ≤ (212945727 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 9041)) (n := 12)
    (lo := (106472863 / 500000000)) (hi := (212945727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4041) = 1/(4041 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5809 : Bounds (-212945727 / 1000000000) (-106472863 / 500000000) (Real.log (4041 / 5000)) := by
  have h := reflection_log_5809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5810_neg : (191781 / 1000000000) ≤ -Real.log (5000000 / 5000959) ∧
    -Real.log (5000000 / 5000959) ≤ (95891 / 500000000) := by
  have h := checkLog_sound (w := (959 / 10000959)) (n := 12)
    (lo := (191781 / 1000000000)) (hi := (95891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000959 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000959 / 5000000) = 1/(5000000 / 5000959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5810 : Bounds (191781 / 1000000000) (95891 / 500000000) (Real.log (5000959 / 5000000)) := by
  have h := reflection_log_5810_neg
  have he : Real.log (5000959 / 5000000) = -Real.log (5000000 / 5000959) := by
    rw [show ((5000959 / 5000000) : ℝ) = ((5000000 / 5000959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5811_neg : (95909 / 500000000) ≤ -Real.log (4999041 / 5000000) ∧
    -Real.log (4999041 / 5000000) ≤ (191819 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 9999041)) (n := 12)
    (lo := (95909 / 500000000)) (hi := (191819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999041) = 1/(4999041 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5811 : Bounds (-191819 / 1000000000) (-95909 / 500000000) (Real.log (4999041 / 5000000)) := by
  have h := reflection_log_5811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5812_neg : (92028437 / 1000000000) ≤ -Real.log (250000 / 274099) ∧
    -Real.log (250000 / 274099) ≤ (46014219 / 500000000) := by
  have h := checkLog_sound (w := (24099 / 524099)) (n := 12)
    (lo := (92028437 / 1000000000)) (hi := (46014219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274099 / 250000) = 1/(250000 / 274099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5812 : Bounds (92028437 / 1000000000) (46014219 / 500000000) (Real.log (274099 / 250000)) := by
  have h := reflection_log_5812_neg
  have he : Real.log (274099 / 250000) = -Real.log (250000 / 274099) := by
    rw [show ((274099 / 250000) : ℝ) = ((250000 / 274099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5813_neg : (101364067 / 1000000000) ≤ -Real.log (225901 / 250000) ∧
    -Real.log (225901 / 250000) ≤ (25341017 / 250000000) := by
  have h := checkLog_sound (w := (24099 / 475901)) (n := 12)
    (lo := (101364067 / 1000000000)) (hi := (25341017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225901) = 1/(225901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5813 : Bounds (-25341017 / 250000000) (-101364067 / 1000000000) (Real.log (225901 / 250000)) := by
  have h := reflection_log_5813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5814_neg : (92250047 / 1000000000) ≤ -Real.log (1000000 / 1096639) ∧
    -Real.log (1000000 / 1096639) ≤ (1441407 / 15625000) := by
  have h := checkLog_sound (w := (96639 / 2096639)) (n := 12)
    (lo := (92250047 / 1000000000)) (hi := (1441407 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096639 / 1000000) = 1/(1000000 / 1096639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5814 : Bounds (92250047 / 1000000000) (1441407 / 15625000) (Real.log (1096639 / 1000000)) := by
  have h := reflection_log_5814_neg
  have he : Real.log (1096639 / 1000000) = -Real.log (1000000 / 1096639) := by
    rw [show ((1096639 / 1000000) : ℝ) = ((1000000 / 1096639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5815_neg : (50816513 / 500000000) ≤ -Real.log (903361 / 1000000) ∧
    -Real.log (903361 / 1000000) ≤ (101633027 / 1000000000) := by
  have h := checkLog_sound (w := (96639 / 1903361)) (n := 12)
    (lo := (50816513 / 500000000)) (hi := (101633027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903361) = 1/(903361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5815 : Bounds (-101633027 / 1000000000) (-50816513 / 500000000) (Real.log (903361 / 1000000)) := by
  have h := reflection_log_5815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5816_neg : (9382979 / 1000000000) ≤ -Real.log (990660903679 / 1000000000000) ∧
    -Real.log (990660903679 / 1000000000000) ≤ (469149 / 50000000) := by
  have h := checkLog_sound (w := (9339096321 / 1990660903679)) (n := 12)
    (lo := (9382979 / 1000000000)) (hi := (469149 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990660903679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990660903679) = 1/(990660903679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5816 : Bounds (-469149 / 50000000) (-9382979 / 1000000000) (Real.log (990660903679 / 1000000000000)) := by
  have h := reflection_log_5816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5817_neg : (933563 / 100000000) ≤ -Real.log (61919238199 / 62500000000) ∧
    -Real.log (61919238199 / 62500000000) ≤ (9335631 / 1000000000) := by
  have h := checkLog_sound (w := (580761801 / 124419238199)) (n := 12)
    (lo := (933563 / 100000000)) (hi := (9335631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61919238199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61919238199) = 1/(61919238199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5817 : Bounds (-9335631 / 1000000000) (-933563 / 100000000) (Real.log (61919238199 / 62500000000)) := by
  have h := reflection_log_5817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5818_neg : (24174063 / 125000000) ≤ -Real.log (500000000000 / 606679474637) ∧
    -Real.log (500000000000 / 606679474637) ≤ (38678501 / 200000000) := by
  have h := checkLog_sound (w := (106679474637 / 1106679474637)) (n := 12)
    (lo := (24174063 / 125000000)) (hi := (38678501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606679474637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606679474637 / 500000000000) = 1/(500000000000 / 606679474637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5818 : Bounds (24174063 / 125000000) (38678501 / 200000000) (Real.log (606679474637 / 500000000000)) := by
  have h := reflection_log_5818_neg
  have he : Real.log (606679474637 / 500000000000) = -Real.log (500000000000 / 606679474637) := by
    rw [show ((606679474637 / 500000000000) : ℝ) = ((500000000000 / 606679474637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5819_neg : (96941537 / 500000000) ≤ -Real.log (250000000000 / 303488583191) ∧
    -Real.log (250000000000 / 303488583191) ≤ (7755323 / 40000000) := by
  have h := checkLog_sound (w := (53488583191 / 553488583191)) (n := 12)
    (lo := (96941537 / 500000000)) (hi := (7755323 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303488583191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303488583191 / 250000000000) = 1/(250000000000 / 303488583191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5819 : Bounds (96941537 / 500000000) (7755323 / 40000000) (Real.log (303488583191 / 250000000000)) := by
  have h := reflection_log_5819_neg
  have he : Real.log (303488583191 / 250000000000) = -Real.log (250000000000 / 303488583191) := by
    rw [show ((303488583191 / 250000000000) : ℝ) = ((250000000000 / 303488583191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5820_neg : (388202861 / 1000000000) ≤ -Real.log (500000000000 / 737164419151) ∧
    -Real.log (500000000000 / 737164419151) ≤ (194101431 / 500000000) := by
  have h := checkLog_sound (w := (237164419151 / 1237164419151)) (n := 12)
    (lo := (388202861 / 1000000000)) (hi := (194101431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737164419151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737164419151 / 500000000000) = 1/(500000000000 / 737164419151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5820 : Bounds (388202861 / 1000000000) (194101431 / 500000000) (Real.log (737164419151 / 500000000000)) := by
  have h := reflection_log_5820_neg
  have he : Real.log (737164419151 / 500000000000) = -Real.log (500000000000 / 737164419151) := by
    rw [show ((737164419151 / 500000000000) : ℝ) = ((500000000000 / 737164419151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5821_neg : (77682099 / 200000000) ≤ -Real.log (50000000000 / 73731749567) ∧
    -Real.log (50000000000 / 73731749567) ≤ (3034457 / 7812500) := by
  have h := checkLog_sound (w := (23731749567 / 123731749567)) (n := 12)
    (lo := (77682099 / 200000000)) (hi := (3034457 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73731749567 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73731749567 / 50000000000) = 1/(50000000000 / 73731749567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5821 : Bounds (77682099 / 200000000) (3034457 / 7812500) (Real.log (73731749567 / 50000000000)) := by
  have h := reflection_log_5821_neg
  have he : Real.log (73731749567 / 50000000000) = -Real.log (50000000000 / 73731749567) := by
    rw [show ((73731749567 / 50000000000) : ℝ) = ((50000000000 / 73731749567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5822_neg : (685737 / 3906250) ≤ -Real.log (10000 / 11919) ∧
    -Real.log (10000 / 11919) ≤ (175548673 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 21919)) (n := 12)
    (lo := (685737 / 3906250)) (hi := (175548673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11919 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11919 / 10000) = 1/(10000 / 11919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5822 : Bounds (685737 / 3906250) (175548673 / 1000000000) (Real.log (11919 / 10000)) := by
  have h := reflection_log_5822_neg
  have he : Real.log (11919 / 10000) = -Real.log (10000 / 11919) := by
    rw [show ((11919 / 10000) : ℝ) = ((10000 / 11919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5823_neg : (42613893 / 200000000) ≤ -Real.log (8081 / 10000) ∧
    -Real.log (8081 / 10000) ≤ (106534733 / 500000000) := by
  have h := checkLog_sound (w := (1919 / 18081)) (n := 12)
    (lo := (42613893 / 200000000)) (hi := (106534733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8081) = 1/(8081 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5823 : Bounds (-106534733 / 500000000) (-42613893 / 200000000) (Real.log (8081 / 10000)) := by
  have h := reflection_log_5823_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
