import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10816_neg : (77881451 / 200000000) ≤ -Real.log (50000000000 / 73805279057) ∧
    -Real.log (50000000000 / 73805279057) ≤ (48675907 / 125000000) := by
  have h := checkLog_sound (w := (23805279057 / 123805279057)) (n := 12)
    (lo := (77881451 / 200000000)) (hi := (48675907 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73805279057 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73805279057 / 50000000000) = 1/(50000000000 / 73805279057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10816 : Bounds (77881451 / 200000000) (48675907 / 125000000) (Real.log (73805279057 / 50000000000)) := by
  have h := reflection_log_10816_neg
  have he : Real.log (73805279057 / 50000000000) = -Real.log (50000000000 / 73805279057) := by
    rw [show ((73805279057 / 50000000000) : ℝ) = ((50000000000 / 73805279057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10817_neg : (195645619 / 500000000) ≤ -Real.log (100000000000 / 147888916019) ∧
    -Real.log (100000000000 / 147888916019) ≤ (391291239 / 1000000000) := by
  have h := checkLog_sound (w := (47888916019 / 247888916019)) (n := 12)
    (lo := (195645619 / 500000000)) (hi := (391291239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147888916019 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147888916019 / 100000000000) = 1/(100000000000 / 147888916019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10817 : Bounds (195645619 / 500000000) (391291239 / 1000000000) (Real.log (147888916019 / 100000000000)) := by
  have h := reflection_log_10817_neg
  have he : Real.log (147888916019 / 100000000000) = -Real.log (100000000000 / 147888916019) := by
    rw [show ((147888916019 / 100000000000) : ℝ) = ((100000000000 / 147888916019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10818_neg : (790785649 / 1000000000) ≤ -Real.log (100000000000 / 220512820513) ∧
    -Real.log (100000000000 / 220512820513) ≤ (790785651 / 1000000000) := by
  have h := checkLog_sound (w := (20512820513 / 420512820513)) (n := 12)
    (lo := (97638469 / 1000000000)) (hi := (9763847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220512820513 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(220512820513 / 200000000000) = 1/(100000000000 / 220512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10818 : Bounds (790785649 / 1000000000) (790785651 / 1000000000) (Real.log (220512820513 / 100000000000)) := by
  have h := reflection_log_10818_neg
  have he : Real.log (220512820513 / 100000000000) = -Real.log (100000000000 / 220512820513) := by
    rw [show ((220512820513 / 100000000000) : ℝ) = ((100000000000 / 220512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10819_neg : (319907219 / 1000000000) ≤ -Real.log (1000 / 1377) ∧
    -Real.log (1000 / 1377) ≤ (15995361 / 50000000) := by
  have h := checkLog_sound (w := (377 / 2377)) (n := 12)
    (lo := (319907219 / 1000000000)) (hi := (15995361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377 / 1000) = 1/(1000 / 1377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10819 : Bounds (319907219 / 1000000000) (15995361 / 50000000) (Real.log (1377 / 1000)) := by
  have h := reflection_log_10819_neg
  have he : Real.log (1377 / 1000) = -Real.log (1000 / 1377) := by
    rw [show ((1377 / 1000) : ℝ) = ((1000 / 1377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10820_neg : (11830219 / 25000000) ≤ -Real.log (623 / 1000) ∧
    -Real.log (623 / 1000) ≤ (473208761 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 1623)) (n := 12)
    (lo := (11830219 / 25000000)) (hi := (473208761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 623) = 1/(623 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10820 : Bounds (-473208761 / 1000000000) (-11830219 / 25000000) (Real.log (623 / 1000)) := by
  have h := reflection_log_10820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10821_neg : (11779 / 31250000) ≤ -Real.log (1000000 / 1000377) ∧
    -Real.log (1000000 / 1000377) ≤ (376929 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2000377)) (n := 12)
    (lo := (11779 / 31250000)) (hi := (376929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000377 / 1000000) = 1/(1000000 / 1000377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10821 : Bounds (11779 / 31250000) (376929 / 1000000000) (Real.log (1000377 / 1000000)) := by
  have h := reflection_log_10821_neg
  have he : Real.log (1000377 / 1000000) = -Real.log (1000000 / 1000377) := by
    rw [show ((1000377 / 1000000) : ℝ) = ((1000000 / 1000377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10822_neg : (377071 / 1000000000) ≤ -Real.log (999623 / 1000000) ∧
    -Real.log (999623 / 1000000) ≤ (23567 / 62500000) := by
  have h := checkLog_sound (w := (377 / 1999623)) (n := 12)
    (lo := (377071 / 1000000000)) (hi := (23567 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999623) = 1/(999623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10822 : Bounds (-23567 / 62500000) (-377071 / 1000000000) (Real.log (999623 / 1000000)) := by
  have h := reflection_log_10822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10823_neg : (176321089 / 1000000000) ≤ -Real.log (1000000 / 1192821) ∧
    -Real.log (1000000 / 1192821) ≤ (17632109 / 100000000) := by
  have h := checkLog_sound (w := (192821 / 2192821)) (n := 12)
    (lo := (176321089 / 1000000000)) (hi := (17632109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192821 / 1000000) = 1/(1000000 / 1192821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10823 : Bounds (176321089 / 1000000000) (17632109 / 100000000) (Real.log (1192821 / 1000000)) := by
  have h := reflection_log_10823_neg
  have he : Real.log (1192821 / 1000000) = -Real.log (1000000 / 1192821) := by
    rw [show ((1192821 / 1000000) : ℝ) = ((1000000 / 1192821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10824_neg : (107104913 / 500000000) ≤ -Real.log (807179 / 1000000) ∧
    -Real.log (807179 / 1000000) ≤ (214209827 / 1000000000) := by
  have h := checkLog_sound (w := (192821 / 1807179)) (n := 12)
    (lo := (107104913 / 500000000)) (hi := (214209827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807179) = 1/(807179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10824 : Bounds (-214209827 / 1000000000) (-107104913 / 500000000) (Real.log (807179 / 1000000)) := by
  have h := reflection_log_10824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10825_neg : (177082021 / 1000000000) ≤ -Real.log (1000000 / 1193729) ∧
    -Real.log (1000000 / 1193729) ≤ (88541011 / 500000000) := by
  have h := checkLog_sound (w := (193729 / 2193729)) (n := 12)
    (lo := (177082021 / 1000000000)) (hi := (88541011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193729 / 1000000) = 1/(1000000 / 1193729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10825 : Bounds (177082021 / 1000000000) (88541011 / 500000000) (Real.log (1193729 / 1000000)) := by
  have h := reflection_log_10825_neg
  have he : Real.log (1193729 / 1000000) = -Real.log (1000000 / 1193729) := by
    rw [show ((1193729 / 1000000) : ℝ) = ((1000000 / 1193729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10826_neg : (53833841 / 250000000) ≤ -Real.log (806271 / 1000000) ∧
    -Real.log (806271 / 1000000) ≤ (43067073 / 200000000) := by
  have h := checkLog_sound (w := (193729 / 1806271)) (n := 12)
    (lo := (53833841 / 250000000)) (hi := (43067073 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806271) = 1/(806271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10826 : Bounds (-43067073 / 200000000) (-53833841 / 250000000) (Real.log (806271 / 1000000)) := by
  have h := reflection_log_10826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10827_neg : (38253343 / 1000000000) ≤ -Real.log (962469074559 / 1000000000000) ∧
    -Real.log (962469074559 / 1000000000000) ≤ (1195417 / 31250000) := by
  have h := checkLog_sound (w := (37530925441 / 1962469074559)) (n := 12)
    (lo := (38253343 / 1000000000)) (hi := (1195417 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962469074559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962469074559) = 1/(962469074559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10827 : Bounds (-1195417 / 31250000) (-38253343 / 1000000000) (Real.log (962469074559 / 1000000000000)) := by
  have h := reflection_log_10827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10828_neg : (1184023 / 31250000) ≤ -Real.log (962820061959 / 1000000000000) ∧
    -Real.log (962820061959 / 1000000000000) ≤ (37888737 / 1000000000) := by
  have h := checkLog_sound (w := (37179938041 / 1962820061959)) (n := 12)
    (lo := (1184023 / 31250000)) (hi := (37888737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962820061959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962820061959) = 1/(962820061959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10828 : Bounds (-37888737 / 1000000000) (-1184023 / 31250000) (Real.log (962820061959 / 1000000000000)) := by
  have h := reflection_log_10828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10829_neg : (97632729 / 250000000) ≤ -Real.log (50000000000 / 73888257747) ∧
    -Real.log (50000000000 / 73888257747) ≤ (390530917 / 1000000000) := by
  have h := checkLog_sound (w := (23888257747 / 123888257747)) (n := 12)
    (lo := (97632729 / 250000000)) (hi := (390530917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73888257747 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73888257747 / 50000000000) = 1/(50000000000 / 73888257747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10829 : Bounds (97632729 / 250000000) (390530917 / 1000000000) (Real.log (73888257747 / 50000000000)) := by
  have h := reflection_log_10829_neg
  have he : Real.log (73888257747 / 50000000000) = -Real.log (50000000000 / 73888257747) := by
    rw [show ((73888257747 / 50000000000) : ℝ) = ((50000000000 / 73888257747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10830_neg : (78483477 / 200000000) ≤ -Real.log (50000000000 / 74027777261) ∧
    -Real.log (50000000000 / 74027777261) ≤ (196208693 / 500000000) := by
  have h := checkLog_sound (w := (24027777261 / 124027777261)) (n := 12)
    (lo := (78483477 / 200000000)) (hi := (196208693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74027777261 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74027777261 / 50000000000) = 1/(50000000000 / 74027777261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10830 : Bounds (78483477 / 200000000) (196208693 / 500000000) (Real.log (74027777261 / 50000000000)) := by
  have h := reflection_log_10830_neg
  have he : Real.log (74027777261 / 50000000000) = -Real.log (50000000000 / 74027777261) := by
    rw [show ((74027777261 / 50000000000) : ℝ) = ((50000000000 / 74027777261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10831_neg : (790785649 / 1000000000) ≤ -Real.log (125000000000 / 275641025641) ∧
    -Real.log (125000000000 / 275641025641) ≤ (790785651 / 1000000000) := by
  have h := checkLog_sound (w := (25641025641 / 525641025641)) (n := 12)
    (lo := (97638469 / 1000000000)) (hi := (9763847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275641025641 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275641025641 / 250000000000) = 1/(125000000000 / 275641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10831 : Bounds (790785649 / 1000000000) (790785651 / 1000000000) (Real.log (275641025641 / 125000000000)) := by
  have h := reflection_log_10831_neg
  have he : Real.log (275641025641 / 125000000000) = -Real.log (125000000000 / 275641025641) := by
    rw [show ((275641025641 / 125000000000) : ℝ) = ((125000000000 / 275641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10832_neg : (793115979 / 1000000000) ≤ -Real.log (250000000000 / 552568218299) ∧
    -Real.log (250000000000 / 552568218299) ≤ (793115981 / 1000000000) := by
  have h := checkLog_sound (w := (52568218299 / 1052568218299)) (n := 12)
    (lo := (99968799 / 1000000000)) (hi := (124961 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552568218299 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(552568218299 / 500000000000) = 1/(250000000000 / 552568218299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10832 : Bounds (793115979 / 1000000000) (793115981 / 1000000000) (Real.log (552568218299 / 250000000000)) := by
  have h := reflection_log_10832_neg
  have he : Real.log (552568218299 / 250000000000) = -Real.log (250000000000 / 552568218299) := by
    rw [show ((552568218299 / 250000000000) : ℝ) = ((250000000000 / 552568218299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10833_neg : (80158293 / 250000000) ≤ -Real.log (500 / 689) ∧
    -Real.log (500 / 689) ≤ (320633173 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 1189)) (n := 12)
    (lo := (80158293 / 250000000)) (hi := (320633173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 500) = 1/(500 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10833 : Bounds (80158293 / 250000000) (320633173 / 1000000000) (Real.log (689 / 500)) := by
  have h := reflection_log_10833_neg
  have he : Real.log (689 / 500) = -Real.log (500 / 689) := by
    rw [show ((689 / 500) : ℝ) = ((500 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10834_neg : (237407593 / 500000000) ≤ -Real.log (311 / 500) ∧
    -Real.log (311 / 500) ≤ (474815187 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 811)) (n := 12)
    (lo := (237407593 / 500000000)) (hi := (474815187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 311) = 1/(311 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10834 : Bounds (-474815187 / 1000000000) (-237407593 / 500000000) (Real.log (311 / 500)) := by
  have h := reflection_log_10834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10835_neg : (47241 / 125000000) ≤ -Real.log (500000 / 500189) ∧
    -Real.log (500000 / 500189) ≤ (377929 / 1000000000) := by
  have h := checkLog_sound (w := (189 / 1000189)) (n := 12)
    (lo := (47241 / 125000000)) (hi := (377929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500189 / 500000) = 1/(500000 / 500189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10835 : Bounds (47241 / 125000000) (377929 / 1000000000) (Real.log (500189 / 500000)) := by
  have h := reflection_log_10835_neg
  have he : Real.log (500189 / 500000) = -Real.log (500000 / 500189) := by
    rw [show ((500189 / 500000) : ℝ) = ((500000 / 500189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10836_neg : (378071 / 1000000000) ≤ -Real.log (499811 / 500000) ∧
    -Real.log (499811 / 500000) ≤ (47259 / 125000000) := by
  have h := checkLog_sound (w := (189 / 999811)) (n := 12)
    (lo := (378071 / 1000000000)) (hi := (47259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499811) = 1/(499811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10836 : Bounds (-47259 / 125000000) (-378071 / 1000000000) (Real.log (499811 / 500000)) := by
  have h := reflection_log_10836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10837_neg : (35354739 / 200000000) ≤ -Real.log (1000000 / 1193361) ∧
    -Real.log (1000000 / 1193361) ≤ (2762089 / 15625000) := by
  have h := checkLog_sound (w := (193361 / 2193361)) (n := 12)
    (lo := (35354739 / 200000000)) (hi := (2762089 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193361 / 1000000) = 1/(1000000 / 1193361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10837 : Bounds (35354739 / 200000000) (2762089 / 15625000) (Real.log (1193361 / 1000000)) := by
  have h := reflection_log_10837_neg
  have he : Real.log (1193361 / 1000000) = -Real.log (1000000 / 1193361) := by
    rw [show ((1193361 / 1000000) : ℝ) = ((1000000 / 1193361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10838_neg : (107439523 / 500000000) ≤ -Real.log (806639 / 1000000) ∧
    -Real.log (806639 / 1000000) ≤ (214879047 / 1000000000) := by
  have h := checkLog_sound (w := (193361 / 1806639)) (n := 12)
    (lo := (107439523 / 500000000)) (hi := (214879047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806639) = 1/(806639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10838 : Bounds (-214879047 / 1000000000) (-107439523 / 500000000) (Real.log (806639 / 1000000)) := by
  have h := reflection_log_10838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10839_neg : (177535957 / 1000000000) ≤ -Real.log (1000000 / 1194271) ∧
    -Real.log (1000000 / 1194271) ≤ (88767979 / 500000000) := by
  have h := checkLog_sound (w := (194271 / 2194271)) (n := 12)
    (lo := (177535957 / 1000000000)) (hi := (88767979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194271 / 1000000) = 1/(1000000 / 1194271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10839 : Bounds (177535957 / 1000000000) (88767979 / 500000000) (Real.log (1194271 / 1000000)) := by
  have h := reflection_log_10839_neg
  have he : Real.log (1194271 / 1000000) = -Real.log (1000000 / 1194271) := by
    rw [show ((1194271 / 1000000) : ℝ) = ((1000000 / 1194271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10840_neg : (216007821 / 1000000000) ≤ -Real.log (805729 / 1000000) ∧
    -Real.log (805729 / 1000000) ≤ (108003911 / 500000000) := by
  have h := checkLog_sound (w := (194271 / 1805729)) (n := 12)
    (lo := (216007821 / 1000000000)) (hi := (108003911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805729) = 1/(805729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10840 : Bounds (-108003911 / 500000000) (-216007821 / 1000000000) (Real.log (805729 / 1000000)) := by
  have h := reflection_log_10840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10841_neg : (38471863 / 1000000000) ≤ -Real.log (962258778559 / 1000000000000) ∧
    -Real.log (962258778559 / 1000000000000) ≤ (4808983 / 125000000) := by
  have h := checkLog_sound (w := (37741221441 / 1962258778559)) (n := 12)
    (lo := (38471863 / 1000000000)) (hi := (4808983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962258778559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962258778559) = 1/(962258778559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10841 : Bounds (-4808983 / 125000000) (-38471863 / 1000000000) (Real.log (962258778559 / 1000000000000)) := by
  have h := reflection_log_10841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10842_neg : (762107 / 20000000) ≤ -Real.log (962611523679 / 1000000000000) ∧
    -Real.log (962611523679 / 1000000000000) ≤ (38105351 / 1000000000) := by
  have h := checkLog_sound (w := (37388476321 / 1962611523679)) (n := 12)
    (lo := (762107 / 20000000)) (hi := (38105351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962611523679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962611523679) = 1/(962611523679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10842 : Bounds (-38105351 / 1000000000) (-762107 / 20000000) (Real.log (962611523679 / 1000000000000)) := by
  have h := reflection_log_10842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10843_neg : (195826371 / 500000000) ≤ -Real.log (500000000000 / 739711940533) ∧
    -Real.log (500000000000 / 739711940533) ≤ (391652743 / 1000000000) := by
  have h := checkLog_sound (w := (239711940533 / 1239711940533)) (n := 12)
    (lo := (195826371 / 500000000)) (hi := (391652743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739711940533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739711940533 / 500000000000) = 1/(500000000000 / 739711940533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10843 : Bounds (195826371 / 500000000) (391652743 / 1000000000) (Real.log (739711940533 / 500000000000)) := by
  have h := reflection_log_10843_neg
  have he : Real.log (739711940533 / 500000000000) = -Real.log (500000000000 / 739711940533) := by
    rw [show ((739711940533 / 500000000000) : ℝ) = ((500000000000 / 739711940533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10844_neg : (196771889 / 500000000) ≤ -Real.log (250000000000 / 370556043037) ∧
    -Real.log (250000000000 / 370556043037) ≤ (393543779 / 1000000000) := by
  have h := checkLog_sound (w := (120556043037 / 620556043037)) (n := 12)
    (lo := (196771889 / 500000000)) (hi := (393543779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370556043037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370556043037 / 250000000000) = 1/(250000000000 / 370556043037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10844 : Bounds (196771889 / 500000000) (393543779 / 1000000000) (Real.log (370556043037 / 250000000000)) := by
  have h := reflection_log_10844_neg
  have he : Real.log (370556043037 / 250000000000) = -Real.log (250000000000 / 370556043037) := by
    rw [show ((370556043037 / 250000000000) : ℝ) = ((250000000000 / 370556043037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10845_neg : (793115979 / 1000000000) ≤ -Real.log (500000000000 / 1105136436597) ∧
    -Real.log (500000000000 / 1105136436597) ≤ (793115981 / 1000000000) := by
  have h := checkLog_sound (w := (105136436597 / 2105136436597)) (n := 12)
    (lo := (99968799 / 1000000000)) (hi := (124961 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105136436597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1105136436597 / 1000000000000) = 1/(500000000000 / 1105136436597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10845 : Bounds (793115979 / 1000000000) (793115981 / 1000000000) (Real.log (1105136436597 / 500000000000)) := by
  have h := reflection_log_10845_neg
  have he : Real.log (1105136436597 / 500000000000) = -Real.log (500000000000 / 1105136436597) := by
    rw [show ((1105136436597 / 500000000000) : ℝ) = ((500000000000 / 1105136436597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10846_neg : (397724179 / 500000000) ≤ -Real.log (500000000000 / 1107717041801) ∧
    -Real.log (500000000000 / 1107717041801) ≤ (19886209 / 25000000) := by
  have h := checkLog_sound (w := (107717041801 / 2107717041801)) (n := 12)
    (lo := (51150589 / 500000000)) (hi := (102301179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107717041801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1107717041801 / 1000000000000) = 1/(500000000000 / 1107717041801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10846 : Bounds (397724179 / 500000000) (19886209 / 25000000) (Real.log (1107717041801 / 500000000000)) := by
  have h := reflection_log_10846_neg
  have he : Real.log (1107717041801 / 500000000000) = -Real.log (500000000000 / 1107717041801) := by
    rw [show ((1107717041801 / 500000000000) : ℝ) = ((500000000000 / 1107717041801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10847_neg : (160679299 / 500000000) ≤ -Real.log (1000 / 1379) ∧
    -Real.log (1000 / 1379) ≤ (321358599 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 2379)) (n := 12)
    (lo := (160679299 / 500000000)) (hi := (321358599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1000) = 1/(1000 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10847 : Bounds (160679299 / 500000000) (321358599 / 1000000000) (Real.log (1379 / 1000)) := by
  have h := reflection_log_10847_neg
  have he : Real.log (1379 / 1000) = -Real.log (1000 / 1379) := by
    rw [show ((1379 / 1000) : ℝ) = ((1000 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10848_neg : (476424197 / 1000000000) ≤ -Real.log (621 / 1000) ∧
    -Real.log (621 / 1000) ≤ (238212099 / 500000000) := by
  have h := checkLog_sound (w := (379 / 1621)) (n := 12)
    (lo := (476424197 / 1000000000)) (hi := (238212099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 621) = 1/(621 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10848 : Bounds (-238212099 / 500000000) (-476424197 / 1000000000) (Real.log (621 / 1000)) := by
  have h := reflection_log_10848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10849_neg : (23683 / 62500000) ≤ -Real.log (1000000 / 1000379) ∧
    -Real.log (1000000 / 1000379) ≤ (378929 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 2000379)) (n := 12)
    (lo := (23683 / 62500000)) (hi := (378929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000379 / 1000000) = 1/(1000000 / 1000379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10849 : Bounds (23683 / 62500000) (378929 / 1000000000) (Real.log (1000379 / 1000000)) := by
  have h := reflection_log_10849_neg
  have he : Real.log (1000379 / 1000000) = -Real.log (1000000 / 1000379) := by
    rw [show ((1000379 / 1000000) : ℝ) = ((1000000 / 1000379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10850_neg : (379071 / 1000000000) ≤ -Real.log (999621 / 1000000) ∧
    -Real.log (999621 / 1000000) ≤ (5923 / 15625000) := by
  have h := checkLog_sound (w := (379 / 1999621)) (n := 12)
    (lo := (379071 / 1000000000)) (hi := (5923 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999621) = 1/(999621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10850 : Bounds (-5923 / 15625000) (-379071 / 1000000000) (Real.log (999621 / 1000000)) := by
  have h := reflection_log_10850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10851_neg : (88613467 / 500000000) ≤ -Real.log (500000 / 596951) ∧
    -Real.log (500000 / 596951) ≤ (35445387 / 200000000) := by
  have h := checkLog_sound (w := (96951 / 1096951)) (n := 12)
    (lo := (88613467 / 500000000)) (hi := (35445387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596951 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596951 / 500000) = 1/(500000 / 596951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10851 : Bounds (88613467 / 500000000) (35445387 / 200000000) (Real.log (596951 / 500000)) := by
  have h := reflection_log_10851_neg
  have he : Real.log (596951 / 500000) = -Real.log (500000 / 596951) := by
    rw [show ((596951 / 500000) : ℝ) = ((500000 / 596951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10852_neg : (43109991 / 200000000) ≤ -Real.log (403049 / 500000) ∧
    -Real.log (403049 / 500000) ≤ (53887489 / 250000000) := by
  have h := checkLog_sound (w := (96951 / 903049)) (n := 12)
    (lo := (43109991 / 200000000)) (hi := (53887489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403049) = 1/(403049 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10852 : Bounds (-53887489 / 250000000) (-43109991 / 200000000) (Real.log (403049 / 500000)) := by
  have h := reflection_log_10852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10853_neg : (177989687 / 1000000000) ≤ -Real.log (1000000 / 1194813) ∧
    -Real.log (1000000 / 1194813) ≤ (22248711 / 125000000) := by
  have h := checkLog_sound (w := (194813 / 2194813)) (n := 12)
    (lo := (177989687 / 1000000000)) (hi := (22248711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194813 / 1000000) = 1/(1000000 / 1194813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10853 : Bounds (177989687 / 1000000000) (22248711 / 125000000) (Real.log (1194813 / 1000000)) := by
  have h := reflection_log_10853_neg
  have he : Real.log (1194813 / 1000000) = -Real.log (1000000 / 1194813) := by
    rw [show ((1194813 / 1000000) : ℝ) = ((1000000 / 1194813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10854_neg : (21668073 / 100000000) ≤ -Real.log (805187 / 1000000) ∧
    -Real.log (805187 / 1000000) ≤ (216680731 / 1000000000) := by
  have h := checkLog_sound (w := (194813 / 1805187)) (n := 12)
    (lo := (21668073 / 100000000)) (hi := (216680731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805187) = 1/(805187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10854 : Bounds (-216680731 / 1000000000) (-21668073 / 100000000) (Real.log (805187 / 1000000)) := by
  have h := reflection_log_10854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10855_neg : (19345521 / 500000000) ≤ -Real.log (962047895031 / 1000000000000) ∧
    -Real.log (962047895031 / 1000000000000) ≤ (38691043 / 1000000000) := by
  have h := checkLog_sound (w := (37952104969 / 1962047895031)) (n := 12)
    (lo := (19345521 / 500000000)) (hi := (38691043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962047895031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962047895031) = 1/(962047895031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10855 : Bounds (-38691043 / 1000000000) (-19345521 / 500000000) (Real.log (962047895031 / 1000000000000)) := by
  have h := reflection_log_10855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10856_neg : (38323021 / 1000000000) ≤ -Real.log (240600503599 / 250000000000) ∧
    -Real.log (240600503599 / 250000000000) ≤ (19161511 / 500000000) := by
  have h := checkLog_sound (w := (9399496401 / 490600503599)) (n := 12)
    (lo := (38323021 / 1000000000)) (hi := (19161511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240600503599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240600503599) = 1/(240600503599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10856 : Bounds (-19161511 / 500000000) (-38323021 / 1000000000) (Real.log (240600503599 / 250000000000)) := by
  have h := reflection_log_10856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10857_neg : (39277689 / 100000000) ≤ -Real.log (31250000000 / 46283997107) ∧
    -Real.log (31250000000 / 46283997107) ≤ (392776891 / 1000000000) := by
  have h := checkLog_sound (w := (15033997107 / 77533997107)) (n := 12)
    (lo := (39277689 / 100000000)) (hi := (392776891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46283997107 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46283997107 / 31250000000) = 1/(31250000000 / 46283997107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10857 : Bounds (39277689 / 100000000) (392776891 / 1000000000) (Real.log (46283997107 / 31250000000)) := by
  have h := reflection_log_10857_neg
  have he : Real.log (46283997107 / 31250000000) = -Real.log (31250000000 / 46283997107) := by
    rw [show ((46283997107 / 31250000000) : ℝ) = ((31250000000 / 46283997107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10858_neg : (197335209 / 500000000) ≤ -Real.log (2000000000 / 2967790091) ∧
    -Real.log (2000000000 / 2967790091) ≤ (394670419 / 1000000000) := by
  have h := checkLog_sound (w := (967790091 / 4967790091)) (n := 12)
    (lo := (197335209 / 500000000)) (hi := (394670419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2967790091 / 2000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2967790091 / 2000000000) = 1/(2000000000 / 2967790091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10858 : Bounds (197335209 / 500000000) (394670419 / 1000000000) (Real.log (2967790091 / 2000000000)) := by
  have h := reflection_log_10858_neg
  have he : Real.log (2967790091 / 2000000000) = -Real.log (2000000000 / 2967790091) := by
    rw [show ((2967790091 / 2000000000) : ℝ) = ((2000000000 / 2967790091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10859_neg : (397724179 / 500000000) ≤ -Real.log (2500000000 / 5538585209) ∧
    -Real.log (2500000000 / 5538585209) ≤ (19886209 / 25000000) := by
  have h := checkLog_sound (w := (538585209 / 10538585209)) (n := 12)
    (lo := (51150589 / 500000000)) (hi := (102301179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5538585209 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5538585209 / 5000000000) = 1/(2500000000 / 5538585209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10859 : Bounds (397724179 / 500000000) (19886209 / 25000000) (Real.log (5538585209 / 2500000000)) := by
  have h := reflection_log_10859_neg
  have he : Real.log (5538585209 / 2500000000) = -Real.log (2500000000 / 5538585209) := by
    rw [show ((5538585209 / 2500000000) : ℝ) = ((2500000000 / 5538585209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10860_neg : (159556559 / 200000000) ≤ -Real.log (500000000000 / 1110305958133) ∧
    -Real.log (500000000000 / 1110305958133) ≤ (797782797 / 1000000000) := by
  have h := checkLog_sound (w := (110305958133 / 2110305958133)) (n := 12)
    (lo := (20927123 / 200000000)) (hi := (3269863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110305958133 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110305958133 / 1000000000000) = 1/(500000000000 / 1110305958133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10860 : Bounds (159556559 / 200000000) (797782797 / 1000000000) (Real.log (1110305958133 / 500000000000)) := by
  have h := reflection_log_10860_neg
  have he : Real.log (1110305958133 / 500000000000) = -Real.log (500000000000 / 1110305958133) := by
    rw [show ((1110305958133 / 500000000000) : ℝ) = ((500000000000 / 1110305958133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10861_neg : (322083499 / 1000000000) ≤ -Real.log (50 / 69) ∧
    -Real.log (50 / 69) ≤ (644167 / 2000000) := by
  have h := checkLog_sound (w := (19 / 119)) (n := 12)
    (lo := (322083499 / 1000000000)) (hi := (644167 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69 / 50) = 1/(50 / 69) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10861 : Bounds (322083499 / 1000000000) (644167 / 2000000) (Real.log (69 / 50)) := by
  have h := reflection_log_10861_neg
  have he : Real.log (69 / 50) = -Real.log (50 / 69) := by
    rw [show ((69 / 50) : ℝ) = ((50 / 69) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10862_neg : (2390179 / 5000000) ≤ -Real.log (31 / 50) ∧
    -Real.log (31 / 50) ≤ (478035801 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 81)) (n := 12)
    (lo := (2390179 / 5000000)) (hi := (478035801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 31) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 31) = 1/(31 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10862 : Bounds (-478035801 / 1000000000) (-2390179 / 5000000) (Real.log (31 / 50)) := by
  have h := reflection_log_10862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10863_neg : (379927 / 1000000000) ≤ -Real.log (50000 / 50019) ∧
    -Real.log (50000 / 50019) ≤ (47491 / 125000000) := by
  have h := checkLog_sound (w := (19 / 100019)) (n := 12)
    (lo := (379927 / 1000000000)) (hi := (47491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50019 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50019 / 50000) = 1/(50000 / 50019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10863 : Bounds (379927 / 1000000000) (47491 / 125000000) (Real.log (50019 / 50000)) := by
  have h := reflection_log_10863_neg
  have he : Real.log (50019 / 50000) = -Real.log (50000 / 50019) := by
    rw [show ((50019 / 50000) : ℝ) = ((50000 / 50019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10864_neg : (47509 / 125000000) ≤ -Real.log (49981 / 50000) ∧
    -Real.log (49981 / 50000) ≤ (380073 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 99981)) (n := 12)
    (lo := (47509 / 125000000)) (hi := (380073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49981) = 1/(49981 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10864 : Bounds (-380073 / 1000000000) (-47509 / 125000000) (Real.log (49981 / 50000)) := by
  have h := reflection_log_10864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10865_neg : (35536161 / 200000000) ≤ -Real.log (250000 / 298611) ∧
    -Real.log (250000 / 298611) ≤ (88840403 / 500000000) := by
  have h := checkLog_sound (w := (48611 / 548611)) (n := 12)
    (lo := (35536161 / 200000000)) (hi := (88840403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298611 / 250000) = 1/(250000 / 298611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10865 : Bounds (35536161 / 200000000) (88840403 / 500000000) (Real.log (298611 / 250000)) := by
  have h := reflection_log_10865_neg
  have he : Real.log (298611 / 250000) = -Real.log (250000 / 298611) := by
    rw [show ((298611 / 250000) : ℝ) = ((250000 / 298611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10866_neg : (54055639 / 250000000) ≤ -Real.log (201389 / 250000) ∧
    -Real.log (201389 / 250000) ≤ (216222557 / 1000000000) := by
  have h := checkLog_sound (w := (48611 / 451389)) (n := 12)
    (lo := (54055639 / 250000000)) (hi := (216222557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201389) = 1/(201389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10866 : Bounds (-216222557 / 1000000000) (-54055639 / 250000000) (Real.log (201389 / 250000)) := by
  have h := reflection_log_10866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10867_neg : (44610803 / 250000000) ≤ -Real.log (200000 / 239071) ∧
    -Real.log (200000 / 239071) ≤ (178443213 / 1000000000) := by
  have h := checkLog_sound (w := (39071 / 439071)) (n := 12)
    (lo := (44610803 / 250000000)) (hi := (178443213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239071 / 200000) = 1/(200000 / 239071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10867 : Bounds (44610803 / 250000000) (178443213 / 1000000000) (Real.log (239071 / 200000)) := by
  have h := reflection_log_10867_neg
  have he : Real.log (239071 / 200000) = -Real.log (200000 / 239071) := by
    rw [show ((239071 / 200000) : ℝ) = ((200000 / 239071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10868_neg : (54338523 / 250000000) ≤ -Real.log (160929 / 200000) ∧
    -Real.log (160929 / 200000) ≤ (217354093 / 1000000000) := by
  have h := checkLog_sound (w := (39071 / 360929)) (n := 12)
    (lo := (54338523 / 250000000)) (hi := (217354093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160929) = 1/(160929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10868 : Bounds (-217354093 / 1000000000) (-54338523 / 250000000) (Real.log (160929 / 200000)) := by
  have h := reflection_log_10868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10869_neg : (243193 / 6250000) ≤ -Real.log (38473456959 / 40000000000) ∧
    -Real.log (38473456959 / 40000000000) ≤ (38910881 / 1000000000) := by
  have h := checkLog_sound (w := (1526543041 / 78473456959)) (n := 12)
    (lo := (243193 / 6250000)) (hi := (38910881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38473456959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38473456959) = 1/(38473456959 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10869 : Bounds (-38910881 / 1000000000) (-243193 / 6250000) (Real.log (38473456959 / 40000000000)) := by
  have h := reflection_log_10869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10870_neg : (38541751 / 1000000000) ≤ -Real.log (60136970679 / 62500000000) ∧
    -Real.log (60136970679 / 62500000000) ≤ (4817719 / 125000000) := by
  have h := checkLog_sound (w := (2363029321 / 122636970679)) (n := 12)
    (lo := (38541751 / 1000000000)) (hi := (4817719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60136970679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60136970679) = 1/(60136970679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10870 : Bounds (-4817719 / 125000000) (-38541751 / 1000000000) (Real.log (60136970679 / 62500000000)) := by
  have h := reflection_log_10870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10871_neg : (393903361 / 1000000000) ≤ -Real.log (250000000000 / 370689312723) ∧
    -Real.log (250000000000 / 370689312723) ≤ (196951681 / 500000000) := by
  have h := checkLog_sound (w := (120689312723 / 620689312723)) (n := 12)
    (lo := (393903361 / 1000000000)) (hi := (196951681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370689312723 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370689312723 / 250000000000) = 1/(250000000000 / 370689312723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10871 : Bounds (393903361 / 1000000000) (196951681 / 500000000) (Real.log (370689312723 / 250000000000)) := by
  have h := reflection_log_10871_neg
  have he : Real.log (370689312723 / 250000000000) = -Real.log (250000000000 / 370689312723) := by
    rw [show ((370689312723 / 250000000000) : ℝ) = ((250000000000 / 370689312723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10872_neg : (79159461 / 200000000) ≤ -Real.log (125000000000 / 185696021227) ∧
    -Real.log (125000000000 / 185696021227) ≤ (197898653 / 500000000) := by
  have h := checkLog_sound (w := (60696021227 / 310696021227)) (n := 12)
    (lo := (79159461 / 200000000)) (hi := (197898653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185696021227 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185696021227 / 125000000000) = 1/(125000000000 / 185696021227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10872 : Bounds (79159461 / 200000000) (197898653 / 500000000) (Real.log (185696021227 / 125000000000)) := by
  have h := reflection_log_10872_neg
  have he : Real.log (185696021227 / 125000000000) = -Real.log (125000000000 / 185696021227) := by
    rw [show ((185696021227 / 125000000000) : ℝ) = ((125000000000 / 185696021227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10873_neg : (159556559 / 200000000) ≤ -Real.log (125000000000 / 277576489533) ∧
    -Real.log (125000000000 / 277576489533) ≤ (797782797 / 1000000000) := by
  have h := checkLog_sound (w := (27576489533 / 527576489533)) (n := 12)
    (lo := (20927123 / 200000000)) (hi := (3269863 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277576489533 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(277576489533 / 250000000000) = 1/(125000000000 / 277576489533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10873 : Bounds (159556559 / 200000000) (797782797 / 1000000000) (Real.log (277576489533 / 125000000000)) := by
  have h := reflection_log_10873_neg
  have he : Real.log (277576489533 / 125000000000) = -Real.log (125000000000 / 277576489533) := by
    rw [show ((277576489533 / 125000000000) : ℝ) = ((125000000000 / 277576489533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10874_neg : (800119299 / 1000000000) ≤ -Real.log (500000000000 / 1112903225807) ∧
    -Real.log (500000000000 / 1112903225807) ≤ (800119301 / 1000000000) := by
  have h := checkLog_sound (w := (112903225807 / 2112903225807)) (n := 12)
    (lo := (106972119 / 1000000000)) (hi := (2674303 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112903225807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1112903225807 / 1000000000000) = 1/(500000000000 / 1112903225807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10874 : Bounds (800119299 / 1000000000) (800119301 / 1000000000) (Real.log (1112903225807 / 500000000000)) := by
  have h := reflection_log_10874_neg
  have he : Real.log (1112903225807 / 500000000000) = -Real.log (500000000000 / 1112903225807) := by
    rw [show ((1112903225807 / 500000000000) : ℝ) = ((500000000000 / 1112903225807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10875_neg : (161403937 / 500000000) ≤ -Real.log (1000 / 1381) ∧
    -Real.log (1000 / 1381) ≤ (2582463 / 8000000) := by
  have h := checkLog_sound (w := (381 / 2381)) (n := 12)
    (lo := (161403937 / 500000000)) (hi := (2582463 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381 / 1000) = 1/(1000 / 1381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10875 : Bounds (161403937 / 500000000) (2582463 / 8000000) (Real.log (1381 / 1000)) := by
  have h := reflection_log_10875_neg
  have he : Real.log (1381 / 1000) = -Real.log (1000 / 1381) := by
    rw [show ((1381 / 1000) : ℝ) = ((1000 / 1381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10876_neg : (239825003 / 500000000) ≤ -Real.log (619 / 1000) ∧
    -Real.log (619 / 1000) ≤ (479650007 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 1619)) (n := 12)
    (lo := (239825003 / 500000000)) (hi := (479650007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 619) = 1/(619 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10876 : Bounds (-479650007 / 1000000000) (-239825003 / 500000000) (Real.log (619 / 1000)) := by
  have h := reflection_log_10876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10877_neg : (380927 / 1000000000) ≤ -Real.log (1000000 / 1000381) ∧
    -Real.log (1000000 / 1000381) ≤ (744 / 1953125) := by
  have h := checkLog_sound (w := (381 / 2000381)) (n := 12)
    (lo := (380927 / 1000000000)) (hi := (744 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000381 / 1000000) = 1/(1000000 / 1000381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10877 : Bounds (380927 / 1000000000) (744 / 1953125) (Real.log (1000381 / 1000000)) := by
  have h := reflection_log_10877_neg
  have he : Real.log (1000381 / 1000000) = -Real.log (1000000 / 1000381) := by
    rw [show ((1000381 / 1000000) : ℝ) = ((1000000 / 1000381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10878_neg : (23817 / 62500000) ≤ -Real.log (999619 / 1000000) ∧
    -Real.log (999619 / 1000000) ≤ (381073 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 1999619)) (n := 12)
    (lo := (23817 / 62500000)) (hi := (381073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999619) = 1/(999619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10878 : Bounds (-381073 / 1000000000) (-23817 / 62500000) (Real.log (999619 / 1000000)) := by
  have h := reflection_log_10878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10879_neg : (178133633 / 1000000000) ≤ -Real.log (200000 / 238997) ∧
    -Real.log (200000 / 238997) ≤ (89066817 / 500000000) := by
  have h := checkLog_sound (w := (38997 / 438997)) (n := 12)
    (lo := (178133633 / 1000000000)) (hi := (89066817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238997 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238997 / 200000) = 1/(200000 / 238997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10879 : Bounds (178133633 / 1000000000) (89066817 / 500000000) (Real.log (238997 / 200000)) := by
  have h := reflection_log_10879_neg
  have he : Real.log (238997 / 200000) = -Real.log (200000 / 238997) := by
    rw [show ((238997 / 200000) : ℝ) = ((200000 / 238997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
