import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10752_neg : (389582211 / 500000000) ≤ -Real.log (500000000000 / 1089825119237) ∧
    -Real.log (500000000000 / 1089825119237) ≤ (97395553 / 125000000) := by
  have h := checkLog_sound (w := (89825119237 / 2089825119237)) (n := 12)
    (lo := (43008621 / 500000000)) (hi := (86017243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089825119237 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1089825119237 / 1000000000000) = 1/(500000000000 / 1089825119237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10752 : Bounds (389582211 / 500000000) (97395553 / 125000000) (Real.log (1089825119237 / 500000000000)) := by
  have h := reflection_log_10752_neg
  have he : Real.log (1089825119237 / 500000000000) = -Real.log (500000000000 / 1089825119237) := by
    rw [show ((1089825119237 / 500000000000) : ℝ) = ((500000000000 / 1089825119237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10753_neg : (316269529 / 1000000000) ≤ -Real.log (250 / 343) ∧
    -Real.log (250 / 343) ≤ (31626953 / 100000000) := by
  have h := checkLog_sound (w := (93 / 593)) (n := 12)
    (lo := (316269529 / 1000000000)) (hi := (31626953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343 / 250) = 1/(250 / 343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10753 : Bounds (316269529 / 1000000000) (31626953 / 100000000) (Real.log (343 / 250)) := by
  have h := reflection_log_10753_neg
  have he : Real.log (343 / 250) = -Real.log (250 / 343) := by
    rw [show ((343 / 250) : ℝ) = ((250 / 343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10754_neg : (58151889 / 125000000) ≤ -Real.log (157 / 250) ∧
    -Real.log (157 / 250) ≤ (465215113 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 407)) (n := 12)
    (lo := (58151889 / 125000000)) (hi := (465215113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 157) = 1/(157 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10754 : Bounds (-465215113 / 1000000000) (-58151889 / 125000000) (Real.log (157 / 250)) := by
  have h := reflection_log_10754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10755_neg : (37193 / 100000000) ≤ -Real.log (250000 / 250093) ∧
    -Real.log (250000 / 250093) ≤ (371931 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 500093)) (n := 12)
    (lo := (37193 / 100000000)) (hi := (371931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250093 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250093 / 250000) = 1/(250000 / 250093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10755 : Bounds (37193 / 100000000) (371931 / 1000000000) (Real.log (250093 / 250000)) := by
  have h := reflection_log_10755_neg
  have he : Real.log (250093 / 250000) = -Real.log (250000 / 250093) := by
    rw [show ((250093 / 250000) : ℝ) = ((250000 / 250093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10756_neg : (372069 / 1000000000) ≤ -Real.log (249907 / 250000) ∧
    -Real.log (249907 / 250000) ≤ (37207 / 100000000) := by
  have h := checkLog_sound (w := (93 / 499907)) (n := 12)
    (lo := (372069 / 1000000000)) (hi := (37207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249907) = 1/(249907 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10756 : Bounds (-37207 / 100000000) (-372069 / 1000000000) (Real.log (249907 / 250000)) := by
  have h := reflection_log_10756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10757_neg : (87027071 / 500000000) ≤ -Real.log (25000 / 29753) ∧
    -Real.log (25000 / 29753) ≤ (174054143 / 1000000000) := by
  have h := checkLog_sound (w := (4753 / 54753)) (n := 12)
    (lo := (87027071 / 500000000)) (hi := (174054143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29753 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29753 / 25000) = 1/(25000 / 29753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10757 : Bounds (87027071 / 500000000) (174054143 / 1000000000) (Real.log (29753 / 25000)) := by
  have h := reflection_log_10757_neg
  have he : Real.log (29753 / 25000) = -Real.log (25000 / 29753) := by
    rw [show ((29753 / 25000) : ℝ) = ((25000 / 29753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10758_neg : (21086919 / 100000000) ≤ -Real.log (20247 / 25000) ∧
    -Real.log (20247 / 25000) ≤ (210869191 / 1000000000) := by
  have h := checkLog_sound (w := (4753 / 45247)) (n := 12)
    (lo := (21086919 / 100000000)) (hi := (210869191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20247) = 1/(20247 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10758 : Bounds (-210869191 / 1000000000) (-21086919 / 100000000) (Real.log (20247 / 25000)) := by
  have h := reflection_log_10758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10759_neg : (174812601 / 1000000000) ≤ -Real.log (1000000 / 1191023) ∧
    -Real.log (1000000 / 1191023) ≤ (87406301 / 500000000) := by
  have h := checkLog_sound (w := (191023 / 2191023)) (n := 12)
    (lo := (174812601 / 1000000000)) (hi := (87406301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191023 / 1000000) = 1/(1000000 / 1191023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10759 : Bounds (174812601 / 1000000000) (87406301 / 500000000) (Real.log (1191023 / 1000000)) := by
  have h := reflection_log_10759_neg
  have he : Real.log (1191023 / 1000000) = -Real.log (1000000 / 1191023) := by
    rw [show ((1191023 / 1000000) : ℝ) = ((1000000 / 1191023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10760_neg : (26498099 / 125000000) ≤ -Real.log (808977 / 1000000) ∧
    -Real.log (808977 / 1000000) ≤ (211984793 / 1000000000) := by
  have h := checkLog_sound (w := (191023 / 1808977)) (n := 12)
    (lo := (26498099 / 125000000)) (hi := (211984793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808977) = 1/(808977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10760 : Bounds (-211984793 / 1000000000) (-26498099 / 125000000) (Real.log (808977 / 1000000)) := by
  have h := reflection_log_10760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10761_neg : (3717219 / 100000000) ≤ -Real.log (963510213471 / 1000000000000) ∧
    -Real.log (963510213471 / 1000000000000) ≤ (37172191 / 1000000000) := by
  have h := checkLog_sound (w := (36489786529 / 1963510213471)) (n := 12)
    (lo := (3717219 / 100000000)) (hi := (37172191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963510213471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963510213471) = 1/(963510213471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10761 : Bounds (-37172191 / 1000000000) (-3717219 / 100000000) (Real.log (963510213471 / 1000000000000)) := by
  have h := reflection_log_10761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10762_neg : (4601881 / 125000000) ≤ -Real.log (602408991 / 625000000) ∧
    -Real.log (602408991 / 625000000) ≤ (36815049 / 1000000000) := by
  have h := checkLog_sound (w := (22591009 / 1227408991)) (n := 12)
    (lo := (4601881 / 125000000)) (hi := (36815049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 602408991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 602408991) = 1/(602408991 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10762 : Bounds (-36815049 / 1000000000) (-4601881 / 125000000) (Real.log (602408991 / 625000000)) := by
  have h := reflection_log_10762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10763_neg : (96230833 / 250000000) ≤ -Real.log (500000000000 / 734750827283) ∧
    -Real.log (500000000000 / 734750827283) ≤ (384923333 / 1000000000) := by
  have h := checkLog_sound (w := (234750827283 / 1234750827283)) (n := 12)
    (lo := (96230833 / 250000000)) (hi := (384923333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734750827283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734750827283 / 500000000000) = 1/(500000000000 / 734750827283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10763 : Bounds (96230833 / 250000000) (384923333 / 1000000000) (Real.log (734750827283 / 500000000000)) := by
  have h := reflection_log_10763_neg
  have he : Real.log (734750827283 / 500000000000) = -Real.log (500000000000 / 734750827283) := by
    rw [show ((734750827283 / 500000000000) : ℝ) = ((500000000000 / 734750827283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10764_neg : (193398697 / 500000000) ≤ -Real.log (500000000000 / 736129086489) ∧
    -Real.log (500000000000 / 736129086489) ≤ (77359479 / 200000000) := by
  have h := checkLog_sound (w := (236129086489 / 1236129086489)) (n := 12)
    (lo := (193398697 / 500000000)) (hi := (77359479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736129086489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736129086489 / 500000000000) = 1/(500000000000 / 736129086489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10764 : Bounds (193398697 / 500000000) (77359479 / 200000000) (Real.log (736129086489 / 500000000000)) := by
  have h := reflection_log_10764_neg
  have he : Real.log (736129086489 / 500000000000) = -Real.log (500000000000 / 736129086489) := by
    rw [show ((736129086489 / 500000000000) : ℝ) = ((500000000000 / 736129086489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10765_neg : (389582211 / 500000000) ≤ -Real.log (125000000000 / 272456279809) ∧
    -Real.log (125000000000 / 272456279809) ≤ (97395553 / 125000000) := by
  have h := checkLog_sound (w := (22456279809 / 522456279809)) (n := 12)
    (lo := (43008621 / 500000000)) (hi := (86017243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272456279809 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272456279809 / 250000000000) = 1/(125000000000 / 272456279809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10765 : Bounds (389582211 / 500000000) (97395553 / 125000000) (Real.log (272456279809 / 125000000000)) := by
  have h := reflection_log_10765_neg
  have he : Real.log (272456279809 / 125000000000) = -Real.log (125000000000 / 272456279809) := by
    rw [show ((272456279809 / 125000000000) : ℝ) = ((125000000000 / 272456279809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10766_neg : (781484641 / 1000000000) ≤ -Real.log (500000000000 / 1092356687899) ∧
    -Real.log (500000000000 / 1092356687899) ≤ (781484643 / 1000000000) := by
  have h := checkLog_sound (w := (92356687899 / 2092356687899)) (n := 12)
    (lo := (88337461 / 1000000000)) (hi := (44168731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092356687899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1092356687899 / 1000000000000) = 1/(500000000000 / 1092356687899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10766 : Bounds (781484641 / 1000000000) (781484643 / 1000000000) (Real.log (1092356687899 / 500000000000)) := by
  have h := reflection_log_10766_neg
  have he : Real.log (1092356687899 / 500000000000) = -Real.log (500000000000 / 1092356687899) := by
    rw [show ((1092356687899 / 500000000000) : ℝ) = ((500000000000 / 1092356687899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10767_neg : (158499063 / 500000000) ≤ -Real.log (1000 / 1373) ∧
    -Real.log (1000 / 1373) ≤ (316998127 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2373)) (n := 12)
    (lo := (158499063 / 500000000)) (hi := (316998127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1000) = 1/(1000 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10767 : Bounds (158499063 / 500000000) (316998127 / 1000000000) (Real.log (1373 / 1000)) := by
  have h := reflection_log_10767_neg
  have he : Real.log (1373 / 1000) = -Real.log (1000 / 1373) := by
    rw [show ((1373 / 1000) : ℝ) = ((1000 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10768_neg : (233404369 / 500000000) ≤ -Real.log (627 / 1000) ∧
    -Real.log (627 / 1000) ≤ (466808739 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 1627)) (n := 12)
    (lo := (233404369 / 500000000)) (hi := (466808739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 627) = 1/(627 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10768 : Bounds (-466808739 / 1000000000) (-233404369 / 500000000) (Real.log (627 / 1000)) := by
  have h := reflection_log_10768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10769_neg : (37293 / 100000000) ≤ -Real.log (1000000 / 1000373) ∧
    -Real.log (1000000 / 1000373) ≤ (372931 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 2000373)) (n := 12)
    (lo := (37293 / 100000000)) (hi := (372931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000373 / 1000000) = 1/(1000000 / 1000373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10769 : Bounds (37293 / 100000000) (372931 / 1000000000) (Real.log (1000373 / 1000000)) := by
  have h := reflection_log_10769_neg
  have he : Real.log (1000373 / 1000000) = -Real.log (1000000 / 1000373) := by
    rw [show ((1000373 / 1000000) : ℝ) = ((1000000 / 1000373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10770_neg : (373069 / 1000000000) ≤ -Real.log (999627 / 1000000) ∧
    -Real.log (999627 / 1000000) ≤ (37307 / 100000000) := by
  have h := checkLog_sound (w := (373 / 1999627)) (n := 12)
    (lo := (373069 / 1000000000)) (hi := (37307 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999627) = 1/(999627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10770 : Bounds (-37307 / 100000000) (-373069 / 1000000000) (Real.log (999627 / 1000000)) := by
  have h := reflection_log_10770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10771_neg : (6980311 / 40000000) ≤ -Real.log (50000 / 59533) ∧
    -Real.log (50000 / 59533) ≤ (681671 / 3906250) := by
  have h := checkLog_sound (w := (9533 / 109533)) (n := 12)
    (lo := (6980311 / 40000000)) (hi := (681671 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59533 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59533 / 50000) = 1/(50000 / 59533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10771 : Bounds (6980311 / 40000000) (681671 / 3906250) (Real.log (59533 / 50000)) := by
  have h := reflection_log_10771_neg
  have he : Real.log (59533 / 50000) = -Real.log (50000 / 59533) := by
    rw [show ((59533 / 50000) : ℝ) = ((50000 / 59533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10772_neg : (105768089 / 500000000) ≤ -Real.log (40467 / 50000) ∧
    -Real.log (40467 / 50000) ≤ (211536179 / 1000000000) := by
  have h := checkLog_sound (w := (9533 / 90467)) (n := 12)
    (lo := (105768089 / 500000000)) (hi := (211536179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40467) = 1/(40467 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10772 : Bounds (-211536179 / 1000000000) (-105768089 / 500000000) (Real.log (40467 / 50000)) := by
  have h := reflection_log_10772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10773_neg : (175266729 / 1000000000) ≤ -Real.log (250000 / 297891) ∧
    -Real.log (250000 / 297891) ≤ (17526673 / 100000000) := by
  have h := checkLog_sound (w := (47891 / 547891)) (n := 12)
    (lo := (175266729 / 1000000000)) (hi := (17526673 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297891 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297891 / 250000) = 1/(250000 / 297891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10773 : Bounds (175266729 / 1000000000) (17526673 / 100000000) (Real.log (297891 / 250000)) := by
  have h := reflection_log_10773_neg
  have he : Real.log (297891 / 250000) = -Real.log (250000 / 297891) := by
    rw [show ((297891 / 250000) : ℝ) = ((250000 / 297891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10774_neg : (106326881 / 500000000) ≤ -Real.log (202109 / 250000) ∧
    -Real.log (202109 / 250000) ≤ (212653763 / 1000000000) := by
  have h := checkLog_sound (w := (47891 / 452109)) (n := 12)
    (lo := (106326881 / 500000000)) (hi := (212653763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202109) = 1/(202109 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10774 : Bounds (-212653763 / 1000000000) (-106326881 / 500000000) (Real.log (202109 / 250000)) := by
  have h := reflection_log_10774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10775_neg : (4673379 / 125000000) ≤ -Real.log (60206452119 / 62500000000) ∧
    -Real.log (60206452119 / 62500000000) ≤ (37387033 / 1000000000) := by
  have h := checkLog_sound (w := (2293547881 / 122706452119)) (n := 12)
    (lo := (4673379 / 125000000)) (hi := (37387033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60206452119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60206452119) = 1/(60206452119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10775 : Bounds (-37387033 / 1000000000) (-4673379 / 125000000) (Real.log (60206452119 / 62500000000)) := by
  have h := reflection_log_10775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10776_neg : (37028403 / 1000000000) ≤ -Real.log (2409121911 / 2500000000) ∧
    -Real.log (2409121911 / 2500000000) ≤ (9257101 / 250000000) := by
  have h := checkLog_sound (w := (90878089 / 4909121911)) (n := 12)
    (lo := (37028403 / 1000000000)) (hi := (9257101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2409121911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2409121911) = 1/(2409121911 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10776 : Bounds (-9257101 / 250000000) (-37028403 / 1000000000) (Real.log (2409121911 / 2500000000)) := by
  have h := reflection_log_10776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10777_neg : (386043953 / 1000000000) ≤ -Real.log (500000000000 / 735574665777) ∧
    -Real.log (500000000000 / 735574665777) ≤ (193021977 / 500000000) := by
  have h := checkLog_sound (w := (235574665777 / 1235574665777)) (n := 12)
    (lo := (386043953 / 1000000000)) (hi := (193021977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735574665777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735574665777 / 500000000000) = 1/(500000000000 / 735574665777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10777 : Bounds (386043953 / 1000000000) (193021977 / 500000000) (Real.log (735574665777 / 500000000000)) := by
  have h := reflection_log_10777_neg
  have he : Real.log (735574665777 / 500000000000) = -Real.log (500000000000 / 735574665777) := by
    rw [show ((735574665777 / 500000000000) : ℝ) = ((500000000000 / 735574665777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10778_neg : (387920491 / 1000000000) ≤ -Real.log (500000000000 / 736956295861) ∧
    -Real.log (500000000000 / 736956295861) ≤ (96980123 / 250000000) := by
  have h := checkLog_sound (w := (236956295861 / 1236956295861)) (n := 12)
    (lo := (387920491 / 1000000000)) (hi := (96980123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736956295861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736956295861 / 500000000000) = 1/(500000000000 / 736956295861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10778 : Bounds (387920491 / 1000000000) (96980123 / 250000000) (Real.log (736956295861 / 500000000000)) := by
  have h := reflection_log_10778_neg
  have he : Real.log (736956295861 / 500000000000) = -Real.log (500000000000 / 736956295861) := by
    rw [show ((736956295861 / 500000000000) : ℝ) = ((500000000000 / 736956295861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10779_neg : (781484641 / 1000000000) ≤ -Real.log (250000000000 / 546178343949) ∧
    -Real.log (250000000000 / 546178343949) ≤ (781484643 / 1000000000) := by
  have h := checkLog_sound (w := (46178343949 / 1046178343949)) (n := 12)
    (lo := (88337461 / 1000000000)) (hi := (44168731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546178343949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(546178343949 / 500000000000) = 1/(250000000000 / 546178343949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10779 : Bounds (781484641 / 1000000000) (781484643 / 1000000000) (Real.log (546178343949 / 250000000000)) := by
  have h := reflection_log_10779_neg
  have he : Real.log (546178343949 / 250000000000) = -Real.log (250000000000 / 546178343949) := by
    rw [show ((546178343949 / 250000000000) : ℝ) = ((250000000000 / 546178343949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10780_neg : (48987929 / 62500000) ≤ -Real.log (500000000000 / 1094896331739) ∧
    -Real.log (500000000000 / 1094896331739) ≤ (391903433 / 500000000) := by
  have h := checkLog_sound (w := (94896331739 / 2094896331739)) (n := 12)
    (lo := (22664921 / 250000000)) (hi := (18131937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094896331739 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094896331739 / 1000000000000) = 1/(500000000000 / 1094896331739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10780 : Bounds (48987929 / 62500000) (391903433 / 500000000) (Real.log (1094896331739 / 500000000000)) := by
  have h := reflection_log_10780_neg
  have he : Real.log (1094896331739 / 500000000000) = -Real.log (500000000000 / 1094896331739) := by
    rw [show ((1094896331739 / 500000000000) : ℝ) = ((500000000000 / 1094896331739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10781_neg : (317726193 / 1000000000) ≤ -Real.log (500 / 687) ∧
    -Real.log (500 / 687) ≤ (158863097 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1187)) (n := 12)
    (lo := (317726193 / 1000000000)) (hi := (158863097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 500) = 1/(500 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10781 : Bounds (317726193 / 1000000000) (158863097 / 500000000) (Real.log (687 / 500)) := by
  have h := reflection_log_10781_neg
  have he : Real.log (687 / 500) = -Real.log (500 / 687) := by
    rw [show ((687 / 500) : ℝ) = ((500 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10782_neg : (468404907 / 1000000000) ≤ -Real.log (313 / 500) ∧
    -Real.log (313 / 500) ≤ (117101227 / 250000000) := by
  have h := checkLog_sound (w := (187 / 813)) (n := 12)
    (lo := (468404907 / 1000000000)) (hi := (117101227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 313) = 1/(313 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10782 : Bounds (-117101227 / 250000000) (-468404907 / 1000000000) (Real.log (313 / 500)) := by
  have h := reflection_log_10782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10783_neg : (37393 / 100000000) ≤ -Real.log (500000 / 500187) ∧
    -Real.log (500000 / 500187) ≤ (373931 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 1000187)) (n := 12)
    (lo := (37393 / 100000000)) (hi := (373931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500187 / 500000) = 1/(500000 / 500187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10783 : Bounds (37393 / 100000000) (373931 / 1000000000) (Real.log (500187 / 500000)) := by
  have h := reflection_log_10783_neg
  have he : Real.log (500187 / 500000) = -Real.log (500000 / 500187) := by
    rw [show ((500187 / 500000) : ℝ) = ((500000 / 500187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10784_neg : (374069 / 1000000000) ≤ -Real.log (499813 / 500000) ∧
    -Real.log (499813 / 500000) ≤ (37407 / 100000000) := by
  have h := checkLog_sound (w := (187 / 999813)) (n := 12)
    (lo := (374069 / 1000000000)) (hi := (37407 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499813) = 1/(499813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10784 : Bounds (-37407 / 100000000) (-374069 / 1000000000) (Real.log (499813 / 500000)) := by
  have h := reflection_log_10784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10785_neg : (43930163 / 250000000) ≤ -Real.log (200000 / 238421) ∧
    -Real.log (200000 / 238421) ≤ (175720653 / 1000000000) := by
  have h := checkLog_sound (w := (38421 / 438421)) (n := 12)
    (lo := (43930163 / 250000000)) (hi := (175720653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238421 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238421 / 200000) = 1/(200000 / 238421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10785 : Bounds (43930163 / 250000000) (175720653 / 1000000000) (Real.log (238421 / 200000)) := by
  have h := reflection_log_10785_neg
  have he : Real.log (238421 / 200000) = -Real.log (200000 / 238421) := by
    rw [show ((238421 / 200000) : ℝ) = ((200000 / 238421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10786_neg : (213323179 / 1000000000) ≤ -Real.log (161579 / 200000) ∧
    -Real.log (161579 / 200000) ≤ (10666159 / 50000000) := by
  have h := checkLog_sound (w := (38421 / 361579)) (n := 12)
    (lo := (213323179 / 1000000000)) (hi := (10666159 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161579) = 1/(161579 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10786 : Bounds (-10666159 / 50000000) (-213323179 / 1000000000) (Real.log (161579 / 200000)) := by
  have h := reflection_log_10786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10787_neg : (37602527 / 1000000000) ≤ -Real.log (38523826759 / 40000000000) ∧
    -Real.log (38523826759 / 40000000000) ≤ (1175079 / 31250000) := by
  have h := checkLog_sound (w := (1476173241 / 78523826759)) (n := 12)
    (lo := (37602527 / 1000000000)) (hi := (1175079 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38523826759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38523826759) = 1/(38523826759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10787 : Bounds (-1175079 / 31250000) (-37602527 / 1000000000) (Real.log (38523826759 / 40000000000)) := by
  have h := reflection_log_10787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10788_neg : (4655301 / 125000000) ≤ -Real.log (1505379 / 1562500) ∧
    -Real.log (1505379 / 1562500) ≤ (37242409 / 1000000000) := by
  have h := checkLog_sound (w := (57121 / 3067879)) (n := 12)
    (lo := (4655301 / 125000000)) (hi := (37242409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562500 / 1505379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562500 / 1505379) = 1/(1505379 / 1562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10788 : Bounds (-37242409 / 1000000000) (-4655301 / 125000000) (Real.log (1505379 / 1562500)) := by
  have h := reflection_log_10788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10789_neg : (389043831 / 1000000000) ≤ -Real.log (5000000000 / 7377846131) ∧
    -Real.log (5000000000 / 7377846131) ≤ (48630479 / 125000000) := by
  have h := checkLog_sound (w := (2377846131 / 12377846131)) (n := 12)
    (lo := (389043831 / 1000000000)) (hi := (48630479 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7377846131 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7377846131 / 5000000000) = 1/(5000000000 / 7377846131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10789 : Bounds (389043831 / 1000000000) (48630479 / 125000000) (Real.log (7377846131 / 5000000000)) := by
  have h := reflection_log_10789_neg
  have he : Real.log (7377846131 / 5000000000) = -Real.log (5000000000 / 7377846131) := by
    rw [show ((7377846131 / 5000000000) : ℝ) = ((5000000000 / 7377846131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10790_neg : (48987929 / 62500000) ≤ -Real.log (250000000000 / 547448165869) ∧
    -Real.log (250000000000 / 547448165869) ≤ (391903433 / 500000000) := by
  have h := checkLog_sound (w := (47448165869 / 1047448165869)) (n := 12)
    (lo := (22664921 / 250000000)) (hi := (18131937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547448165869 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(547448165869 / 500000000000) = 1/(250000000000 / 547448165869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10790 : Bounds (48987929 / 62500000) (391903433 / 500000000) (Real.log (547448165869 / 250000000000)) := by
  have h := reflection_log_10790_neg
  have he : Real.log (547448165869 / 250000000000) = -Real.log (250000000000 / 547448165869) := by
    rw [show ((547448165869 / 250000000000) : ℝ) = ((250000000000 / 547448165869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10791_neg : (786131101 / 1000000000) ≤ -Real.log (500000000000 / 1097444089457) ∧
    -Real.log (500000000000 / 1097444089457) ≤ (786131103 / 1000000000) := by
  have h := checkLog_sound (w := (97444089457 / 2097444089457)) (n := 12)
    (lo := (92983921 / 1000000000)) (hi := (46491961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097444089457 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1097444089457 / 1000000000000) = 1/(500000000000 / 1097444089457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10791 : Bounds (786131101 / 1000000000) (786131103 / 1000000000) (Real.log (1097444089457 / 500000000000)) := by
  have h := reflection_log_10791_neg
  have he : Real.log (1097444089457 / 500000000000) = -Real.log (500000000000 / 1097444089457) := by
    rw [show ((1097444089457 / 500000000000) : ℝ) = ((500000000000 / 1097444089457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10792_neg : (318453731 / 1000000000) ≤ -Real.log (8 / 11) ∧
    -Real.log (8 / 11) ≤ (79613433 / 250000000) := by
  have h := checkLog_sound (w := (3 / 19)) (n := 12)
    (lo := (318453731 / 1000000000)) (hi := (79613433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 8) = 1/(8 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10792 : Bounds (318453731 / 1000000000) (79613433 / 250000000) (Real.log (11 / 8)) := by
  have h := reflection_log_10792_neg
  have he : Real.log (11 / 8) = -Real.log (8 / 11) := by
    rw [show ((11 / 8) : ℝ) = ((8 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10793_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10793 : Bounds (-47000363 / 100000000) (-470003629 / 1000000000) (Real.log (5 / 8)) := by
  have h := reflection_log_10793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10794_neg : (374929 / 1000000000) ≤ -Real.log (8000 / 8003) ∧
    -Real.log (8000 / 8003) ≤ (37493 / 100000000) := by
  have h := checkLog_sound (w := (3 / 16003)) (n := 12)
    (lo := (374929 / 1000000000)) (hi := (37493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8003 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8003 / 8000) = 1/(8000 / 8003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10794 : Bounds (374929 / 1000000000) (37493 / 100000000) (Real.log (8003 / 8000)) := by
  have h := reflection_log_10794_neg
  have he : Real.log (8003 / 8000) = -Real.log (8000 / 8003) := by
    rw [show ((8003 / 8000) : ℝ) = ((8000 / 8003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10795_neg : (37507 / 100000000) ≤ -Real.log (7997 / 8000) ∧
    -Real.log (7997 / 8000) ≤ (375071 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 15997)) (n := 12)
    (lo := (37507 / 100000000)) (hi := (375071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7997) = 1/(7997 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10795 : Bounds (-375071 / 1000000000) (-37507 / 100000000) (Real.log (7997 / 8000)) := by
  have h := reflection_log_10795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10796_neg : (21926803 / 125000000) ≤ -Real.log (50000 / 59587) ∧
    -Real.log (50000 / 59587) ≤ (7016577 / 40000000) := by
  have h := checkLog_sound (w := (9587 / 109587)) (n := 12)
    (lo := (21926803 / 125000000)) (hi := (7016577 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59587 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59587 / 50000) = 1/(50000 / 59587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10796 : Bounds (21926803 / 125000000) (7016577 / 40000000) (Real.log (59587 / 50000)) := by
  have h := reflection_log_10796_neg
  have he : Real.log (59587 / 50000) = -Real.log (50000 / 59587) := by
    rw [show ((59587 / 50000) : ℝ) = ((50000 / 59587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10797_neg : (21287149 / 100000000) ≤ -Real.log (40413 / 50000) ∧
    -Real.log (40413 / 50000) ≤ (212871491 / 1000000000) := by
  have h := checkLog_sound (w := (9587 / 90413)) (n := 12)
    (lo := (21287149 / 100000000)) (hi := (212871491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40413) = 1/(40413 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10797 : Bounds (-212871491 / 1000000000) (-21287149 / 100000000) (Real.log (40413 / 50000)) := by
  have h := reflection_log_10797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10798_neg : (5505449 / 31250000) ≤ -Real.log (500000 / 596323) ∧
    -Real.log (500000 / 596323) ≤ (176174369 / 1000000000) := by
  have h := checkLog_sound (w := (96323 / 1096323)) (n := 12)
    (lo := (5505449 / 31250000)) (hi := (176174369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596323 / 500000) = 1/(500000 / 596323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10798 : Bounds (5505449 / 31250000) (176174369 / 1000000000) (Real.log (596323 / 500000)) := by
  have h := reflection_log_10798_neg
  have he : Real.log (596323 / 500000) = -Real.log (500000 / 596323) := by
    rw [show ((596323 / 500000) : ℝ) = ((500000 / 596323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10799_neg : (42798609 / 200000000) ≤ -Real.log (403677 / 500000) ∧
    -Real.log (403677 / 500000) ≤ (106996523 / 500000000) := by
  have h := checkLog_sound (w := (96323 / 903677)) (n := 12)
    (lo := (42798609 / 200000000)) (hi := (106996523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403677) = 1/(403677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10799 : Bounds (-106996523 / 500000000) (-42798609 / 200000000) (Real.log (403677 / 500000)) := by
  have h := reflection_log_10799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10800_neg : (37818677 / 1000000000) ≤ -Real.log (240721879671 / 250000000000) ∧
    -Real.log (240721879671 / 250000000000) ≤ (18909339 / 500000000) := by
  have h := checkLog_sound (w := (9278120329 / 490721879671)) (n := 12)
    (lo := (37818677 / 1000000000)) (hi := (18909339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240721879671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240721879671) = 1/(240721879671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10800 : Bounds (-18909339 / 500000000) (-37818677 / 1000000000) (Real.log (240721879671 / 250000000000)) := by
  have h := reflection_log_10800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10801_neg : (7491413 / 200000000) ≤ -Real.log (2408089431 / 2500000000) ∧
    -Real.log (2408089431 / 2500000000) ≤ (18728533 / 500000000) := by
  have h := checkLog_sound (w := (91910569 / 4908089431)) (n := 12)
    (lo := (7491413 / 200000000)) (hi := (18728533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2408089431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2408089431) = 1/(2408089431 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10801 : Bounds (-18728533 / 500000000) (-7491413 / 200000000) (Real.log (2408089431 / 2500000000)) := by
  have h := reflection_log_10801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10802_neg : (194142957 / 500000000) ≤ -Real.log (500000000000 / 737225645213) ∧
    -Real.log (500000000000 / 737225645213) ≤ (77657183 / 200000000) := by
  have h := checkLog_sound (w := (237225645213 / 1237225645213)) (n := 12)
    (lo := (194142957 / 500000000)) (hi := (77657183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737225645213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737225645213 / 500000000000) = 1/(500000000000 / 737225645213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10802 : Bounds (194142957 / 500000000) (77657183 / 200000000) (Real.log (737225645213 / 500000000000)) := by
  have h := reflection_log_10802_neg
  have he : Real.log (737225645213 / 500000000000) = -Real.log (500000000000 / 737225645213) := by
    rw [show ((737225645213 / 500000000000) : ℝ) = ((500000000000 / 737225645213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10803_neg : (390167413 / 1000000000) ≤ -Real.log (250000000000 / 369307020217) ∧
    -Real.log (250000000000 / 369307020217) ≤ (195083707 / 500000000) := by
  have h := checkLog_sound (w := (119307020217 / 619307020217)) (n := 12)
    (lo := (390167413 / 1000000000)) (hi := (195083707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369307020217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369307020217 / 250000000000) = 1/(250000000000 / 369307020217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10803 : Bounds (390167413 / 1000000000) (195083707 / 500000000) (Real.log (369307020217 / 250000000000)) := by
  have h := reflection_log_10803_neg
  have he : Real.log (369307020217 / 250000000000) = -Real.log (250000000000 / 369307020217) := by
    rw [show ((369307020217 / 250000000000) : ℝ) = ((250000000000 / 369307020217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10804_neg : (786131101 / 1000000000) ≤ -Real.log (31250000000 / 68590255591) ∧
    -Real.log (31250000000 / 68590255591) ≤ (786131103 / 1000000000) := by
  have h := checkLog_sound (w := (6090255591 / 131090255591)) (n := 12)
    (lo := (92983921 / 1000000000)) (hi := (46491961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68590255591 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68590255591 / 62500000000) = 1/(31250000000 / 68590255591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10804 : Bounds (786131101 / 1000000000) (786131103 / 1000000000) (Real.log (68590255591 / 31250000000)) := by
  have h := reflection_log_10804_neg
  have he : Real.log (68590255591 / 31250000000) = -Real.log (31250000000 / 68590255591) := by
    rw [show ((68590255591 / 31250000000) : ℝ) = ((31250000000 / 68590255591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10805_neg : (788457359 / 1000000000) ≤ -Real.log (5 / 11) ∧
    -Real.log (5 / 11) ≤ (788457361 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11 / 10) = 1/(5 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10805 : Bounds (788457359 / 1000000000) (788457361 / 1000000000) (Real.log (11 / 5)) := by
  have h := reflection_log_10805_neg
  have he : Real.log (11 / 5) = -Real.log (5 / 11) := by
    rw [show ((11 / 5) : ℝ) = ((5 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10806_neg : (319180739 / 1000000000) ≤ -Real.log (125 / 172) ∧
    -Real.log (125 / 172) ≤ (15959037 / 50000000) := by
  have h := checkLog_sound (w := (47 / 297)) (n := 12)
    (lo := (319180739 / 1000000000)) (hi := (15959037 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172 / 125) = 1/(125 / 172) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10806 : Bounds (319180739 / 1000000000) (15959037 / 50000000) (Real.log (172 / 125)) := by
  have h := reflection_log_10806_neg
  have he : Real.log (172 / 125) = -Real.log (125 / 172) := by
    rw [show ((172 / 125) : ℝ) = ((125 / 172) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10807_neg : (47160491 / 100000000) ≤ -Real.log (78 / 125) ∧
    -Real.log (78 / 125) ≤ (471604911 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 203)) (n := 12)
    (lo := (47160491 / 100000000)) (hi := (471604911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 78) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 78) = 1/(78 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10807 : Bounds (-471604911 / 1000000000) (-47160491 / 100000000) (Real.log (78 / 125)) := by
  have h := reflection_log_10807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10808_neg : (375929 / 1000000000) ≤ -Real.log (125000 / 125047) ∧
    -Real.log (125000 / 125047) ≤ (37593 / 100000000) := by
  have h := checkLog_sound (w := (47 / 250047)) (n := 12)
    (lo := (375929 / 1000000000)) (hi := (37593 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125047 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125047 / 125000) = 1/(125000 / 125047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10808 : Bounds (375929 / 1000000000) (37593 / 100000000) (Real.log (125047 / 125000)) := by
  have h := reflection_log_10808_neg
  have he : Real.log (125047 / 125000) = -Real.log (125000 / 125047) := by
    rw [show ((125047 / 125000) : ℝ) = ((125000 / 125047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10809_neg : (37607 / 100000000) ≤ -Real.log (124953 / 125000) ∧
    -Real.log (124953 / 125000) ≤ (376071 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 249953)) (n := 12)
    (lo := (37607 / 100000000)) (hi := (376071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124953) = 1/(124953 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10809 : Bounds (-376071 / 1000000000) (-37607 / 100000000) (Real.log (124953 / 125000)) := by
  have h := reflection_log_10809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10810_neg : (2198343 / 12500000) ≤ -Real.log (25000 / 29807) ∧
    -Real.log (25000 / 29807) ≤ (175867441 / 1000000000) := by
  have h := checkLog_sound (w := (4807 / 54807)) (n := 12)
    (lo := (2198343 / 12500000)) (hi := (175867441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29807 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29807 / 25000) = 1/(25000 / 29807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10810 : Bounds (2198343 / 12500000) (175867441 / 1000000000) (Real.log (29807 / 25000)) := by
  have h := reflection_log_10810_neg
  have he : Real.log (29807 / 25000) = -Real.log (25000 / 29807) := by
    rw [show ((29807 / 25000) : ℝ) = ((25000 / 29807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10811_neg : (42707963 / 200000000) ≤ -Real.log (20193 / 25000) ∧
    -Real.log (20193 / 25000) ≤ (26692477 / 125000000) := by
  have h := checkLog_sound (w := (4807 / 45193)) (n := 12)
    (lo := (42707963 / 200000000)) (hi := (26692477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20193) = 1/(20193 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10811 : Bounds (-26692477 / 125000000) (-42707963 / 200000000) (Real.log (20193 / 25000)) := by
  have h := reflection_log_10811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10812_neg : (88313939 / 500000000) ≤ -Real.log (1000000 / 1193187) ∧
    -Real.log (1000000 / 1193187) ≤ (176627879 / 1000000000) := by
  have h := checkLog_sound (w := (193187 / 2193187)) (n := 12)
    (lo := (88313939 / 500000000)) (hi := (176627879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193187 / 1000000) = 1/(1000000 / 1193187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10812 : Bounds (88313939 / 500000000) (176627879 / 1000000000) (Real.log (1193187 / 1000000)) := by
  have h := reflection_log_10812_neg
  have he : Real.log (1193187 / 1000000) = -Real.log (1000000 / 1193187) := by
    rw [show ((1193187 / 1000000) : ℝ) = ((1000000 / 1193187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10813_neg : (214663359 / 1000000000) ≤ -Real.log (806813 / 1000000) ∧
    -Real.log (806813 / 1000000) ≤ (670823 / 3125000) := by
  have h := checkLog_sound (w := (193187 / 1806813)) (n := 12)
    (lo := (214663359 / 1000000000)) (hi := (670823 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806813) = 1/(806813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10813 : Bounds (-670823 / 3125000) (-214663359 / 1000000000) (Real.log (806813 / 1000000)) := by
  have h := reflection_log_10813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10814_neg : (38035481 / 1000000000) ≤ -Real.log (962678783031 / 1000000000000) ∧
    -Real.log (962678783031 / 1000000000000) ≤ (19017741 / 500000000) := by
  have h := checkLog_sound (w := (37321216969 / 1962678783031)) (n := 12)
    (lo := (38035481 / 1000000000)) (hi := (19017741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962678783031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962678783031) = 1/(962678783031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10814 : Bounds (-19017741 / 500000000) (-38035481 / 1000000000) (Real.log (962678783031 / 1000000000000)) := by
  have h := reflection_log_10814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10815_neg : (18836187 / 500000000) ≤ -Real.log (601892751 / 625000000) ∧
    -Real.log (601892751 / 625000000) ≤ (301379 / 8000000) := by
  have h := checkLog_sound (w := (23107249 / 1226892751)) (n := 12)
    (lo := (18836187 / 500000000)) (hi := (301379 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 601892751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 601892751) = 1/(601892751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10815 : Bounds (-301379 / 8000000) (-18836187 / 500000000) (Real.log (601892751 / 625000000)) := by
  have h := reflection_log_10815_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
