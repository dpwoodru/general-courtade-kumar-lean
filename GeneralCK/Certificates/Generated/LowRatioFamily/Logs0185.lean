import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11840_neg : (241723533 / 250000000) ≤ -Real.log (125000000000 / 328720508167) ∧
    -Real.log (125000000000 / 328720508167) ≤ (483447067 / 500000000) := by
  have h := checkLog_sound (w := (78720508167 / 578720508167)) (n := 12)
    (lo := (34218369 / 125000000)) (hi := (273746953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328720508167 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(328720508167 / 250000000000) = 1/(125000000000 / 328720508167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11840 : Bounds (241723533 / 250000000) (483447067 / 500000000) (Real.log (328720508167 / 125000000000)) := by
  have h := reflection_log_11840_neg
  have he : Real.log (328720508167 / 125000000000) = -Real.log (125000000000 / 328720508167) := by
    rw [show ((328720508167 / 125000000000) : ℝ) = ((125000000000 / 328720508167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11841_neg : (92890889 / 250000000) ≤ -Real.log (20 / 29) ∧
    -Real.log (20 / 29) ≤ (371563557 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 49)) (n := 12)
    (lo := (92890889 / 250000000)) (hi := (371563557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 20) = 1/(20 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11841 : Bounds (92890889 / 250000000) (371563557 / 1000000000) (Real.log (29 / 20)) := by
  have h := reflection_log_11841_neg
  have he : Real.log (29 / 20) = -Real.log (20 / 29) := by
    rw [show ((29 / 20) : ℝ) = ((20 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11842_neg : (597837 / 1000000) ≤ -Real.log (11 / 20) ∧
    -Real.log (11 / 20) ≤ (597837001 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 31)) (n := 12)
    (lo := (597837 / 1000000)) (hi := (597837001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 11) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 11) = 1/(11 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11842 : Bounds (-597837001 / 1000000000) (-597837 / 1000000) (Real.log (11 / 20)) := by
  have h := reflection_log_11842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11843_neg : (224949 / 500000000) ≤ -Real.log (20000 / 20009) ∧
    -Real.log (20000 / 20009) ≤ (449899 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 40009)) (n := 12)
    (lo := (224949 / 500000000)) (hi := (449899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20009 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20009 / 20000) = 1/(20000 / 20009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11843 : Bounds (224949 / 500000000) (449899 / 1000000000) (Real.log (20009 / 20000)) := by
  have h := reflection_log_11843_neg
  have he : Real.log (20009 / 20000) = -Real.log (20000 / 20009) := by
    rw [show ((20009 / 20000) : ℝ) = ((20000 / 20009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11844_neg : (450101 / 1000000000) ≤ -Real.log (19991 / 20000) ∧
    -Real.log (19991 / 20000) ≤ (225051 / 500000000) := by
  have h := checkLog_sound (w := (9 / 39991)) (n := 12)
    (lo := (450101 / 1000000000)) (hi := (225051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19991) = 1/(19991 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11844 : Bounds (-225051 / 500000000) (-450101 / 1000000000) (Real.log (19991 / 20000)) := by
  have h := reflection_log_11844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11845_neg : (209429137 / 1000000000) ≤ -Real.log (500000 / 616487) ∧
    -Real.log (500000 / 616487) ≤ (104714569 / 500000000) := by
  have h := checkLog_sound (w := (116487 / 1116487)) (n := 12)
    (lo := (209429137 / 1000000000)) (hi := (104714569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616487 / 500000) = 1/(500000 / 616487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11845 : Bounds (209429137 / 1000000000) (104714569 / 500000000) (Real.log (616487 / 500000)) := by
  have h := reflection_log_11845_neg
  have he : Real.log (616487 / 500000) = -Real.log (500000 / 616487) := by
    rw [show ((616487 / 500000) : ℝ) = ((500000 / 616487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11846_neg : (265234579 / 1000000000) ≤ -Real.log (383513 / 500000) ∧
    -Real.log (383513 / 500000) ≤ (13261729 / 50000000) := by
  have h := checkLog_sound (w := (116487 / 883513)) (n := 12)
    (lo := (265234579 / 1000000000)) (hi := (13261729 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383513) = 1/(383513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11846 : Bounds (-13261729 / 50000000) (-265234579 / 1000000000) (Real.log (383513 / 500000)) := by
  have h := reflection_log_11846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11847_neg : (52558343 / 250000000) ≤ -Real.log (500000 / 616983) ∧
    -Real.log (500000 / 616983) ≤ (210233373 / 1000000000) := by
  have h := checkLog_sound (w := (116983 / 1116983)) (n := 12)
    (lo := (52558343 / 250000000)) (hi := (210233373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616983 / 500000) = 1/(500000 / 616983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11847 : Bounds (52558343 / 250000000) (210233373 / 1000000000) (Real.log (616983 / 500000)) := by
  have h := reflection_log_11847_neg
  have he : Real.log (616983 / 500000) = -Real.log (500000 / 616983) := by
    rw [show ((616983 / 500000) : ℝ) = ((500000 / 616983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11848_neg : (266528723 / 1000000000) ≤ -Real.log (383017 / 500000) ∧
    -Real.log (383017 / 500000) ≤ (66632181 / 250000000) := by
  have h := checkLog_sound (w := (116983 / 883017)) (n := 12)
    (lo := (266528723 / 1000000000)) (hi := (66632181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383017) = 1/(383017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11848 : Bounds (-66632181 / 250000000) (-266528723 / 1000000000) (Real.log (383017 / 500000)) := by
  have h := reflection_log_11848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11849_neg : (56295351 / 1000000000) ≤ -Real.log (236314977711 / 250000000000) ∧
    -Real.log (236314977711 / 250000000000) ≤ (7036919 / 125000000) := by
  have h := checkLog_sound (w := (13685022289 / 486314977711)) (n := 12)
    (lo := (56295351 / 1000000000)) (hi := (7036919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236314977711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236314977711) = 1/(236314977711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11849 : Bounds (-7036919 / 125000000) (-56295351 / 1000000000) (Real.log (236314977711 / 250000000000)) := by
  have h := reflection_log_11849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11850_neg : (27902721 / 500000000) ≤ -Real.log (236430778831 / 250000000000) ∧
    -Real.log (236430778831 / 250000000000) ≤ (55805443 / 1000000000) := by
  have h := checkLog_sound (w := (13569221169 / 486430778831)) (n := 12)
    (lo := (27902721 / 500000000)) (hi := (55805443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236430778831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236430778831) = 1/(236430778831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11850 : Bounds (-55805443 / 1000000000) (-27902721 / 500000000) (Real.log (236430778831 / 250000000000)) := by
  have h := reflection_log_11850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11851_neg : (474663717 / 1000000000) ≤ -Real.log (500000000000 / 803736770331) ∧
    -Real.log (500000000000 / 803736770331) ≤ (237331859 / 500000000) := by
  have h := checkLog_sound (w := (303736770331 / 1303736770331)) (n := 12)
    (lo := (474663717 / 1000000000)) (hi := (237331859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803736770331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803736770331 / 500000000000) = 1/(500000000000 / 803736770331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11851 : Bounds (474663717 / 1000000000) (237331859 / 500000000) (Real.log (803736770331 / 500000000000)) := by
  have h := reflection_log_11851_neg
  have he : Real.log (803736770331 / 500000000000) = -Real.log (500000000000 / 803736770331) := by
    rw [show ((803736770331 / 500000000000) : ℝ) = ((500000000000 / 803736770331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11852_neg : (29797631 / 62500000) ≤ -Real.log (500000000000 / 805425085571) ∧
    -Real.log (500000000000 / 805425085571) ≤ (476762097 / 1000000000) := by
  have h := checkLog_sound (w := (305425085571 / 1305425085571)) (n := 12)
    (lo := (29797631 / 62500000)) (hi := (476762097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805425085571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805425085571 / 500000000000) = 1/(500000000000 / 805425085571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11852 : Bounds (29797631 / 62500000) (476762097 / 1000000000) (Real.log (805425085571 / 500000000000)) := by
  have h := reflection_log_11852_neg
  have he : Real.log (805425085571 / 500000000000) = -Real.log (500000000000 / 805425085571) := by
    rw [show ((805425085571 / 500000000000) : ℝ) = ((500000000000 / 805425085571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11853_neg : (241723533 / 250000000) ≤ -Real.log (500000000000 / 1314882032667) ∧
    -Real.log (500000000000 / 1314882032667) ≤ (483447067 / 500000000) := by
  have h := checkLog_sound (w := (314882032667 / 2314882032667)) (n := 12)
    (lo := (34218369 / 125000000)) (hi := (273746953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314882032667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1314882032667 / 1000000000000) = 1/(500000000000 / 1314882032667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11853 : Bounds (241723533 / 250000000) (483447067 / 500000000) (Real.log (1314882032667 / 500000000000)) := by
  have h := reflection_log_11853_neg
  have he : Real.log (1314882032667 / 500000000000) = -Real.log (500000000000 / 1314882032667) := by
    rw [show ((1314882032667 / 500000000000) : ℝ) = ((500000000000 / 1314882032667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11854_neg : (242350139 / 250000000) ≤ -Real.log (250000000000 / 659090909091) ∧
    -Real.log (250000000000 / 659090909091) ≤ (484700279 / 500000000) := by
  have h := checkLog_sound (w := (159090909091 / 1159090909091)) (n := 12)
    (lo := (4316459 / 15625000)) (hi := (276253377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659090909091 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(659090909091 / 500000000000) = 1/(250000000000 / 659090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11854 : Bounds (242350139 / 250000000) (484700279 / 500000000) (Real.log (659090909091 / 250000000000)) := by
  have h := reflection_log_11854_neg
  have he : Real.log (659090909091 / 250000000000) = -Real.log (250000000000 / 659090909091) := by
    rw [show ((659090909091 / 250000000000) : ℝ) = ((250000000000 / 659090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11855_neg : (372252973 / 1000000000) ≤ -Real.log (1000 / 1451) ∧
    -Real.log (1000 / 1451) ≤ (186126487 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2451)) (n := 12)
    (lo := (372252973 / 1000000000)) (hi := (186126487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1000) = 1/(1000 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11855 : Bounds (372252973 / 1000000000) (186126487 / 500000000) (Real.log (1451 / 1000)) := by
  have h := reflection_log_11855_neg
  have he : Real.log (1451 / 1000) = -Real.log (1000 / 1451) := by
    rw [show ((1451 / 1000) : ℝ) = ((1000 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11856_neg : (599656837 / 1000000000) ≤ -Real.log (549 / 1000) ∧
    -Real.log (549 / 1000) ≤ (299828419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1549)) (n := 12)
    (lo := (599656837 / 1000000000)) (hi := (299828419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 549) = 1/(549 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11856 : Bounds (-299828419 / 500000000) (-599656837 / 1000000000) (Real.log (549 / 1000)) := by
  have h := reflection_log_11856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11857_neg : (225449 / 500000000) ≤ -Real.log (1000000 / 1000451) ∧
    -Real.log (1000000 / 1000451) ≤ (450899 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2000451)) (n := 12)
    (lo := (225449 / 500000000)) (hi := (450899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000451 / 1000000) = 1/(1000000 / 1000451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11857 : Bounds (225449 / 500000000) (450899 / 1000000000) (Real.log (1000451 / 1000000)) := by
  have h := reflection_log_11857_neg
  have he : Real.log (1000451 / 1000000) = -Real.log (1000000 / 1000451) := by
    rw [show ((1000451 / 1000000) : ℝ) = ((1000000 / 1000451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11858_neg : (451101 / 1000000000) ≤ -Real.log (999549 / 1000000) ∧
    -Real.log (999549 / 1000000) ≤ (225551 / 500000000) := by
  have h := checkLog_sound (w := (451 / 1999549)) (n := 12)
    (lo := (451101 / 1000000000)) (hi := (225551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999549) = 1/(999549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11858 : Bounds (-225551 / 500000000) (-451101 / 1000000000) (Real.log (999549 / 1000000)) := by
  have h := reflection_log_11858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11859_neg : (10494161 / 50000000) ≤ -Real.log (500000 / 616767) ∧
    -Real.log (500000 / 616767) ≤ (209883221 / 1000000000) := by
  have h := checkLog_sound (w := (116767 / 1116767)) (n := 12)
    (lo := (10494161 / 50000000)) (hi := (209883221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616767 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616767 / 500000) = 1/(500000 / 616767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11859 : Bounds (10494161 / 50000000) (209883221 / 1000000000) (Real.log (616767 / 500000)) := by
  have h := reflection_log_11859_neg
  have he : Real.log (616767 / 500000) = -Real.log (500000 / 616767) := by
    rw [show ((616767 / 500000) : ℝ) = ((500000 / 616767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11860_neg : (265964939 / 1000000000) ≤ -Real.log (383233 / 500000) ∧
    -Real.log (383233 / 500000) ≤ (13298247 / 50000000) := by
  have h := checkLog_sound (w := (116767 / 883233)) (n := 12)
    (lo := (265964939 / 1000000000)) (hi := (13298247 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383233) = 1/(383233 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11860 : Bounds (-13298247 / 50000000) (-265964939 / 1000000000) (Real.log (383233 / 500000)) := by
  have h := reflection_log_11860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11861_neg : (21068871 / 100000000) ≤ -Real.log (31250 / 38579) ∧
    -Real.log (31250 / 38579) ≤ (210688711 / 1000000000) := by
  have h := checkLog_sound (w := (7329 / 69829)) (n := 12)
    (lo := (21068871 / 100000000)) (hi := (210688711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38579 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38579 / 31250) = 1/(31250 / 38579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11861 : Bounds (21068871 / 100000000) (210688711 / 1000000000) (Real.log (38579 / 31250)) := by
  have h := reflection_log_11861_neg
  have he : Real.log (38579 / 31250) = -Real.log (31250 / 38579) := by
    rw [show ((38579 / 31250) : ℝ) = ((31250 / 38579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11862_neg : (267262641 / 1000000000) ≤ -Real.log (23921 / 31250) ∧
    -Real.log (23921 / 31250) ≤ (133631321 / 500000000) := by
  have h := checkLog_sound (w := (7329 / 55171)) (n := 12)
    (lo := (267262641 / 1000000000)) (hi := (133631321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23921) = 1/(23921 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11862 : Bounds (-133631321 / 500000000) (-267262641 / 1000000000) (Real.log (23921 / 31250)) := by
  have h := reflection_log_11862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11863_neg : (56573931 / 1000000000) ≤ -Real.log (922848259 / 976562500) ∧
    -Real.log (922848259 / 976562500) ≤ (14143483 / 250000000) := by
  have h := checkLog_sound (w := (53714241 / 1899410759)) (n := 12)
    (lo := (56573931 / 1000000000)) (hi := (14143483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 922848259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 922848259) = 1/(922848259 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11863 : Bounds (-14143483 / 250000000) (-56573931 / 1000000000) (Real.log (922848259 / 976562500)) := by
  have h := reflection_log_11863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11864_neg : (28040859 / 500000000) ≤ -Real.log (236365467711 / 250000000000) ∧
    -Real.log (236365467711 / 250000000000) ≤ (56081719 / 1000000000) := by
  have h := checkLog_sound (w := (13634532289 / 486365467711)) (n := 12)
    (lo := (28040859 / 500000000)) (hi := (56081719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236365467711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236365467711) = 1/(236365467711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11864 : Bounds (-56081719 / 1000000000) (-28040859 / 500000000) (Real.log (236365467711 / 250000000000)) := by
  have h := reflection_log_11864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11865_neg : (475848159 / 1000000000) ≤ -Real.log (500000000000 / 804689314333) ∧
    -Real.log (500000000000 / 804689314333) ≤ (2974051 / 6250000) := by
  have h := checkLog_sound (w := (304689314333 / 1304689314333)) (n := 12)
    (lo := (475848159 / 1000000000)) (hi := (2974051 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804689314333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804689314333 / 500000000000) = 1/(500000000000 / 804689314333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11865 : Bounds (475848159 / 1000000000) (2974051 / 6250000) (Real.log (804689314333 / 500000000000)) := by
  have h := reflection_log_11865_neg
  have he : Real.log (804689314333 / 500000000000) = -Real.log (500000000000 / 804689314333) := by
    rw [show ((804689314333 / 500000000000) : ℝ) = ((500000000000 / 804689314333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11866_neg : (59743919 / 125000000) ≤ -Real.log (100000000000 / 161276702479) ∧
    -Real.log (100000000000 / 161276702479) ≤ (477951353 / 1000000000) := by
  have h := checkLog_sound (w := (61276702479 / 261276702479)) (n := 12)
    (lo := (59743919 / 125000000)) (hi := (477951353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161276702479 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161276702479 / 100000000000) = 1/(100000000000 / 161276702479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11866 : Bounds (59743919 / 125000000) (477951353 / 1000000000) (Real.log (161276702479 / 100000000000)) := by
  have h := reflection_log_11866_neg
  have he : Real.log (161276702479 / 100000000000) = -Real.log (100000000000 / 161276702479) := by
    rw [show ((161276702479 / 100000000000) : ℝ) = ((100000000000 / 161276702479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11867_neg : (242350139 / 250000000) ≤ -Real.log (500000000000 / 1318181818181) ∧
    -Real.log (500000000000 / 1318181818181) ≤ (484700279 / 500000000) := by
  have h := checkLog_sound (w := (318181818181 / 2318181818181)) (n := 12)
    (lo := (4316459 / 15625000)) (hi := (276253377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318181818181 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1318181818181 / 1000000000000) = 1/(500000000000 / 1318181818181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11867 : Bounds (242350139 / 250000000) (484700279 / 500000000) (Real.log (1318181818181 / 500000000000)) := by
  have h := reflection_log_11867_neg
  have he : Real.log (1318181818181 / 500000000000) = -Real.log (500000000000 / 1318181818181) := by
    rw [show ((1318181818181 / 500000000000) : ℝ) = ((500000000000 / 1318181818181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11868_neg : (97190981 / 100000000) ≤ -Real.log (500000000000 / 1321493624773) ∧
    -Real.log (500000000000 / 1321493624773) ≤ (242977453 / 250000000) := by
  have h := checkLog_sound (w := (321493624773 / 2321493624773)) (n := 12)
    (lo := (27876263 / 100000000)) (hi := (278762631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321493624773 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1321493624773 / 1000000000000) = 1/(500000000000 / 1321493624773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11868 : Bounds (97190981 / 100000000) (242977453 / 250000000) (Real.log (1321493624773 / 500000000000)) := by
  have h := reflection_log_11868_neg
  have he : Real.log (1321493624773 / 500000000000) = -Real.log (500000000000 / 1321493624773) := by
    rw [show ((1321493624773 / 500000000000) : ℝ) = ((500000000000 / 1321493624773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11869_neg : (93235479 / 250000000) ≤ -Real.log (250 / 363) ∧
    -Real.log (250 / 363) ≤ (372941917 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 613)) (n := 12)
    (lo := (93235479 / 250000000)) (hi := (372941917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 250) = 1/(250 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11869 : Bounds (93235479 / 250000000) (372941917 / 1000000000) (Real.log (363 / 250)) := by
  have h := reflection_log_11869_neg
  have he : Real.log (363 / 250) = -Real.log (250 / 363) := by
    rw [show ((363 / 250) : ℝ) = ((250 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11870_neg : (75184999 / 125000000) ≤ -Real.log (137 / 250) ∧
    -Real.log (137 / 250) ≤ (601479993 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 387)) (n := 12)
    (lo := (75184999 / 125000000)) (hi := (601479993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 137) = 1/(137 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11870 : Bounds (-601479993 / 1000000000) (-75184999 / 125000000) (Real.log (137 / 250)) := by
  have h := reflection_log_11870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11871_neg : (451897 / 1000000000) ≤ -Real.log (250000 / 250113) ∧
    -Real.log (250000 / 250113) ≤ (225949 / 500000000) := by
  have h := checkLog_sound (w := (113 / 500113)) (n := 12)
    (lo := (451897 / 1000000000)) (hi := (225949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250113 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250113 / 250000) = 1/(250000 / 250113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11871 : Bounds (451897 / 1000000000) (225949 / 500000000) (Real.log (250113 / 250000)) := by
  have h := reflection_log_11871_neg
  have he : Real.log (250113 / 250000) = -Real.log (250000 / 250113) := by
    rw [show ((250113 / 250000) : ℝ) = ((250000 / 250113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11872_neg : (226051 / 500000000) ≤ -Real.log (249887 / 250000) ∧
    -Real.log (249887 / 250000) ≤ (452103 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 499887)) (n := 12)
    (lo := (226051 / 500000000)) (hi := (452103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249887) = 1/(249887 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11872 : Bounds (-452103 / 1000000000) (-226051 / 500000000) (Real.log (249887 / 250000)) := by
  have h := reflection_log_11872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11873_neg : (210337907 / 1000000000) ≤ -Real.log (200000 / 246819) ∧
    -Real.log (200000 / 246819) ≤ (52584477 / 250000000) := by
  have h := checkLog_sound (w := (46819 / 446819)) (n := 12)
    (lo := (210337907 / 1000000000)) (hi := (52584477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246819 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246819 / 200000) = 1/(200000 / 246819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11873 : Bounds (210337907 / 1000000000) (52584477 / 250000000) (Real.log (246819 / 200000)) := by
  have h := reflection_log_11873_neg
  have he : Real.log (246819 / 200000) = -Real.log (200000 / 246819) := by
    rw [show ((246819 / 200000) : ℝ) = ((200000 / 246819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11874_neg : (266697137 / 1000000000) ≤ -Real.log (153181 / 200000) ∧
    -Real.log (153181 / 200000) ≤ (133348569 / 500000000) := by
  have h := checkLog_sound (w := (46819 / 353181)) (n := 12)
    (lo := (266697137 / 1000000000)) (hi := (133348569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153181) = 1/(153181 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11874 : Bounds (-133348569 / 500000000) (-266697137 / 1000000000) (Real.log (153181 / 200000)) := by
  have h := reflection_log_11874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11875_neg : (211143841 / 1000000000) ≤ -Real.log (100000 / 123509) ∧
    -Real.log (100000 / 123509) ≤ (105571921 / 500000000) := by
  have h := checkLog_sound (w := (23509 / 223509)) (n := 12)
    (lo := (211143841 / 1000000000)) (hi := (105571921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123509 / 100000) = 1/(100000 / 123509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11875 : Bounds (211143841 / 1000000000) (105571921 / 500000000) (Real.log (123509 / 100000)) := by
  have h := reflection_log_11875_neg
  have he : Real.log (123509 / 100000) = -Real.log (100000 / 123509) := by
    rw [show ((123509 / 100000) : ℝ) = ((100000 / 123509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11876_neg : (267997099 / 1000000000) ≤ -Real.log (76491 / 100000) ∧
    -Real.log (76491 / 100000) ≤ (2679971 / 10000000) := by
  have h := checkLog_sound (w := (23509 / 176491)) (n := 12)
    (lo := (267997099 / 1000000000)) (hi := (2679971 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76491) = 1/(76491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11876 : Bounds (-2679971 / 10000000) (-267997099 / 1000000000) (Real.log (76491 / 100000)) := by
  have h := reflection_log_11876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11877_neg : (56853257 / 1000000000) ≤ -Real.log (9447326919 / 10000000000) ∧
    -Real.log (9447326919 / 10000000000) ≤ (28426629 / 500000000) := by
  have h := checkLog_sound (w := (552673081 / 19447326919)) (n := 12)
    (lo := (56853257 / 1000000000)) (hi := (28426629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9447326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9447326919) = 1/(9447326919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11877 : Bounds (-28426629 / 500000000) (-56853257 / 1000000000) (Real.log (9447326919 / 10000000000)) := by
  have h := reflection_log_11877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11878_neg : (56359229 / 1000000000) ≤ -Real.log (37807981239 / 40000000000) ∧
    -Real.log (37807981239 / 40000000000) ≤ (5635923 / 100000000) := by
  have h := checkLog_sound (w := (2192018761 / 77807981239)) (n := 12)
    (lo := (56359229 / 1000000000)) (hi := (5635923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37807981239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37807981239) = 1/(37807981239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11878 : Bounds (-5635923 / 100000000) (-56359229 / 1000000000) (Real.log (37807981239 / 40000000000)) := by
  have h := reflection_log_11878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11879_neg : (95407009 / 200000000) ≤ -Real.log (500000000000 / 805644955967) ∧
    -Real.log (500000000000 / 805644955967) ≤ (238517523 / 500000000) := by
  have h := checkLog_sound (w := (305644955967 / 1305644955967)) (n := 12)
    (lo := (95407009 / 200000000)) (hi := (238517523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805644955967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805644955967 / 500000000000) = 1/(500000000000 / 805644955967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11879 : Bounds (95407009 / 200000000) (238517523 / 500000000) (Real.log (805644955967 / 500000000000)) := by
  have h := reflection_log_11879_neg
  have he : Real.log (805644955967 / 500000000000) = -Real.log (500000000000 / 805644955967) := by
    rw [show ((805644955967 / 500000000000) : ℝ) = ((500000000000 / 805644955967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11880_neg : (479140941 / 1000000000) ≤ -Real.log (3906250000 / 6307369903) ∧
    -Real.log (3906250000 / 6307369903) ≤ (239570471 / 500000000) := by
  have h := checkLog_sound (w := (2401119903 / 10213619903)) (n := 12)
    (lo := (479140941 / 1000000000)) (hi := (239570471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6307369903 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6307369903 / 3906250000) = 1/(3906250000 / 6307369903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11880 : Bounds (479140941 / 1000000000) (239570471 / 500000000) (Real.log (6307369903 / 3906250000)) := by
  have h := reflection_log_11880_neg
  have he : Real.log (6307369903 / 3906250000) = -Real.log (3906250000 / 6307369903) := by
    rw [show ((6307369903 / 3906250000) : ℝ) = ((3906250000 / 6307369903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11881_neg : (97190981 / 100000000) ≤ -Real.log (125000000000 / 330373406193) ∧
    -Real.log (125000000000 / 330373406193) ≤ (242977453 / 250000000) := by
  have h := checkLog_sound (w := (80373406193 / 580373406193)) (n := 12)
    (lo := (27876263 / 100000000)) (hi := (278762631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330373406193 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330373406193 / 250000000000) = 1/(125000000000 / 330373406193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11881 : Bounds (97190981 / 100000000) (242977453 / 250000000) (Real.log (330373406193 / 125000000000)) := by
  have h := reflection_log_11881_neg
  have he : Real.log (330373406193 / 125000000000) = -Real.log (125000000000 / 330373406193) := by
    rw [show ((330373406193 / 125000000000) : ℝ) = ((125000000000 / 330373406193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11882_neg : (974421907 / 1000000000) ≤ -Real.log (500000000000 / 1324817518249) ∧
    -Real.log (500000000000 / 1324817518249) ≤ (974421909 / 1000000000) := by
  have h := checkLog_sound (w := (324817518249 / 2324817518249)) (n := 12)
    (lo := (281274727 / 1000000000)) (hi := (35159341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1324817518249 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1324817518249 / 1000000000000) = 1/(500000000000 / 1324817518249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11882 : Bounds (974421907 / 1000000000) (974421909 / 1000000000) (Real.log (1324817518249 / 500000000000)) := by
  have h := reflection_log_11882_neg
  have he : Real.log (1324817518249 / 500000000000) = -Real.log (500000000000 / 1324817518249) := by
    rw [show ((1324817518249 / 500000000000) : ℝ) = ((500000000000 / 1324817518249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11883_neg : (23351899 / 62500000) ≤ -Real.log (1000 / 1453) ∧
    -Real.log (1000 / 1453) ≤ (74726077 / 200000000) := by
  have h := checkLog_sound (w := (453 / 2453)) (n := 12)
    (lo := (23351899 / 62500000)) (hi := (74726077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453 / 1000) = 1/(1000 / 1453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11883 : Bounds (23351899 / 62500000) (74726077 / 200000000) (Real.log (1453 / 1000)) := by
  have h := reflection_log_11883_neg
  have he : Real.log (1453 / 1000) = -Real.log (1000 / 1453) := by
    rw [show ((1453 / 1000) : ℝ) = ((1000 / 1453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11884_neg : (150826619 / 250000000) ≤ -Real.log (547 / 1000) ∧
    -Real.log (547 / 1000) ≤ (603306477 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 1547)) (n := 12)
    (lo := (150826619 / 250000000)) (hi := (603306477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 547) = 1/(547 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11884 : Bounds (-603306477 / 1000000000) (-150826619 / 250000000) (Real.log (547 / 1000)) := by
  have h := reflection_log_11884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11885_neg : (452897 / 1000000000) ≤ -Real.log (1000000 / 1000453) ∧
    -Real.log (1000000 / 1000453) ≤ (226449 / 500000000) := by
  have h := checkLog_sound (w := (453 / 2000453)) (n := 12)
    (lo := (452897 / 1000000000)) (hi := (226449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000453 / 1000000) = 1/(1000000 / 1000453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11885 : Bounds (452897 / 1000000000) (226449 / 500000000) (Real.log (1000453 / 1000000)) := by
  have h := reflection_log_11885_neg
  have he : Real.log (1000453 / 1000000) = -Real.log (1000000 / 1000453) := by
    rw [show ((1000453 / 1000000) : ℝ) = ((1000000 / 1000453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11886_neg : (226551 / 500000000) ≤ -Real.log (999547 / 1000000) ∧
    -Real.log (999547 / 1000000) ≤ (453103 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 1999547)) (n := 12)
    (lo := (226551 / 500000000)) (hi := (453103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999547) = 1/(999547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11886 : Bounds (-453103 / 1000000000) (-226551 / 500000000) (Real.log (999547 / 1000000)) := by
  have h := reflection_log_11886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11887_neg : (52698097 / 250000000) ≤ -Real.log (31250 / 38583) ∧
    -Real.log (31250 / 38583) ≤ (210792389 / 1000000000) := by
  have h := checkLog_sound (w := (7333 / 69833)) (n := 12)
    (lo := (52698097 / 250000000)) (hi := (210792389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38583 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38583 / 31250) = 1/(31250 / 38583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11887 : Bounds (52698097 / 250000000) (210792389 / 1000000000) (Real.log (38583 / 31250)) := by
  have h := reflection_log_11887_neg
  have he : Real.log (38583 / 31250) = -Real.log (31250 / 38583) := by
    rw [show ((38583 / 31250) : ℝ) = ((31250 / 38583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11888_neg : (267429873 / 1000000000) ≤ -Real.log (23917 / 31250) ∧
    -Real.log (23917 / 31250) ≤ (133714937 / 500000000) := by
  have h := checkLog_sound (w := (7333 / 55167)) (n := 12)
    (lo := (267429873 / 1000000000)) (hi := (133714937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23917) = 1/(23917 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11888 : Bounds (-133714937 / 500000000) (-267429873 / 1000000000) (Real.log (23917 / 31250)) := by
  have h := reflection_log_11888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11889_neg : (42319753 / 200000000) ≤ -Real.log (250000 / 308913) ∧
    -Real.log (250000 / 308913) ≤ (105799383 / 500000000) := by
  have h := checkLog_sound (w := (58913 / 558913)) (n := 12)
    (lo := (42319753 / 200000000)) (hi := (105799383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308913 / 250000) = 1/(250000 / 308913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11889 : Bounds (42319753 / 200000000) (105799383 / 500000000) (Real.log (308913 / 250000)) := by
  have h := reflection_log_11889_neg
  have he : Real.log (308913 / 250000) = -Real.log (250000 / 308913) := by
    rw [show ((308913 / 250000) : ℝ) = ((250000 / 308913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11890_neg : (4198939 / 15625000) ≤ -Real.log (191087 / 250000) ∧
    -Real.log (191087 / 250000) ≤ (268732097 / 1000000000) := by
  have h := checkLog_sound (w := (58913 / 441087)) (n := 12)
    (lo := (4198939 / 15625000)) (hi := (268732097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191087) = 1/(191087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11890 : Bounds (-268732097 / 1000000000) (-4198939 / 15625000) (Real.log (191087 / 250000)) := by
  have h := reflection_log_11890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11891_neg : (5713333 / 100000000) ≤ -Real.log (59029258431 / 62500000000) ∧
    -Real.log (59029258431 / 62500000000) ≤ (57133331 / 1000000000) := by
  have h := checkLog_sound (w := (3470741569 / 121529258431)) (n := 12)
    (lo := (5713333 / 100000000)) (hi := (57133331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59029258431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59029258431) = 1/(59029258431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11891 : Bounds (-57133331 / 1000000000) (-5713333 / 100000000) (Real.log (59029258431 / 62500000000)) := by
  have h := reflection_log_11891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11892_neg : (14159371 / 250000000) ≤ -Real.log (922789611 / 976562500) ∧
    -Real.log (922789611 / 976562500) ≤ (11327497 / 200000000) := by
  have h := checkLog_sound (w := (53772889 / 1899352111)) (n := 12)
    (lo := (14159371 / 250000000)) (hi := (11327497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 922789611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 922789611) = 1/(922789611 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11892 : Bounds (-11327497 / 200000000) (-14159371 / 250000000) (Real.log (922789611 / 976562500)) := by
  have h := reflection_log_11892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11893_neg : (478222261 / 1000000000) ≤ -Real.log (250000000000 / 403300999289) ∧
    -Real.log (250000000000 / 403300999289) ≤ (239111131 / 500000000) := by
  have h := checkLog_sound (w := (153300999289 / 653300999289)) (n := 12)
    (lo := (478222261 / 1000000000)) (hi := (239111131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403300999289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403300999289 / 250000000000) = 1/(250000000000 / 403300999289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11893 : Bounds (478222261 / 1000000000) (239111131 / 500000000) (Real.log (403300999289 / 250000000000)) := by
  have h := reflection_log_11893_neg
  have he : Real.log (403300999289 / 250000000000) = -Real.log (250000000000 / 403300999289) := by
    rw [show ((403300999289 / 250000000000) : ℝ) = ((250000000000 / 403300999289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11894_neg : (240165431 / 500000000) ≤ -Real.log (500000000000 / 808304594243) ∧
    -Real.log (500000000000 / 808304594243) ≤ (480330863 / 1000000000) := by
  have h := checkLog_sound (w := (308304594243 / 1308304594243)) (n := 12)
    (lo := (240165431 / 500000000)) (hi := (480330863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808304594243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808304594243 / 500000000000) = 1/(500000000000 / 808304594243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11894 : Bounds (240165431 / 500000000) (480330863 / 1000000000) (Real.log (808304594243 / 500000000000)) := by
  have h := reflection_log_11894_neg
  have he : Real.log (808304594243 / 500000000000) = -Real.log (500000000000 / 808304594243) := by
    rw [show ((808304594243 / 500000000000) : ℝ) = ((500000000000 / 808304594243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11895_neg : (974421907 / 1000000000) ≤ -Real.log (62500000000 / 165602189781) ∧
    -Real.log (62500000000 / 165602189781) ≤ (974421909 / 1000000000) := by
  have h := checkLog_sound (w := (40602189781 / 290602189781)) (n := 12)
    (lo := (281274727 / 1000000000)) (hi := (35159341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165602189781 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(165602189781 / 125000000000) = 1/(62500000000 / 165602189781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11895 : Bounds (974421907 / 1000000000) (974421909 / 1000000000) (Real.log (165602189781 / 62500000000)) := by
  have h := reflection_log_11895_neg
  have he : Real.log (165602189781 / 62500000000) = -Real.log (62500000000 / 165602189781) := by
    rw [show ((165602189781 / 62500000000) : ℝ) = ((62500000000 / 165602189781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11896_neg : (48846843 / 50000000) ≤ -Real.log (5000000000 / 13281535649) ∧
    -Real.log (5000000000 / 13281535649) ≤ (488468431 / 500000000) := by
  have h := checkLog_sound (w := (3281535649 / 23281535649)) (n := 12)
    (lo := (3547371 / 12500000)) (hi := (283789681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13281535649 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13281535649 / 10000000000) = 1/(5000000000 / 13281535649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11896 : Bounds (48846843 / 50000000) (488468431 / 500000000) (Real.log (13281535649 / 5000000000)) := by
  have h := reflection_log_11896_neg
  have he : Real.log (13281535649 / 5000000000) = -Real.log (5000000000 / 13281535649) := by
    rw [show ((13281535649 / 5000000000) : ℝ) = ((5000000000 / 13281535649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11897_neg : (374318379 / 1000000000) ≤ -Real.log (500 / 727) ∧
    -Real.log (500 / 727) ≤ (18715919 / 50000000) := by
  have h := checkLog_sound (w := (227 / 1227)) (n := 12)
    (lo := (374318379 / 1000000000)) (hi := (18715919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 500) = 1/(500 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11897 : Bounds (374318379 / 1000000000) (18715919 / 50000000) (Real.log (727 / 500)) := by
  have h := reflection_log_11897_neg
  have he : Real.log (727 / 500) = -Real.log (500 / 727) := by
    rw [show ((727 / 500) : ℝ) = ((500 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11898_neg : (605136303 / 1000000000) ≤ -Real.log (273 / 500) ∧
    -Real.log (273 / 500) ≤ (37821019 / 62500000) := by
  have h := checkLog_sound (w := (227 / 773)) (n := 12)
    (lo := (605136303 / 1000000000)) (hi := (37821019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 273) = 1/(273 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11898 : Bounds (-37821019 / 62500000) (-605136303 / 1000000000) (Real.log (273 / 500)) := by
  have h := reflection_log_11898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11899_neg : (56737 / 125000000) ≤ -Real.log (500000 / 500227) ∧
    -Real.log (500000 / 500227) ≤ (453897 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1000227)) (n := 12)
    (lo := (56737 / 125000000)) (hi := (453897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500227 / 500000) = 1/(500000 / 500227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11899 : Bounds (56737 / 125000000) (453897 / 1000000000) (Real.log (500227 / 500000)) := by
  have h := reflection_log_11899_neg
  have he : Real.log (500227 / 500000) = -Real.log (500000 / 500227) := by
    rw [show ((500227 / 500000) : ℝ) = ((500000 / 500227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11900_neg : (454103 / 1000000000) ≤ -Real.log (499773 / 500000) ∧
    -Real.log (499773 / 500000) ≤ (56763 / 125000000) := by
  have h := checkLog_sound (w := (227 / 999773)) (n := 12)
    (lo := (454103 / 1000000000)) (hi := (56763 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499773) = 1/(499773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11900 : Bounds (-56763 / 125000000) (-454103 / 1000000000) (Real.log (499773 / 500000)) := by
  have h := reflection_log_11900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11901_neg : (211246663 / 1000000000) ≤ -Real.log (1000000 / 1235217) ∧
    -Real.log (1000000 / 1235217) ≤ (26405833 / 125000000) := by
  have h := checkLog_sound (w := (235217 / 2235217)) (n := 12)
    (lo := (211246663 / 1000000000)) (hi := (26405833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1235217 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1235217 / 1000000) = 1/(1000000 / 1235217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11901 : Bounds (211246663 / 1000000000) (26405833 / 125000000) (Real.log (1235217 / 1000000)) := by
  have h := reflection_log_11901_neg
  have he : Real.log (1235217 / 1000000) = -Real.log (1000000 / 1235217) := by
    rw [show ((1235217 / 1000000) : ℝ) = ((1000000 / 1235217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11902_neg : (53632629 / 200000000) ≤ -Real.log (764783 / 1000000) ∧
    -Real.log (764783 / 1000000) ≤ (134081573 / 500000000) := by
  have h := checkLog_sound (w := (235217 / 1764783)) (n := 12)
    (lo := (53632629 / 200000000)) (hi := (134081573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 764783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 764783) = 1/(764783 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11902 : Bounds (-134081573 / 500000000) (-53632629 / 200000000) (Real.log (764783 / 1000000)) := by
  have h := reflection_log_11902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11903_neg : (212053483 / 1000000000) ≤ -Real.log (500000 / 618107) ∧
    -Real.log (500000 / 618107) ≤ (53013371 / 250000000) := by
  have h := checkLog_sound (w := (118107 / 1118107)) (n := 12)
    (lo := (212053483 / 1000000000)) (hi := (53013371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618107 / 500000) = 1/(500000 / 618107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11903 : Bounds (212053483 / 1000000000) (53013371 / 250000000) (Real.log (618107 / 500000)) := by
  have h := reflection_log_11903_neg
  have he : Real.log (618107 / 500000) = -Real.log (500000 / 618107) := by
    rw [show ((618107 / 500000) : ℝ) = ((500000 / 618107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
