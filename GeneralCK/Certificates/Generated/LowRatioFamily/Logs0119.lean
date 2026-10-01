import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7616_neg : (55881 / 250000000) ≤ -Real.log (1999553 / 2000000) ∧
    -Real.log (1999553 / 2000000) ≤ (8941 / 40000000) := by
  have h := checkLog_sound (w := (447 / 3999553)) (n := 12)
    (lo := (55881 / 250000000)) (hi := (8941 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999553) = 1/(1999553 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7616 : Bounds (-8941 / 40000000) (-55881 / 250000000) (Real.log (1999553 / 2000000)) := by
  have h := reflection_log_7616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7617_neg : (106523439 / 1000000000) ≤ -Real.log (250000 / 278101) ∧
    -Real.log (250000 / 278101) ≤ (1331543 / 12500000) := by
  have h := checkLog_sound (w := (28101 / 528101)) (n := 12)
    (lo := (106523439 / 1000000000)) (hi := (1331543 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278101 / 250000) = 1/(250000 / 278101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7617 : Bounds (106523439 / 1000000000) (1331543 / 12500000) (Real.log (278101 / 250000)) := by
  have h := reflection_log_7617_neg
  have he : Real.log (278101 / 250000) = -Real.log (250000 / 278101) := by
    rw [show ((278101 / 250000) : ℝ) = ((250000 / 278101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7618_neg : (59619297 / 500000000) ≤ -Real.log (221899 / 250000) ∧
    -Real.log (221899 / 250000) ≤ (23847719 / 200000000) := by
  have h := checkLog_sound (w := (28101 / 471899)) (n := 12)
    (lo := (59619297 / 500000000)) (hi := (23847719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221899) = 1/(221899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7618 : Bounds (-23847719 / 200000000) (-59619297 / 500000000) (Real.log (221899 / 250000)) := by
  have h := reflection_log_7618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7619_neg : (21390789 / 200000000) ≤ -Real.log (1000000 / 1112883) ∧
    -Real.log (1000000 / 1112883) ≤ (53476973 / 500000000) := by
  have h := checkLog_sound (w := (112883 / 2112883)) (n := 12)
    (lo := (21390789 / 200000000)) (hi := (53476973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112883 / 1000000) = 1/(1000000 / 1112883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7619 : Bounds (21390789 / 200000000) (53476973 / 500000000) (Real.log (1112883 / 1000000)) := by
  have h := reflection_log_7619_neg
  have he : Real.log (1112883 / 1000000) = -Real.log (1000000 / 1112883) := by
    rw [show ((1112883 / 1000000) : ℝ) = ((1000000 / 1112883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7620_neg : (149723 / 1250000) ≤ -Real.log (887117 / 1000000) ∧
    -Real.log (887117 / 1000000) ≤ (119778401 / 1000000000) := by
  have h := checkLog_sound (w := (112883 / 1887117)) (n := 12)
    (lo := (149723 / 1250000)) (hi := (119778401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887117) = 1/(887117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7620 : Bounds (-119778401 / 1000000000) (-149723 / 1250000) (Real.log (887117 / 1000000)) := by
  have h := reflection_log_7620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7621_neg : (6412227 / 500000000) ≤ -Real.log (987257428311 / 1000000000000) ∧
    -Real.log (987257428311 / 1000000000000) ≤ (2564891 / 200000000) := by
  have h := checkLog_sound (w := (12742571689 / 1987257428311)) (n := 12)
    (lo := (6412227 / 500000000)) (hi := (2564891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987257428311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987257428311) = 1/(987257428311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7621 : Bounds (-2564891 / 200000000) (-6412227 / 500000000) (Real.log (987257428311 / 1000000000000)) := by
  have h := reflection_log_7621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7622_neg : (2543031 / 200000000) ≤ -Real.log (61710333799 / 62500000000) ∧
    -Real.log (61710333799 / 62500000000) ≤ (3178789 / 250000000) := by
  have h := checkLog_sound (w := (789666201 / 124210333799)) (n := 12)
    (lo := (2543031 / 200000000)) (hi := (3178789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61710333799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61710333799) = 1/(61710333799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7622 : Bounds (-3178789 / 250000000) (-2543031 / 200000000) (Real.log (61710333799 / 62500000000)) := by
  have h := reflection_log_7622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7623_neg : (225762033 / 1000000000) ≤ -Real.log (500000000000 / 626638695983) ∧
    -Real.log (500000000000 / 626638695983) ≤ (112881017 / 500000000) := by
  have h := checkLog_sound (w := (126638695983 / 1126638695983)) (n := 12)
    (lo := (225762033 / 1000000000)) (hi := (112881017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626638695983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626638695983 / 500000000000) = 1/(500000000000 / 626638695983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7623 : Bounds (225762033 / 1000000000) (112881017 / 500000000) (Real.log (626638695983 / 500000000000)) := by
  have h := reflection_log_7623_neg
  have he : Real.log (626638695983 / 500000000000) = -Real.log (500000000000 / 626638695983) := by
    rw [show ((626638695983 / 500000000000) : ℝ) = ((500000000000 / 626638695983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7624_neg : (45346469 / 200000000) ≤ -Real.log (500000000000 / 627247026041) ∧
    -Real.log (500000000000 / 627247026041) ≤ (113366173 / 500000000) := by
  have h := checkLog_sound (w := (127247026041 / 1127247026041)) (n := 12)
    (lo := (45346469 / 200000000)) (hi := (113366173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627247026041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627247026041 / 500000000000) = 1/(500000000000 / 627247026041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7624 : Bounds (45346469 / 200000000) (113366173 / 500000000) (Real.log (627247026041 / 500000000000)) := by
  have h := reflection_log_7624_neg
  have he : Real.log (627247026041 / 500000000000) = -Real.log (500000000000 / 627247026041) := by
    rw [show ((627247026041 / 500000000000) : ℝ) = ((500000000000 / 627247026041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7625_neg : (90724357 / 200000000) ≤ -Real.log (500000000000 / 787001287001) ∧
    -Real.log (500000000000 / 787001287001) ≤ (226810893 / 500000000) := by
  have h := checkLog_sound (w := (287001287001 / 1287001287001)) (n := 12)
    (lo := (90724357 / 200000000)) (hi := (226810893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787001287001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787001287001 / 500000000000) = 1/(500000000000 / 787001287001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7625 : Bounds (90724357 / 200000000) (226810893 / 500000000) (Real.log (787001287001 / 500000000000)) := by
  have h := reflection_log_7625_neg
  have he : Real.log (787001287001 / 500000000000) = -Real.log (500000000000 / 787001287001) := by
    rw [show ((787001287001 / 500000000000) : ℝ) = ((500000000000 / 787001287001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7626_neg : (1420857 / 3125000) ≤ -Real.log (12500000000 / 19695750161) ∧
    -Real.log (12500000000 / 19695750161) ≤ (454674241 / 1000000000) := by
  have h := checkLog_sound (w := (7195750161 / 32195750161)) (n := 12)
    (lo := (1420857 / 3125000)) (hi := (454674241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19695750161 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19695750161 / 12500000000) = 1/(12500000000 / 19695750161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7626 : Bounds (1420857 / 3125000) (454674241 / 1000000000) (Real.log (19695750161 / 12500000000)) := by
  have h := reflection_log_7626_neg
  have he : Real.log (19695750161 / 12500000000) = -Real.log (12500000000 / 19695750161) := by
    rw [show ((19695750161 / 12500000000) : ℝ) = ((12500000000 / 19695750161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7627_neg : (25265523 / 125000000) ≤ -Real.log (125 / 153) ∧
    -Real.log (125 / 153) ≤ (40424837 / 200000000) := by
  have h := checkLog_sound (w := (14 / 139)) (n := 12)
    (lo := (25265523 / 125000000)) (hi := (40424837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 125) = 1/(125 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7627 : Bounds (25265523 / 125000000) (40424837 / 200000000) (Real.log (153 / 125)) := by
  have h := reflection_log_7627_neg
  have he : Real.log (153 / 125) = -Real.log (125 / 153) := by
    rw [show ((153 / 125) : ℝ) = ((125 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7628_neg : (126801379 / 500000000) ≤ -Real.log (97 / 125) ∧
    -Real.log (97 / 125) ≤ (253602759 / 1000000000) := by
  have h := checkLog_sound (w := (14 / 111)) (n := 12)
    (lo := (126801379 / 500000000)) (hi := (253602759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 97) = 1/(97 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7628 : Bounds (-253602759 / 1000000000) (-126801379 / 500000000) (Real.log (97 / 125)) := by
  have h := reflection_log_7628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7629_neg : (111987 / 500000000) ≤ -Real.log (31250 / 31257) ∧
    -Real.log (31250 / 31257) ≤ (8959 / 40000000) := by
  have h := checkLog_sound (w := (7 / 62507)) (n := 12)
    (lo := (111987 / 500000000)) (hi := (8959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31257 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31257 / 31250) = 1/(31250 / 31257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7629 : Bounds (111987 / 500000000) (8959 / 40000000) (Real.log (31257 / 31250)) := by
  have h := reflection_log_7629_neg
  have he : Real.log (31257 / 31250) = -Real.log (31250 / 31257) := by
    rw [show ((31257 / 31250) : ℝ) = ((31250 / 31257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7630_neg : (8961 / 40000000) ≤ -Real.log (31243 / 31250) ∧
    -Real.log (31243 / 31250) ≤ (112013 / 500000000) := by
  have h := checkLog_sound (w := (7 / 62493)) (n := 12)
    (lo := (8961 / 40000000)) (hi := (112013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31243) = 1/(31243 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7630 : Bounds (-112013 / 500000000) (-8961 / 40000000) (Real.log (31243 / 31250)) := by
  have h := reflection_log_7630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7631_neg : (13344193 / 125000000) ≤ -Real.log (50000 / 55633) ∧
    -Real.log (50000 / 55633) ≤ (21350709 / 200000000) := by
  have h := checkLog_sound (w := (5633 / 105633)) (n := 12)
    (lo := (13344193 / 125000000)) (hi := (21350709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55633 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55633 / 50000) = 1/(50000 / 55633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7631 : Bounds (13344193 / 125000000) (21350709 / 200000000) (Real.log (55633 / 50000)) := by
  have h := reflection_log_7631_neg
  have he : Real.log (55633 / 50000) = -Real.log (50000 / 55633) := by
    rw [show ((55633 / 50000) : ℝ) = ((50000 / 55633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7632_neg : (23905411 / 200000000) ≤ -Real.log (44367 / 50000) ∧
    -Real.log (44367 / 50000) ≤ (7470441 / 62500000) := by
  have h := checkLog_sound (w := (5633 / 94367)) (n := 12)
    (lo := (23905411 / 200000000)) (hi := (7470441 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44367) = 1/(44367 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7632 : Bounds (-7470441 / 62500000) (-23905411 / 200000000) (Real.log (44367 / 50000)) := by
  have h := reflection_log_7632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7633_neg : (2143697 / 20000000) ≤ -Real.log (50000 / 55657) ∧
    -Real.log (50000 / 55657) ≤ (107184851 / 1000000000) := by
  have h := checkLog_sound (w := (5657 / 105657)) (n := 12)
    (lo := (2143697 / 20000000)) (hi := (107184851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55657 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55657 / 50000) = 1/(50000 / 55657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7633 : Bounds (2143697 / 20000000) (107184851 / 1000000000) (Real.log (55657 / 50000)) := by
  have h := reflection_log_7633_neg
  have he : Real.log (55657 / 50000) = -Real.log (50000 / 55657) := by
    rw [show ((55657 / 50000) : ℝ) = ((50000 / 55657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7634_neg : (7504259 / 62500000) ≤ -Real.log (44343 / 50000) ∧
    -Real.log (44343 / 50000) ≤ (24013629 / 200000000) := by
  have h := checkLog_sound (w := (5657 / 94343)) (n := 12)
    (lo := (7504259 / 62500000)) (hi := (24013629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44343) = 1/(44343 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7634 : Bounds (-24013629 / 200000000) (-7504259 / 62500000) (Real.log (44343 / 50000)) := by
  have h := reflection_log_7634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7635_neg : (12883293 / 1000000000) ≤ -Real.log (2467998351 / 2500000000) ∧
    -Real.log (2467998351 / 2500000000) ≤ (6441647 / 500000000) := by
  have h := checkLog_sound (w := (32001649 / 4967998351)) (n := 12)
    (lo := (12883293 / 1000000000)) (hi := (6441647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2467998351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2467998351) = 1/(2467998351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7635 : Bounds (-6441647 / 500000000) (-12883293 / 1000000000) (Real.log (2467998351 / 2500000000)) := by
  have h := reflection_log_7635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7636_neg : (1277351 / 100000000) ≤ -Real.log (2468269311 / 2500000000) ∧
    -Real.log (2468269311 / 2500000000) ≤ (12773511 / 1000000000) := by
  have h := checkLog_sound (w := (31730689 / 4968269311)) (n := 12)
    (lo := (1277351 / 100000000)) (hi := (12773511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2468269311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2468269311) = 1/(2468269311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7636 : Bounds (-12773511 / 1000000000) (-1277351 / 100000000) (Real.log (2468269311 / 2500000000)) := by
  have h := reflection_log_7636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7637_neg : (1131403 / 5000000) ≤ -Real.log (500000000000 / 626963734307) ∧
    -Real.log (500000000000 / 626963734307) ≤ (226280601 / 1000000000) := by
  have h := checkLog_sound (w := (126963734307 / 1126963734307)) (n := 12)
    (lo := (1131403 / 5000000)) (hi := (226280601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626963734307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626963734307 / 500000000000) = 1/(500000000000 / 626963734307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7637 : Bounds (1131403 / 5000000) (226280601 / 1000000000) (Real.log (626963734307 / 500000000000)) := by
  have h := reflection_log_7637_neg
  have he : Real.log (626963734307 / 500000000000) = -Real.log (500000000000 / 626963734307) := by
    rw [show ((626963734307 / 500000000000) : ℝ) = ((500000000000 / 626963734307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7638_neg : (45450599 / 200000000) ≤ -Real.log (500000000000 / 627573686941) ∧
    -Real.log (500000000000 / 627573686941) ≤ (56813249 / 250000000) := by
  have h := checkLog_sound (w := (127573686941 / 1127573686941)) (n := 12)
    (lo := (45450599 / 200000000)) (hi := (56813249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627573686941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627573686941 / 500000000000) = 1/(500000000000 / 627573686941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7638 : Bounds (45450599 / 200000000) (56813249 / 250000000) (Real.log (627573686941 / 500000000000)) := by
  have h := reflection_log_7638_neg
  have he : Real.log (627573686941 / 500000000000) = -Real.log (500000000000 / 627573686941) := by
    rw [show ((627573686941 / 500000000000) : ℝ) = ((500000000000 / 627573686941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7639_neg : (1420857 / 3125000) ≤ -Real.log (500000000000 / 787830006439) ∧
    -Real.log (500000000000 / 787830006439) ≤ (454674241 / 1000000000) := by
  have h := checkLog_sound (w := (287830006439 / 1287830006439)) (n := 12)
    (lo := (1420857 / 3125000)) (hi := (454674241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787830006439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787830006439 / 500000000000) = 1/(500000000000 / 787830006439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7639 : Bounds (1420857 / 3125000) (454674241 / 1000000000) (Real.log (787830006439 / 500000000000)) := by
  have h := reflection_log_7639_neg
  have he : Real.log (787830006439 / 500000000000) = -Real.log (500000000000 / 787830006439) := by
    rw [show ((787830006439 / 500000000000) : ℝ) = ((500000000000 / 787830006439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7640_neg : (227863471 / 500000000) ≤ -Real.log (100000000000 / 157731958763) ∧
    -Real.log (100000000000 / 157731958763) ≤ (455726943 / 1000000000) := by
  have h := checkLog_sound (w := (57731958763 / 257731958763)) (n := 12)
    (lo := (227863471 / 500000000)) (hi := (455726943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157731958763 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157731958763 / 100000000000) = 1/(100000000000 / 157731958763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7640 : Bounds (227863471 / 500000000) (455726943 / 1000000000) (Real.log (157731958763 / 100000000000)) := by
  have h := reflection_log_7640_neg
  have he : Real.log (157731958763 / 100000000000) = -Real.log (100000000000 / 157731958763) := by
    rw [show ((157731958763 / 100000000000) : ℝ) = ((100000000000 / 157731958763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7641_neg : (202532597 / 1000000000) ≤ -Real.log (2000 / 2449) ∧
    -Real.log (2000 / 2449) ≤ (101266299 / 500000000) := by
  have h := checkLog_sound (w := (449 / 4449)) (n := 12)
    (lo := (202532597 / 1000000000)) (hi := (101266299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 2000) = 1/(2000 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7641 : Bounds (202532597 / 1000000000) (101266299 / 500000000) (Real.log (2449 / 2000)) := by
  have h := reflection_log_7641_neg
  have he : Real.log (2449 / 2000) = -Real.log (2000 / 2449) := by
    rw [show ((2449 / 2000) : ℝ) = ((2000 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7642_neg : (1986307 / 7812500) ≤ -Real.log (1551 / 2000) ∧
    -Real.log (1551 / 2000) ≤ (254247297 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3551)) (n := 12)
    (lo := (1986307 / 7812500)) (hi := (254247297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1551) = 1/(1551 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7642 : Bounds (-254247297 / 1000000000) (-1986307 / 7812500) (Real.log (1551 / 2000)) := by
  have h := reflection_log_7642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7643_neg : (112237 / 500000000) ≤ -Real.log (2000000 / 2000449) ∧
    -Real.log (2000000 / 2000449) ≤ (8979 / 40000000) := by
  have h := checkLog_sound (w := (449 / 4000449)) (n := 12)
    (lo := (112237 / 500000000)) (hi := (8979 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000449 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000449 / 2000000) = 1/(2000000 / 2000449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7643 : Bounds (112237 / 500000000) (8979 / 40000000) (Real.log (2000449 / 2000000)) := by
  have h := reflection_log_7643_neg
  have he : Real.log (2000449 / 2000000) = -Real.log (2000000 / 2000449) := by
    rw [show ((2000449 / 2000000) : ℝ) = ((2000000 / 2000449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7644_neg : (8981 / 40000000) ≤ -Real.log (1999551 / 2000000) ∧
    -Real.log (1999551 / 2000000) ≤ (112263 / 500000000) := by
  have h := checkLog_sound (w := (449 / 3999551)) (n := 12)
    (lo := (8981 / 40000000)) (hi := (112263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999551) = 1/(1999551 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7644 : Bounds (-112263 / 500000000) (-8981 / 40000000) (Real.log (1999551 / 2000000)) := by
  have h := reflection_log_7644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7645_neg : (6686531 / 62500000) ≤ -Real.log (1000000 / 1112917) ∧
    -Real.log (1000000 / 1112917) ≤ (106984497 / 1000000000) := by
  have h := checkLog_sound (w := (112917 / 2112917)) (n := 12)
    (lo := (6686531 / 62500000)) (hi := (106984497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1112917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1112917 / 1000000) = 1/(1000000 / 1112917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7645 : Bounds (6686531 / 62500000) (106984497 / 1000000000) (Real.log (1112917 / 1000000)) := by
  have h := reflection_log_7645_neg
  have he : Real.log (1112917 / 1000000) = -Real.log (1000000 / 1112917) := by
    rw [show ((1112917 / 1000000) : ℝ) = ((1000000 / 1112917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7646_neg : (119816727 / 1000000000) ≤ -Real.log (887083 / 1000000) ∧
    -Real.log (887083 / 1000000) ≤ (14977091 / 125000000) := by
  have h := checkLog_sound (w := (112917 / 1887083)) (n := 12)
    (lo := (119816727 / 1000000000)) (hi := (14977091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 887083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 887083) = 1/(887083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7646 : Bounds (-14977091 / 125000000) (-119816727 / 1000000000) (Real.log (887083 / 1000000)) := by
  have h := reflection_log_7646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7647_neg : (53707851 / 500000000) ≤ -Real.log (1000000 / 1113397) ∧
    -Real.log (1000000 / 1113397) ≤ (107415703 / 1000000000) := by
  have h := checkLog_sound (w := (113397 / 2113397)) (n := 12)
    (lo := (53707851 / 500000000)) (hi := (107415703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113397 / 1000000) = 1/(1000000 / 1113397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7647 : Bounds (53707851 / 500000000) (107415703 / 1000000000) (Real.log (1113397 / 1000000)) := by
  have h := reflection_log_7647_neg
  have he : Real.log (1113397 / 1000000) = -Real.log (1000000 / 1113397) := by
    rw [show ((1113397 / 1000000) : ℝ) = ((1000000 / 1113397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7648_neg : (30089493 / 250000000) ≤ -Real.log (886603 / 1000000) ∧
    -Real.log (886603 / 1000000) ≤ (120357973 / 1000000000) := by
  have h := checkLog_sound (w := (113397 / 1886603)) (n := 12)
    (lo := (30089493 / 250000000)) (hi := (120357973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886603) = 1/(886603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7648 : Bounds (-120357973 / 1000000000) (-30089493 / 250000000) (Real.log (886603 / 1000000)) := by
  have h := reflection_log_7648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7649_neg : (1294227 / 100000000) ≤ -Real.log (987141120391 / 1000000000000) ∧
    -Real.log (987141120391 / 1000000000000) ≤ (12942271 / 1000000000) := by
  have h := checkLog_sound (w := (12858879609 / 1987141120391)) (n := 12)
    (lo := (1294227 / 100000000)) (hi := (12942271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987141120391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987141120391) = 1/(987141120391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7649 : Bounds (-12942271 / 1000000000) (-1294227 / 100000000) (Real.log (987141120391 / 1000000000000)) := by
  have h := reflection_log_7649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7650_neg : (1283223 / 100000000) ≤ -Real.log (987249751111 / 1000000000000) ∧
    -Real.log (987249751111 / 1000000000000) ≤ (12832231 / 1000000000) := by
  have h := checkLog_sound (w := (12750248889 / 1987249751111)) (n := 12)
    (lo := (1283223 / 100000000)) (hi := (12832231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987249751111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987249751111) = 1/(987249751111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7650 : Bounds (-12832231 / 1000000000) (-1283223 / 100000000) (Real.log (987249751111 / 1000000000000)) := by
  have h := reflection_log_7650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7651_neg : (226801223 / 1000000000) ≤ -Real.log (100000000000 / 125458046203) ∧
    -Real.log (100000000000 / 125458046203) ≤ (28350153 / 125000000) := by
  have h := checkLog_sound (w := (25458046203 / 225458046203)) (n := 12)
    (lo := (226801223 / 1000000000)) (hi := (28350153 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125458046203 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125458046203 / 100000000000) = 1/(100000000000 / 125458046203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7651 : Bounds (226801223 / 1000000000) (28350153 / 125000000) (Real.log (125458046203 / 100000000000)) := by
  have h := reflection_log_7651_neg
  have he : Real.log (125458046203 / 100000000000) = -Real.log (100000000000 / 125458046203) := by
    rw [show ((125458046203 / 100000000000) : ℝ) = ((100000000000 / 125458046203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7652_neg : (9110947 / 40000000) ≤ -Real.log (25000000000 / 31395026861) ∧
    -Real.log (25000000000 / 31395026861) ≤ (56943419 / 250000000) := by
  have h := checkLog_sound (w := (6395026861 / 56395026861)) (n := 12)
    (lo := (9110947 / 40000000)) (hi := (56943419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31395026861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31395026861 / 25000000000) = 1/(25000000000 / 31395026861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7652 : Bounds (9110947 / 40000000) (56943419 / 250000000) (Real.log (31395026861 / 25000000000)) := by
  have h := reflection_log_7652_neg
  have he : Real.log (31395026861 / 25000000000) = -Real.log (25000000000 / 31395026861) := by
    rw [show ((31395026861 / 25000000000) : ℝ) = ((25000000000 / 31395026861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7653_neg : (227863471 / 500000000) ≤ -Real.log (250000000000 / 394329896907) ∧
    -Real.log (250000000000 / 394329896907) ≤ (455726943 / 1000000000) := by
  have h := checkLog_sound (w := (144329896907 / 644329896907)) (n := 12)
    (lo := (227863471 / 500000000)) (hi := (455726943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394329896907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394329896907 / 250000000000) = 1/(250000000000 / 394329896907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7653 : Bounds (227863471 / 500000000) (455726943 / 1000000000) (Real.log (394329896907 / 250000000000)) := by
  have h := reflection_log_7653_neg
  have he : Real.log (394329896907 / 250000000000) = -Real.log (250000000000 / 394329896907) := by
    rw [show ((394329896907 / 250000000000) : ℝ) = ((250000000000 / 394329896907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7654_neg : (456779893 / 1000000000) ≤ -Real.log (500000000000 / 789490651193) ∧
    -Real.log (500000000000 / 789490651193) ≤ (228389947 / 500000000) := by
  have h := checkLog_sound (w := (289490651193 / 1289490651193)) (n := 12)
    (lo := (456779893 / 1000000000)) (hi := (228389947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789490651193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789490651193 / 500000000000) = 1/(500000000000 / 789490651193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7654 : Bounds (456779893 / 1000000000) (228389947 / 500000000) (Real.log (789490651193 / 500000000000)) := by
  have h := reflection_log_7654_neg
  have he : Real.log (789490651193 / 500000000000) = -Real.log (500000000000 / 789490651193) := by
    rw [show ((789490651193 / 500000000000) : ℝ) = ((500000000000 / 789490651193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7655_neg : (202940843 / 1000000000) ≤ -Real.log (40 / 49) ∧
    -Real.log (40 / 49) ≤ (50735211 / 250000000) := by
  have h := checkLog_sound (w := (9 / 89)) (n := 12)
    (lo := (202940843 / 1000000000)) (hi := (50735211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 40) = 1/(40 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7655 : Bounds (202940843 / 1000000000) (50735211 / 250000000) (Real.log (49 / 40)) := by
  have h := reflection_log_7655_neg
  have he : Real.log (49 / 40) = -Real.log (40 / 49) := by
    rw [show ((49 / 40) : ℝ) = ((40 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7656_neg : (254892249 / 1000000000) ≤ -Real.log (31 / 40) ∧
    -Real.log (31 / 40) ≤ (1019569 / 4000000) := by
  have h := checkLog_sound (w := (9 / 71)) (n := 12)
    (lo := (254892249 / 1000000000)) (hi := (1019569 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 31) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 31) = 1/(31 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7656 : Bounds (-1019569 / 4000000) (-254892249 / 1000000000) (Real.log (31 / 40)) := by
  have h := reflection_log_7656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7657_neg : (112487 / 500000000) ≤ -Real.log (40000 / 40009) ∧
    -Real.log (40000 / 40009) ≤ (8999 / 40000000) := by
  have h := checkLog_sound (w := (9 / 80009)) (n := 12)
    (lo := (112487 / 500000000)) (hi := (8999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40009 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40009 / 40000) = 1/(40000 / 40009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7657 : Bounds (112487 / 500000000) (8999 / 40000000) (Real.log (40009 / 40000)) := by
  have h := reflection_log_7657_neg
  have he : Real.log (40009 / 40000) = -Real.log (40000 / 40009) := by
    rw [show ((40009 / 40000) : ℝ) = ((40000 / 40009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7658_neg : (9001 / 40000000) ≤ -Real.log (39991 / 40000) ∧
    -Real.log (39991 / 40000) ≤ (112513 / 500000000) := by
  have h := checkLog_sound (w := (9 / 79991)) (n := 12)
    (lo := (9001 / 40000000)) (hi := (112513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39991) = 1/(39991 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7658 : Bounds (-112513 / 500000000) (-9001 / 40000000) (Real.log (39991 / 40000)) := by
  have h := reflection_log_7658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7659_neg : (53607697 / 500000000) ≤ -Real.log (500000 / 556587) ∧
    -Real.log (500000 / 556587) ≤ (21443079 / 200000000) := by
  have h := checkLog_sound (w := (56587 / 1056587)) (n := 12)
    (lo := (53607697 / 500000000)) (hi := (21443079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(556587 / 500000) = 1/(500000 / 556587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7659 : Bounds (53607697 / 500000000) (21443079 / 200000000) (Real.log (556587 / 500000)) := by
  have h := reflection_log_7659_neg
  have he : Real.log (556587 / 500000) = -Real.log (500000 / 556587) := by
    rw [show ((556587 / 500000) : ℝ) = ((500000 / 556587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7660_neg : (60053241 / 500000000) ≤ -Real.log (443413 / 500000) ∧
    -Real.log (443413 / 500000) ≤ (120106483 / 1000000000) := by
  have h := checkLog_sound (w := (56587 / 943413)) (n := 12)
    (lo := (60053241 / 500000000)) (hi := (120106483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 443413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 443413) = 1/(443413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7660 : Bounds (-120106483 / 1000000000) (-60053241 / 500000000) (Real.log (443413 / 500000)) := by
  have h := reflection_log_7660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7661_neg : (53823699 / 500000000) ≤ -Real.log (200000 / 222731) ∧
    -Real.log (200000 / 222731) ≤ (107647399 / 1000000000) := by
  have h := checkLog_sound (w := (22731 / 422731)) (n := 12)
    (lo := (53823699 / 500000000)) (hi := (107647399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222731 / 200000) = 1/(200000 / 222731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7661 : Bounds (53823699 / 500000000) (107647399 / 1000000000) (Real.log (222731 / 200000)) := by
  have h := reflection_log_7661_neg
  have he : Real.log (222731 / 200000) = -Real.log (200000 / 222731) := by
    rw [show ((222731 / 200000) : ℝ) = ((200000 / 222731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7662_neg : (120649013 / 1000000000) ≤ -Real.log (177269 / 200000) ∧
    -Real.log (177269 / 200000) ≤ (60324507 / 500000000) := by
  have h := checkLog_sound (w := (22731 / 377269)) (n := 12)
    (lo := (120649013 / 1000000000)) (hi := (60324507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177269) = 1/(177269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7662 : Bounds (-60324507 / 500000000) (-120649013 / 1000000000) (Real.log (177269 / 200000)) := by
  have h := reflection_log_7662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7663_neg : (6500807 / 500000000) ≤ -Real.log (39483301639 / 40000000000) ∧
    -Real.log (39483301639 / 40000000000) ≤ (2600323 / 200000000) := by
  have h := checkLog_sound (w := (516698361 / 79483301639)) (n := 12)
    (lo := (6500807 / 500000000)) (hi := (2600323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39483301639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39483301639) = 1/(39483301639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7663 : Bounds (-2600323 / 200000000) (-6500807 / 500000000) (Real.log (39483301639 / 40000000000)) := by
  have h := reflection_log_7663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7664_neg : (805693 / 62500000) ≤ -Real.log (246797911431 / 250000000000) ∧
    -Real.log (246797911431 / 250000000000) ≤ (12891089 / 1000000000) := by
  have h := checkLog_sound (w := (3202088569 / 496797911431)) (n := 12)
    (lo := (805693 / 62500000)) (hi := (12891089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246797911431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246797911431) = 1/(246797911431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7664 : Bounds (-12891089 / 1000000000) (-805693 / 62500000) (Real.log (246797911431 / 250000000000)) := by
  have h := reflection_log_7664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7665_neg : (227321877 / 1000000000) ≤ -Real.log (3125000000 / 3922605731) ∧
    -Real.log (3125000000 / 3922605731) ≤ (113660939 / 500000000) := by
  have h := checkLog_sound (w := (797605731 / 7047605731)) (n := 12)
    (lo := (227321877 / 1000000000)) (hi := (113660939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3922605731 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3922605731 / 3125000000) = 1/(3125000000 / 3922605731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7665 : Bounds (227321877 / 1000000000) (113660939 / 500000000) (Real.log (3922605731 / 3125000000)) := by
  have h := reflection_log_7665_neg
  have he : Real.log (3922605731 / 3125000000) = -Real.log (3125000000 / 3922605731) := by
    rw [show ((3922605731 / 3125000000) : ℝ) = ((3125000000 / 3922605731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7666_neg : (57074103 / 250000000) ≤ -Real.log (25000000000 / 31411442497) ∧
    -Real.log (25000000000 / 31411442497) ≤ (228296413 / 1000000000) := by
  have h := checkLog_sound (w := (6411442497 / 56411442497)) (n := 12)
    (lo := (57074103 / 250000000)) (hi := (228296413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31411442497 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31411442497 / 25000000000) = 1/(25000000000 / 31411442497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7666 : Bounds (57074103 / 250000000) (228296413 / 1000000000) (Real.log (31411442497 / 25000000000)) := by
  have h := reflection_log_7666_neg
  have he : Real.log (31411442497 / 25000000000) = -Real.log (25000000000 / 31411442497) := by
    rw [show ((31411442497 / 25000000000) : ℝ) = ((25000000000 / 31411442497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7667_neg : (456779893 / 1000000000) ≤ -Real.log (62500000000 / 98686331399) ∧
    -Real.log (62500000000 / 98686331399) ≤ (228389947 / 500000000) := by
  have h := checkLog_sound (w := (36186331399 / 161186331399)) (n := 12)
    (lo := (456779893 / 1000000000)) (hi := (228389947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98686331399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98686331399 / 62500000000) = 1/(62500000000 / 98686331399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7667 : Bounds (456779893 / 1000000000) (228389947 / 500000000) (Real.log (98686331399 / 62500000000)) := by
  have h := reflection_log_7667_neg
  have he : Real.log (98686331399 / 62500000000) = -Real.log (62500000000 / 98686331399) := by
    rw [show ((98686331399 / 62500000000) : ℝ) = ((62500000000 / 98686331399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7668_neg : (457833093 / 1000000000) ≤ -Real.log (250000000000 / 395161290323) ∧
    -Real.log (250000000000 / 395161290323) ≤ (228916547 / 500000000) := by
  have h := checkLog_sound (w := (145161290323 / 645161290323)) (n := 12)
    (lo := (457833093 / 1000000000)) (hi := (228916547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395161290323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395161290323 / 250000000000) = 1/(250000000000 / 395161290323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7668 : Bounds (457833093 / 1000000000) (228916547 / 500000000) (Real.log (395161290323 / 250000000000)) := by
  have h := reflection_log_7668_neg
  have he : Real.log (395161290323 / 250000000000) = -Real.log (250000000000 / 395161290323) := by
    rw [show ((395161290323 / 250000000000) : ℝ) = ((250000000000 / 395161290323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7669_neg : (203348923 / 1000000000) ≤ -Real.log (2000 / 2451) ∧
    -Real.log (2000 / 2451) ≤ (50837231 / 250000000) := by
  have h := checkLog_sound (w := (451 / 4451)) (n := 12)
    (lo := (203348923 / 1000000000)) (hi := (50837231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2451 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2451 / 2000) = 1/(2000 / 2451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7669 : Bounds (203348923 / 1000000000) (50837231 / 250000000) (Real.log (2451 / 2000)) := by
  have h := reflection_log_7669_neg
  have he : Real.log (2451 / 2000) = -Real.log (2000 / 2451) := by
    rw [show ((2451 / 2000) : ℝ) = ((2000 / 2451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7670_neg : (255537619 / 1000000000) ≤ -Real.log (1549 / 2000) ∧
    -Real.log (1549 / 2000) ≤ (12776881 / 50000000) := by
  have h := checkLog_sound (w := (451 / 3549)) (n := 12)
    (lo := (255537619 / 1000000000)) (hi := (12776881 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1549) = 1/(1549 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7670 : Bounds (-12776881 / 50000000) (-255537619 / 1000000000) (Real.log (1549 / 2000)) := by
  have h := reflection_log_7670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7671_neg : (112737 / 500000000) ≤ -Real.log (2000000 / 2000451) ∧
    -Real.log (2000000 / 2000451) ≤ (9019 / 40000000) := by
  have h := checkLog_sound (w := (451 / 4000451)) (n := 12)
    (lo := (112737 / 500000000)) (hi := (9019 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000451 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000451 / 2000000) = 1/(2000000 / 2000451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7671 : Bounds (112737 / 500000000) (9019 / 40000000) (Real.log (2000451 / 2000000)) := by
  have h := reflection_log_7671_neg
  have he : Real.log (2000451 / 2000000) = -Real.log (2000000 / 2000451) := by
    rw [show ((2000451 / 2000000) : ℝ) = ((2000000 / 2000451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7672_neg : (9021 / 40000000) ≤ -Real.log (1999549 / 2000000) ∧
    -Real.log (1999549 / 2000000) ≤ (112763 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3999549)) (n := 12)
    (lo := (9021 / 40000000)) (hi := (112763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999549) = 1/(1999549 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7672 : Bounds (-112763 / 500000000) (-9021 / 40000000) (Real.log (1999549 / 2000000)) := by
  have h := reflection_log_7672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7673_neg : (107446239 / 1000000000) ≤ -Real.log (1000000 / 1113431) ∧
    -Real.log (1000000 / 1113431) ≤ (671539 / 6250000) := by
  have h := checkLog_sound (w := (113431 / 2113431)) (n := 12)
    (lo := (107446239 / 1000000000)) (hi := (671539 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1113431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1113431 / 1000000) = 1/(1000000 / 1113431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7673 : Bounds (107446239 / 1000000000) (671539 / 6250000) (Real.log (1113431 / 1000000)) := by
  have h := reflection_log_7673_neg
  have he : Real.log (1113431 / 1000000) = -Real.log (1000000 / 1113431) := by
    rw [show ((1113431 / 1000000) : ℝ) = ((1000000 / 1113431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7674_neg : (60198161 / 500000000) ≤ -Real.log (886569 / 1000000) ∧
    -Real.log (886569 / 1000000) ≤ (120396323 / 1000000000) := by
  have h := checkLog_sound (w := (113431 / 1886569)) (n := 12)
    (lo := (60198161 / 500000000)) (hi := (120396323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 886569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 886569) = 1/(886569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7674 : Bounds (-120396323 / 1000000000) (-60198161 / 500000000) (Real.log (886569 / 1000000)) := by
  have h := reflection_log_7674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7675_neg : (107878143 / 1000000000) ≤ -Real.log (125000 / 139239) ∧
    -Real.log (125000 / 139239) ≤ (421399 / 3906250) := by
  have h := checkLog_sound (w := (14239 / 264239)) (n := 12)
    (lo := (107878143 / 1000000000)) (hi := (421399 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139239 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139239 / 125000) = 1/(125000 / 139239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7675 : Bounds (107878143 / 1000000000) (421399 / 3906250) (Real.log (139239 / 125000)) := by
  have h := reflection_log_7675_neg
  have he : Real.log (139239 / 125000) = -Real.log (125000 / 139239) := by
    rw [show ((139239 / 125000) : ℝ) = ((125000 / 139239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7676_neg : (12093901 / 100000000) ≤ -Real.log (110761 / 125000) ∧
    -Real.log (110761 / 125000) ≤ (120939011 / 1000000000) := by
  have h := checkLog_sound (w := (14239 / 235761)) (n := 12)
    (lo := (12093901 / 100000000)) (hi := (120939011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110761) = 1/(110761 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7676 : Bounds (-120939011 / 1000000000) (-12093901 / 100000000) (Real.log (110761 / 125000)) := by
  have h := reflection_log_7676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7677_neg : (6530433 / 500000000) ≤ -Real.log (15422250879 / 15625000000) ∧
    -Real.log (15422250879 / 15625000000) ≤ (13060867 / 1000000000) := by
  have h := checkLog_sound (w := (202749121 / 31047250879)) (n := 12)
    (lo := (6530433 / 500000000)) (hi := (13060867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15422250879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15422250879) = 1/(15422250879 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7677 : Bounds (-13060867 / 1000000000) (-6530433 / 500000000) (Real.log (15422250879 / 15625000000)) := by
  have h := reflection_log_7677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7678_neg : (12950083 / 1000000000) ≤ -Real.log (987133408239 / 1000000000000) ∧
    -Real.log (987133408239 / 1000000000000) ≤ (3237521 / 250000000) := by
  have h := checkLog_sound (w := (12866591761 / 1987133408239)) (n := 12)
    (lo := (12950083 / 1000000000)) (hi := (3237521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 987133408239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 987133408239) = 1/(987133408239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7678 : Bounds (-3237521 / 250000000) (-12950083 / 1000000000) (Real.log (987133408239 / 1000000000000)) := by
  have h := reflection_log_7678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7679_neg : (227842561 / 1000000000) ≤ -Real.log (31250000000 / 39246487019) ∧
    -Real.log (31250000000 / 39246487019) ≤ (113921281 / 500000000) := by
  have h := checkLog_sound (w := (7996487019 / 70496487019)) (n := 12)
    (lo := (227842561 / 1000000000)) (hi := (113921281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39246487019 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39246487019 / 31250000000) = 1/(31250000000 / 39246487019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7679 : Bounds (227842561 / 1000000000) (113921281 / 500000000) (Real.log (39246487019 / 31250000000)) := by
  have h := reflection_log_7679_neg
  have he : Real.log (39246487019 / 31250000000) = -Real.log (31250000000 / 39246487019) := by
    rw [show ((39246487019 / 31250000000) : ℝ) = ((31250000000 / 39246487019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
