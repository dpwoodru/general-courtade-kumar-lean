import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1536_neg : (162478501 / 1000000000) ≤ -Real.log (62500000000 / 73526439187) ∧
    -Real.log (62500000000 / 73526439187) ≤ (81239251 / 500000000) := by
  have h := checkLog_sound (w := (11026439187 / 136026439187)) (n := 12)
    (lo := (162478501 / 1000000000)) (hi := (81239251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73526439187 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73526439187 / 62500000000) = 1/(62500000000 / 73526439187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1536 : Bounds (162478501 / 1000000000) (81239251 / 500000000) (Real.log (73526439187 / 62500000000)) := by
  have h := reflection_log_1536_neg
  have he : Real.log (73526439187 / 62500000000) = -Real.log (62500000000 / 73526439187) := by
    rw [show ((73526439187 / 62500000000) : ℝ) = ((62500000000 / 73526439187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1537_neg : (812579 / 2500000) ≤ -Real.log (12500000000 / 17300929789) ∧
    -Real.log (12500000000 / 17300929789) ≤ (325031601 / 1000000000) := by
  have h := checkLog_sound (w := (4800929789 / 29800929789)) (n := 12)
    (lo := (812579 / 2500000)) (hi := (325031601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17300929789 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17300929789 / 12500000000) = 1/(12500000000 / 17300929789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1537 : Bounds (812579 / 2500000) (325031601 / 1000000000) (Real.log (17300929789 / 12500000000)) := by
  have h := reflection_log_1537_neg
  have he : Real.log (17300929789 / 12500000000) = -Real.log (12500000000 / 17300929789) := by
    rw [show ((17300929789 / 12500000000) : ℝ) = ((12500000000 / 17300929789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1538_neg : (325236933 / 1000000000) ≤ -Real.log (62500000000 / 86522412971) ∧
    -Real.log (62500000000 / 86522412971) ≤ (162618467 / 500000000) := by
  have h := checkLog_sound (w := (24022412971 / 149022412971)) (n := 12)
    (lo := (325236933 / 1000000000)) (hi := (162618467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86522412971 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86522412971 / 62500000000) = 1/(62500000000 / 86522412971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1538 : Bounds (325236933 / 1000000000) (162618467 / 500000000) (Real.log (86522412971 / 62500000000)) := by
  have h := reflection_log_1538_neg
  have he : Real.log (86522412971 / 62500000000) = -Real.log (62500000000 / 86522412971) := by
    rw [show ((86522412971 / 62500000000) : ℝ) = ((62500000000 / 86522412971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1539_neg : (149540067 / 1000000000) ≤ -Real.log (10000 / 11613) ∧
    -Real.log (10000 / 11613) ≤ (37385017 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 21613)) (n := 12)
    (lo := (149540067 / 1000000000)) (hi := (37385017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11613 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11613 / 10000) = 1/(10000 / 11613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1539 : Bounds (149540067 / 1000000000) (37385017 / 250000000) (Real.log (11613 / 10000)) := by
  have h := reflection_log_1539_neg
  have he : Real.log (11613 / 10000) = -Real.log (10000 / 11613) := by
    rw [show ((11613 / 10000) : ℝ) = ((10000 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1540_neg : (43975551 / 250000000) ≤ -Real.log (8387 / 10000) ∧
    -Real.log (8387 / 10000) ≤ (35180441 / 200000000) := by
  have h := checkLog_sound (w := (1613 / 18387)) (n := 12)
    (lo := (43975551 / 250000000)) (hi := (35180441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8387) = 1/(8387 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1540 : Bounds (-35180441 / 200000000) (-43975551 / 250000000) (Real.log (8387 / 10000)) := by
  have h := reflection_log_1540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1541_neg : (80643 / 500000000) ≤ -Real.log (10000000 / 10001613) ∧
    -Real.log (10000000 / 10001613) ≤ (161287 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 20001613)) (n := 12)
    (lo := (80643 / 500000000)) (hi := (161287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001613 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001613 / 10000000) = 1/(10000000 / 10001613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1541 : Bounds (80643 / 500000000) (161287 / 1000000000) (Real.log (10001613 / 10000000)) := by
  have h := reflection_log_1541_neg
  have he : Real.log (10001613 / 10000000) = -Real.log (10000000 / 10001613) := by
    rw [show ((10001613 / 10000000) : ℝ) = ((10000000 / 10001613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1542_neg : (161313 / 1000000000) ≤ -Real.log (9998387 / 10000000) ∧
    -Real.log (9998387 / 10000000) ≤ (80657 / 500000000) := by
  have h := checkLog_sound (w := (1613 / 19998387)) (n := 12)
    (lo := (161313 / 1000000000)) (hi := (80657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998387) = 1/(9998387 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1542 : Bounds (-80657 / 500000000) (-161313 / 1000000000) (Real.log (9998387 / 10000000)) := by
  have h := reflection_log_1542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1543_neg : (77794027 / 1000000000) ≤ -Real.log (10000 / 10809) ∧
    -Real.log (10000 / 10809) ≤ (19448507 / 250000000) := by
  have h := checkLog_sound (w := (809 / 20809)) (n := 12)
    (lo := (77794027 / 1000000000)) (hi := (19448507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10809 / 10000) = 1/(10000 / 10809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1543 : Bounds (77794027 / 1000000000) (19448507 / 250000000) (Real.log (10809 / 10000)) := by
  have h := reflection_log_1543_neg
  have he : Real.log (10809 / 10000) = -Real.log (10000 / 10809) := by
    rw [show ((10809 / 10000) : ℝ) = ((10000 / 10809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1544_neg : (21090087 / 250000000) ≤ -Real.log (9191 / 10000) ∧
    -Real.log (9191 / 10000) ≤ (84360349 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 19191)) (n := 12)
    (lo := (21090087 / 250000000)) (hi := (84360349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9191) = 1/(9191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1544 : Bounds (-84360349 / 1000000000) (-21090087 / 250000000) (Real.log (9191 / 10000)) := by
  have h := reflection_log_1544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1545_neg : (77990141 / 1000000000) ≤ -Real.log (125000 / 135139) ∧
    -Real.log (125000 / 135139) ≤ (38995071 / 500000000) := by
  have h := checkLog_sound (w := (10139 / 260139)) (n := 12)
    (lo := (77990141 / 1000000000)) (hi := (38995071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135139 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135139 / 125000) = 1/(125000 / 135139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1545 : Bounds (77990141 / 1000000000) (38995071 / 500000000) (Real.log (135139 / 125000)) := by
  have h := reflection_log_1545_neg
  have he : Real.log (135139 / 125000) = -Real.log (125000 / 135139) := by
    rw [show ((135139 / 125000) : ℝ) = ((125000 / 135139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1546_neg : (16918207 / 200000000) ≤ -Real.log (114861 / 125000) ∧
    -Real.log (114861 / 125000) ≤ (21147759 / 250000000) := by
  have h := checkLog_sound (w := (10139 / 239861)) (n := 12)
    (lo := (16918207 / 200000000)) (hi := (21147759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114861) = 1/(114861 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1546 : Bounds (-21147759 / 250000000) (-16918207 / 200000000) (Real.log (114861 / 125000)) := by
  have h := reflection_log_1546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1547_neg : (3300447 / 500000000) ≤ -Real.log (15522200679 / 15625000000) ∧
    -Real.log (15522200679 / 15625000000) ≤ (1320179 / 200000000) := by
  have h := checkLog_sound (w := (102799321 / 31147200679)) (n := 12)
    (lo := (3300447 / 500000000)) (hi := (1320179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15522200679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15522200679) = 1/(15522200679 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1547 : Bounds (-1320179 / 200000000) (-3300447 / 500000000) (Real.log (15522200679 / 15625000000)) := by
  have h := reflection_log_1547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1548_neg : (6566321 / 1000000000) ≤ -Real.log (99345519 / 100000000) ∧
    -Real.log (99345519 / 100000000) ≤ (3283161 / 500000000) := by
  have h := checkLog_sound (w := (654481 / 199345519)) (n := 12)
    (lo := (6566321 / 1000000000)) (hi := (3283161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99345519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99345519) = 1/(99345519 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1548 : Bounds (-3283161 / 500000000) (-6566321 / 1000000000) (Real.log (99345519 / 100000000)) := by
  have h := reflection_log_1548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1549_neg : (20269297 / 125000000) ≤ -Real.log (500000000000 / 588020890001) ∧
    -Real.log (500000000000 / 588020890001) ≤ (162154377 / 1000000000) := by
  have h := checkLog_sound (w := (88020890001 / 1088020890001)) (n := 12)
    (lo := (20269297 / 125000000)) (hi := (162154377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588020890001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588020890001 / 500000000000) = 1/(500000000000 / 588020890001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1549 : Bounds (20269297 / 125000000) (162154377 / 1000000000) (Real.log (588020890001 / 500000000000)) := by
  have h := reflection_log_1549_neg
  have he : Real.log (588020890001 / 500000000000) = -Real.log (500000000000 / 588020890001) := by
    rw [show ((588020890001 / 500000000000) : ℝ) = ((500000000000 / 588020890001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1550_neg : (20322647 / 125000000) ≤ -Real.log (500000000000 / 588271911267) ∧
    -Real.log (500000000000 / 588271911267) ≤ (162581177 / 1000000000) := by
  have h := checkLog_sound (w := (88271911267 / 1088271911267)) (n := 12)
    (lo := (20322647 / 125000000)) (hi := (162581177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588271911267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588271911267 / 500000000000) = 1/(500000000000 / 588271911267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1550 : Bounds (20322647 / 125000000) (162581177 / 1000000000) (Real.log (588271911267 / 500000000000)) := by
  have h := reflection_log_1550_neg
  have he : Real.log (588271911267 / 500000000000) = -Real.log (500000000000 / 588271911267) := by
    rw [show ((588271911267 / 500000000000) : ℝ) = ((500000000000 / 588271911267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1551_neg : (325236933 / 1000000000) ≤ -Real.log (500000000000 / 692179303767) ∧
    -Real.log (500000000000 / 692179303767) ≤ (162618467 / 500000000) := by
  have h := checkLog_sound (w := (192179303767 / 1192179303767)) (n := 12)
    (lo := (325236933 / 1000000000)) (hi := (162618467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692179303767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692179303767 / 500000000000) = 1/(500000000000 / 692179303767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1551 : Bounds (325236933 / 1000000000) (162618467 / 500000000) (Real.log (692179303767 / 500000000000)) := by
  have h := reflection_log_1551_neg
  have he : Real.log (692179303767 / 500000000000) = -Real.log (500000000000 / 692179303767) := by
    rw [show ((692179303767 / 500000000000) : ℝ) = ((500000000000 / 692179303767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1552_neg : (10170071 / 31250000) ≤ -Real.log (500000000000 / 692321449863) ∧
    -Real.log (500000000000 / 692321449863) ≤ (325442273 / 1000000000) := by
  have h := checkLog_sound (w := (192321449863 / 1192321449863)) (n := 12)
    (lo := (10170071 / 31250000)) (hi := (325442273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692321449863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692321449863 / 500000000000) = 1/(500000000000 / 692321449863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1552 : Bounds (10170071 / 31250000) (325442273 / 1000000000) (Real.log (692321449863 / 500000000000)) := by
  have h := reflection_log_1552_neg
  have he : Real.log (692321449863 / 500000000000) = -Real.log (500000000000 / 692321449863) := by
    rw [show ((692321449863 / 500000000000) : ℝ) = ((500000000000 / 692321449863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1553_neg : (149626173 / 1000000000) ≤ -Real.log (5000 / 5807) ∧
    -Real.log (5000 / 5807) ≤ (74813087 / 500000000) := by
  have h := checkLog_sound (w := (807 / 10807)) (n := 12)
    (lo := (149626173 / 1000000000)) (hi := (74813087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5807 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5807 / 5000) = 1/(5000 / 5807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1553 : Bounds (149626173 / 1000000000) (74813087 / 500000000) (Real.log (5807 / 5000)) := by
  have h := reflection_log_1553_neg
  have he : Real.log (5807 / 5000) = -Real.log (5000 / 5807) := by
    rw [show ((5807 / 5000) : ℝ) = ((5000 / 5807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1554_neg : (44005361 / 250000000) ≤ -Real.log (4193 / 5000) ∧
    -Real.log (4193 / 5000) ≤ (35204289 / 200000000) := by
  have h := checkLog_sound (w := (807 / 9193)) (n := 12)
    (lo := (44005361 / 250000000)) (hi := (35204289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4193) = 1/(4193 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1554 : Bounds (-35204289 / 200000000) (-44005361 / 250000000) (Real.log (4193 / 5000)) := by
  have h := reflection_log_1554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1555_neg : (80693 / 500000000) ≤ -Real.log (5000000 / 5000807) ∧
    -Real.log (5000000 / 5000807) ≤ (161387 / 1000000000) := by
  have h := checkLog_sound (w := (807 / 10000807)) (n := 12)
    (lo := (80693 / 500000000)) (hi := (161387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000807 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000807 / 5000000) = 1/(5000000 / 5000807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1555 : Bounds (80693 / 500000000) (161387 / 1000000000) (Real.log (5000807 / 5000000)) := by
  have h := reflection_log_1555_neg
  have he : Real.log (5000807 / 5000000) = -Real.log (5000000 / 5000807) := by
    rw [show ((5000807 / 5000000) : ℝ) = ((5000000 / 5000807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1556_neg : (161413 / 1000000000) ≤ -Real.log (4999193 / 5000000) ∧
    -Real.log (4999193 / 5000000) ≤ (80707 / 500000000) := by
  have h := checkLog_sound (w := (807 / 9999193)) (n := 12)
    (lo := (161413 / 1000000000)) (hi := (80707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999193) = 1/(4999193 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1556 : Bounds (-80707 / 500000000) (-161413 / 1000000000) (Real.log (4999193 / 5000000)) := by
  have h := reflection_log_1556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1557_neg : (77841209 / 1000000000) ≤ -Real.log (1000000 / 1080951) ∧
    -Real.log (1000000 / 1080951) ≤ (7784121 / 100000000) := by
  have h := checkLog_sound (w := (80951 / 2080951)) (n := 12)
    (lo := (77841209 / 1000000000)) (hi := (7784121 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080951 / 1000000) = 1/(1000000 / 1080951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1557 : Bounds (77841209 / 1000000000) (7784121 / 100000000) (Real.log (1080951 / 1000000)) := by
  have h := reflection_log_1557_neg
  have he : Real.log (1080951 / 1000000) = -Real.log (1000000 / 1080951) := by
    rw [show ((1080951 / 1000000) : ℝ) = ((1000000 / 1080951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1558_neg : (84415839 / 1000000000) ≤ -Real.log (919049 / 1000000) ∧
    -Real.log (919049 / 1000000) ≤ (527599 / 6250000) := by
  have h := checkLog_sound (w := (80951 / 1919049)) (n := 12)
    (lo := (84415839 / 1000000000)) (hi := (527599 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919049) = 1/(919049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1558 : Bounds (-527599 / 6250000) (-84415839 / 1000000000) (Real.log (919049 / 1000000)) := by
  have h := reflection_log_1558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1559_neg : (78037313 / 1000000000) ≤ -Real.log (1000000 / 1081163) ∧
    -Real.log (1000000 / 1081163) ≤ (39018657 / 500000000) := by
  have h := checkLog_sound (w := (81163 / 2081163)) (n := 12)
    (lo := (78037313 / 1000000000)) (hi := (39018657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081163 / 1000000) = 1/(1000000 / 1081163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1559 : Bounds (78037313 / 1000000000) (39018657 / 500000000) (Real.log (1081163 / 1000000)) := by
  have h := reflection_log_1559_neg
  have he : Real.log (1081163 / 1000000) = -Real.log (1000000 / 1081163) := by
    rw [show ((1081163 / 1000000) : ℝ) = ((1000000 / 1081163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1560_neg : (84646539 / 1000000000) ≤ -Real.log (918837 / 1000000) ∧
    -Real.log (918837 / 1000000) ≤ (4232327 / 50000000) := by
  have h := checkLog_sound (w := (81163 / 1918837)) (n := 12)
    (lo := (84646539 / 1000000000)) (hi := (4232327 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918837) = 1/(918837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1560 : Bounds (-4232327 / 50000000) (-84646539 / 1000000000) (Real.log (918837 / 1000000)) := by
  have h := reflection_log_1560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1561_neg : (264369 / 40000000) ≤ -Real.log (993412567431 / 1000000000000) ∧
    -Real.log (993412567431 / 1000000000000) ≤ (3304613 / 500000000) := by
  have h := checkLog_sound (w := (6587432569 / 1993412567431)) (n := 12)
    (lo := (264369 / 40000000)) (hi := (3304613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993412567431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993412567431) = 1/(993412567431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1561 : Bounds (-3304613 / 500000000) (-264369 / 40000000) (Real.log (993412567431 / 1000000000000)) := by
  have h := reflection_log_1561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1562_neg : (6574629 / 1000000000) ≤ -Real.log (993446935599 / 1000000000000) ∧
    -Real.log (993446935599 / 1000000000000) ≤ (657463 / 100000000) := by
  have h := checkLog_sound (w := (6553064401 / 1993446935599)) (n := 12)
    (lo := (6574629 / 1000000000)) (hi := (657463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993446935599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993446935599) = 1/(993446935599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1562 : Bounds (-657463 / 100000000) (-6574629 / 1000000000) (Real.log (993446935599 / 1000000000000)) := by
  have h := reflection_log_1562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1563_neg : (20282131 / 125000000) ≤ -Real.log (500000000000 / 588081266613) ∧
    -Real.log (500000000000 / 588081266613) ≤ (162257049 / 1000000000) := by
  have h := checkLog_sound (w := (88081266613 / 1088081266613)) (n := 12)
    (lo := (20282131 / 125000000)) (hi := (162257049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588081266613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588081266613 / 500000000000) = 1/(500000000000 / 588081266613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1563 : Bounds (20282131 / 125000000) (162257049 / 1000000000) (Real.log (588081266613 / 500000000000)) := by
  have h := reflection_log_1563_neg
  have he : Real.log (588081266613 / 500000000000) = -Real.log (500000000000 / 588081266613) := by
    rw [show ((588081266613 / 500000000000) : ℝ) = ((500000000000 / 588081266613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1564_neg : (40670963 / 250000000) ≤ -Real.log (500000000000 / 588332315743) ∧
    -Real.log (500000000000 / 588332315743) ≤ (162683853 / 1000000000) := by
  have h := checkLog_sound (w := (88332315743 / 1088332315743)) (n := 12)
    (lo := (40670963 / 250000000)) (hi := (162683853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588332315743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588332315743 / 500000000000) = 1/(500000000000 / 588332315743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1564 : Bounds (40670963 / 250000000) (162683853 / 1000000000) (Real.log (588332315743 / 500000000000)) := by
  have h := reflection_log_1564_neg
  have he : Real.log (588332315743 / 500000000000) = -Real.log (500000000000 / 588332315743) := by
    rw [show ((588332315743 / 500000000000) : ℝ) = ((500000000000 / 588332315743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1565_neg : (10170071 / 31250000) ≤ -Real.log (250000000000 / 346160724931) ∧
    -Real.log (250000000000 / 346160724931) ≤ (325442273 / 1000000000) := by
  have h := checkLog_sound (w := (96160724931 / 596160724931)) (n := 12)
    (lo := (10170071 / 31250000)) (hi := (325442273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346160724931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346160724931 / 250000000000) = 1/(250000000000 / 346160724931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1565 : Bounds (10170071 / 31250000) (325442273 / 1000000000) (Real.log (346160724931 / 250000000000)) := by
  have h := reflection_log_1565_neg
  have he : Real.log (346160724931 / 250000000000) = -Real.log (250000000000 / 346160724931) := by
    rw [show ((346160724931 / 250000000000) : ℝ) = ((250000000000 / 346160724931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1566_neg : (162823809 / 500000000) ≤ -Real.log (25000000000 / 34623181493) ∧
    -Real.log (25000000000 / 34623181493) ≤ (325647619 / 1000000000) := by
  have h := checkLog_sound (w := (9623181493 / 59623181493)) (n := 12)
    (lo := (162823809 / 500000000)) (hi := (325647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34623181493 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34623181493 / 25000000000) = 1/(25000000000 / 34623181493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1566 : Bounds (162823809 / 500000000) (325647619 / 1000000000) (Real.log (34623181493 / 25000000000)) := by
  have h := reflection_log_1566_neg
  have he : Real.log (34623181493 / 25000000000) = -Real.log (25000000000 / 34623181493) := by
    rw [show ((34623181493 / 25000000000) : ℝ) = ((25000000000 / 34623181493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1567_neg : (149712273 / 1000000000) ≤ -Real.log (2000 / 2323) ∧
    -Real.log (2000 / 2323) ≤ (74856137 / 500000000) := by
  have h := checkLog_sound (w := (323 / 4323)) (n := 12)
    (lo := (149712273 / 1000000000)) (hi := (74856137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 2000) = 1/(2000 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1567 : Bounds (149712273 / 1000000000) (74856137 / 500000000) (Real.log (2323 / 2000)) := by
  have h := reflection_log_1567_neg
  have he : Real.log (2323 / 2000) = -Real.log (2000 / 2323) := by
    rw [show ((2323 / 2000) : ℝ) = ((2000 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1568_neg : (176140697 / 1000000000) ≤ -Real.log (1677 / 2000) ∧
    -Real.log (1677 / 2000) ≤ (88070349 / 500000000) := by
  have h := checkLog_sound (w := (323 / 3677)) (n := 12)
    (lo := (176140697 / 1000000000)) (hi := (88070349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1677) = 1/(1677 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1568 : Bounds (-88070349 / 500000000) (-176140697 / 1000000000) (Real.log (1677 / 2000)) := by
  have h := reflection_log_1568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1569_neg : (80743 / 500000000) ≤ -Real.log (2000000 / 2000323) ∧
    -Real.log (2000000 / 2000323) ≤ (161487 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 4000323)) (n := 12)
    (lo := (80743 / 500000000)) (hi := (161487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000323 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000323 / 2000000) = 1/(2000000 / 2000323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1569 : Bounds (80743 / 500000000) (161487 / 1000000000) (Real.log (2000323 / 2000000)) := by
  have h := reflection_log_1569_neg
  have he : Real.log (2000323 / 2000000) = -Real.log (2000000 / 2000323) := by
    rw [show ((2000323 / 2000000) : ℝ) = ((2000000 / 2000323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1570_neg : (161513 / 1000000000) ≤ -Real.log (1999677 / 2000000) ∧
    -Real.log (1999677 / 2000000) ≤ (80757 / 500000000) := by
  have h := checkLog_sound (w := (323 / 3999677)) (n := 12)
    (lo := (161513 / 1000000000)) (hi := (80757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999677) = 1/(1999677 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1570 : Bounds (-80757 / 500000000) (-161513 / 1000000000) (Real.log (1999677 / 2000000)) := by
  have h := reflection_log_1570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1571_neg : (77887463 / 1000000000) ≤ -Real.log (1000000 / 1081001) ∧
    -Real.log (1000000 / 1081001) ≤ (9735933 / 125000000) := by
  have h := checkLog_sound (w := (81001 / 2081001)) (n := 12)
    (lo := (77887463 / 1000000000)) (hi := (9735933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081001 / 1000000) = 1/(1000000 / 1081001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1571 : Bounds (77887463 / 1000000000) (9735933 / 125000000) (Real.log (1081001 / 1000000)) := by
  have h := reflection_log_1571_neg
  have he : Real.log (1081001 / 1000000) = -Real.log (1000000 / 1081001) := by
    rw [show ((1081001 / 1000000) : ℝ) = ((1000000 / 1081001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1572_neg : (21117561 / 250000000) ≤ -Real.log (918999 / 1000000) ∧
    -Real.log (918999 / 1000000) ≤ (16894049 / 200000000) := by
  have h := checkLog_sound (w := (81001 / 1918999)) (n := 12)
    (lo := (21117561 / 250000000)) (hi := (16894049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918999) = 1/(918999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1572 : Bounds (-16894049 / 200000000) (-21117561 / 250000000) (Real.log (918999 / 1000000)) := by
  have h := reflection_log_1572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1573_neg : (78084483 / 1000000000) ≤ -Real.log (500000 / 540607) ∧
    -Real.log (500000 / 540607) ≤ (19521121 / 250000000) := by
  have h := checkLog_sound (w := (40607 / 1040607)) (n := 12)
    (lo := (78084483 / 1000000000)) (hi := (19521121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540607 / 500000) = 1/(500000 / 540607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1573 : Bounds (78084483 / 1000000000) (19521121 / 250000000) (Real.log (540607 / 500000)) := by
  have h := reflection_log_1573_neg
  have he : Real.log (540607 / 500000) = -Real.log (500000 / 540607) := by
    rw [show ((540607 / 500000) : ℝ) = ((500000 / 540607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1574_neg : (16940409 / 200000000) ≤ -Real.log (459393 / 500000) ∧
    -Real.log (459393 / 500000) ≤ (42351023 / 500000000) := by
  have h := checkLog_sound (w := (40607 / 959393)) (n := 12)
    (lo := (16940409 / 200000000)) (hi := (42351023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459393) = 1/(459393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1574 : Bounds (-42351023 / 500000000) (-16940409 / 200000000) (Real.log (459393 / 500000)) := by
  have h := reflection_log_1574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1575_neg : (6617561 / 1000000000) ≤ -Real.log (248351071551 / 250000000000) ∧
    -Real.log (248351071551 / 250000000000) ≤ (3308781 / 500000000) := by
  have h := checkLog_sound (w := (1648928449 / 498351071551)) (n := 12)
    (lo := (6617561 / 1000000000)) (hi := (3308781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248351071551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248351071551) = 1/(248351071551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1575 : Bounds (-3308781 / 500000000) (-6617561 / 1000000000) (Real.log (248351071551 / 250000000000)) := by
  have h := reflection_log_1575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1576_neg : (6582781 / 1000000000) ≤ -Real.log (993438837999 / 1000000000000) ∧
    -Real.log (993438837999 / 1000000000000) ≤ (3291391 / 500000000) := by
  have h := checkLog_sound (w := (6561162001 / 1993438837999)) (n := 12)
    (lo := (6582781 / 1000000000)) (hi := (3291391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993438837999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993438837999) = 1/(993438837999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1576 : Bounds (-3291391 / 500000000) (-6582781 / 1000000000) (Real.log (993438837999 / 1000000000000)) := by
  have h := reflection_log_1576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1577_neg : (40589427 / 250000000) ≤ -Real.log (125000000000 / 147035116469) ∧
    -Real.log (125000000000 / 147035116469) ≤ (162357709 / 1000000000) := by
  have h := checkLog_sound (w := (22035116469 / 272035116469)) (n := 12)
    (lo := (40589427 / 250000000)) (hi := (162357709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147035116469 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147035116469 / 125000000000) = 1/(125000000000 / 147035116469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1577 : Bounds (40589427 / 250000000) (162357709 / 1000000000) (Real.log (147035116469 / 125000000000)) := by
  have h := reflection_log_1577_neg
  have he : Real.log (147035116469 / 125000000000) = -Real.log (125000000000 / 147035116469) := by
    rw [show ((147035116469 / 125000000000) : ℝ) = ((125000000000 / 147035116469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1578_neg : (162786529 / 1000000000) ≤ -Real.log (20000000000 / 23535709077) ∧
    -Real.log (20000000000 / 23535709077) ≤ (16278653 / 100000000) := by
  have h := checkLog_sound (w := (3535709077 / 43535709077)) (n := 12)
    (lo := (162786529 / 1000000000)) (hi := (16278653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23535709077 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23535709077 / 20000000000) = 1/(20000000000 / 23535709077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1578 : Bounds (162786529 / 1000000000) (16278653 / 100000000) (Real.log (23535709077 / 20000000000)) := by
  have h := reflection_log_1578_neg
  have he : Real.log (23535709077 / 20000000000) = -Real.log (20000000000 / 23535709077) := by
    rw [show ((23535709077 / 20000000000) : ℝ) = ((20000000000 / 23535709077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1579_neg : (162823809 / 500000000) ≤ -Real.log (500000000000 / 692463629859) ∧
    -Real.log (500000000000 / 692463629859) ≤ (325647619 / 1000000000) := by
  have h := checkLog_sound (w := (192463629859 / 1192463629859)) (n := 12)
    (lo := (162823809 / 500000000)) (hi := (325647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692463629859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692463629859 / 500000000000) = 1/(500000000000 / 692463629859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1579 : Bounds (162823809 / 500000000) (325647619 / 1000000000) (Real.log (692463629859 / 500000000000)) := by
  have h := reflection_log_1579_neg
  have he : Real.log (692463629859 / 500000000000) = -Real.log (500000000000 / 692463629859) := by
    rw [show ((692463629859 / 500000000000) : ℝ) = ((500000000000 / 692463629859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1580_neg : (32585297 / 100000000) ≤ -Real.log (500000000000 / 692605843769) ∧
    -Real.log (500000000000 / 692605843769) ≤ (325852971 / 1000000000) := by
  have h := checkLog_sound (w := (192605843769 / 1192605843769)) (n := 12)
    (lo := (32585297 / 100000000)) (hi := (325852971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692605843769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692605843769 / 500000000000) = 1/(500000000000 / 692605843769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1580 : Bounds (32585297 / 100000000) (325852971 / 1000000000) (Real.log (692605843769 / 500000000000)) := by
  have h := reflection_log_1580_neg
  have he : Real.log (692605843769 / 500000000000) = -Real.log (500000000000 / 692605843769) := by
    rw [show ((692605843769 / 500000000000) : ℝ) = ((500000000000 / 692605843769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1581_neg : (29959673 / 200000000) ≤ -Real.log (625 / 726) ∧
    -Real.log (625 / 726) ≤ (74899183 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1351)) (n := 12)
    (lo := (29959673 / 200000000)) (hi := (74899183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726 / 625) = 1/(625 / 726) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1581 : Bounds (29959673 / 200000000) (74899183 / 500000000) (Real.log (726 / 625)) := by
  have h := reflection_log_1581_neg
  have he : Real.log (726 / 625) = -Real.log (625 / 726) := by
    rw [show ((726 / 625) : ℝ) = ((625 / 726) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1582_neg : (35251993 / 200000000) ≤ -Real.log (524 / 625) ∧
    -Real.log (524 / 625) ≤ (88129983 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1149)) (n := 12)
    (lo := (35251993 / 200000000)) (hi := (88129983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 524) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 524) = 1/(524 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1582 : Bounds (-88129983 / 500000000) (-35251993 / 200000000) (Real.log (524 / 625)) := by
  have h := reflection_log_1582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1583_neg : (80793 / 500000000) ≤ -Real.log (625000 / 625101) ∧
    -Real.log (625000 / 625101) ≤ (161587 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 1250101)) (n := 12)
    (lo := (80793 / 500000000)) (hi := (161587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625101 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625101 / 625000) = 1/(625000 / 625101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1583 : Bounds (80793 / 500000000) (161587 / 1000000000) (Real.log (625101 / 625000)) := by
  have h := reflection_log_1583_neg
  have he : Real.log (625101 / 625000) = -Real.log (625000 / 625101) := by
    rw [show ((625101 / 625000) : ℝ) = ((625000 / 625101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1584_neg : (161613 / 1000000000) ≤ -Real.log (624899 / 625000) ∧
    -Real.log (624899 / 625000) ≤ (80807 / 500000000) := by
  have h := checkLog_sound (w := (101 / 1249899)) (n := 12)
    (lo := (161613 / 1000000000)) (hi := (80807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624899) = 1/(624899 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1584 : Bounds (-80807 / 500000000) (-161613 / 1000000000) (Real.log (624899 / 625000)) := by
  have h := reflection_log_1584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1585_neg : (77934641 / 1000000000) ≤ -Real.log (250000 / 270263) ∧
    -Real.log (250000 / 270263) ≤ (38967321 / 500000000) := by
  have h := checkLog_sound (w := (20263 / 520263)) (n := 12)
    (lo := (77934641 / 1000000000)) (hi := (38967321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270263 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270263 / 250000) = 1/(250000 / 270263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1585 : Bounds (77934641 / 1000000000) (38967321 / 500000000) (Real.log (270263 / 250000)) := by
  have h := reflection_log_1585_neg
  have he : Real.log (270263 / 250000) = -Real.log (250000 / 270263) := by
    rw [show ((270263 / 250000) : ℝ) = ((250000 / 270263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1586_neg : (84525741 / 1000000000) ≤ -Real.log (229737 / 250000) ∧
    -Real.log (229737 / 250000) ≤ (42262871 / 500000000) := by
  have h := checkLog_sound (w := (20263 / 479737)) (n := 12)
    (lo := (84525741 / 1000000000)) (hi := (42262871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229737) = 1/(229737 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1586 : Bounds (-42262871 / 500000000) (-84525741 / 1000000000) (Real.log (229737 / 250000)) := by
  have h := reflection_log_1586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1587_neg : (78130727 / 1000000000) ≤ -Real.log (62500 / 67579) ∧
    -Real.log (62500 / 67579) ≤ (9766341 / 125000000) := by
  have h := checkLog_sound (w := (5079 / 130079)) (n := 12)
    (lo := (78130727 / 1000000000)) (hi := (9766341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67579 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67579 / 62500) = 1/(62500 / 67579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1587 : Bounds (78130727 / 1000000000) (9766341 / 125000000) (Real.log (67579 / 62500)) := by
  have h := reflection_log_1587_neg
  have he : Real.log (67579 / 62500) = -Real.log (62500 / 67579) := by
    rw [show ((67579 / 62500) : ℝ) = ((62500 / 67579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1588_neg : (42378233 / 500000000) ≤ -Real.log (57421 / 62500) ∧
    -Real.log (57421 / 62500) ≤ (84756467 / 1000000000) := by
  have h := checkLog_sound (w := (5079 / 119921)) (n := 12)
    (lo := (42378233 / 500000000)) (hi := (84756467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57421) = 1/(57421 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1588 : Bounds (-84756467 / 1000000000) (-42378233 / 500000000) (Real.log (57421 / 62500)) := by
  have h := reflection_log_1588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1589_neg : (6625739 / 1000000000) ≤ -Real.log (3880453759 / 3906250000) ∧
    -Real.log (3880453759 / 3906250000) ≤ (331287 / 50000000) := by
  have h := checkLog_sound (w := (25796241 / 7786703759)) (n := 12)
    (lo := (6625739 / 1000000000)) (hi := (331287 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3880453759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3880453759) = 1/(3880453759 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1589 : Bounds (-331287 / 50000000) (-6625739 / 1000000000) (Real.log (3880453759 / 3906250000)) := by
  have h := reflection_log_1589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1590_neg : (65911 / 10000000) ≤ -Real.log (62089410831 / 62500000000) ∧
    -Real.log (62089410831 / 62500000000) ≤ (6591101 / 1000000000) := by
  have h := checkLog_sound (w := (410589169 / 124589410831)) (n := 12)
    (lo := (65911 / 10000000)) (hi := (6591101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62089410831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62089410831) = 1/(62089410831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1590 : Bounds (-6591101 / 1000000000) (-65911 / 10000000) (Real.log (62089410831 / 62500000000)) := by
  have h := reflection_log_1590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1591_neg : (81230191 / 500000000) ≤ -Real.log (500000000000 / 588200855761) ∧
    -Real.log (500000000000 / 588200855761) ≤ (162460383 / 1000000000) := by
  have h := checkLog_sound (w := (88200855761 / 1088200855761)) (n := 12)
    (lo := (81230191 / 500000000)) (hi := (162460383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588200855761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588200855761 / 500000000000) = 1/(500000000000 / 588200855761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1591 : Bounds (81230191 / 500000000) (162460383 / 1000000000) (Real.log (588200855761 / 500000000000)) := by
  have h := reflection_log_1591_neg
  have he : Real.log (588200855761 / 500000000000) = -Real.log (500000000000 / 588200855761) := by
    rw [show ((588200855761 / 500000000000) : ℝ) = ((500000000000 / 588200855761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1592_neg : (162887193 / 1000000000) ≤ -Real.log (100000000000 / 117690392017) ∧
    -Real.log (100000000000 / 117690392017) ≤ (81443597 / 500000000) := by
  have h := checkLog_sound (w := (17690392017 / 217690392017)) (n := 12)
    (lo := (162887193 / 1000000000)) (hi := (81443597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117690392017 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117690392017 / 100000000000) = 1/(100000000000 / 117690392017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1592 : Bounds (162887193 / 1000000000) (81443597 / 500000000) (Real.log (117690392017 / 100000000000)) := by
  have h := reflection_log_1592_neg
  have he : Real.log (117690392017 / 100000000000) = -Real.log (100000000000 / 117690392017) := by
    rw [show ((117690392017 / 100000000000) : ℝ) = ((100000000000 / 117690392017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1593_neg : (32585297 / 100000000) ≤ -Real.log (62500000000 / 86575730471) ∧
    -Real.log (62500000000 / 86575730471) ≤ (325852971 / 1000000000) := by
  have h := checkLog_sound (w := (24075730471 / 149075730471)) (n := 12)
    (lo := (32585297 / 100000000)) (hi := (325852971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86575730471 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86575730471 / 62500000000) = 1/(62500000000 / 86575730471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1593 : Bounds (32585297 / 100000000) (325852971 / 1000000000) (Real.log (86575730471 / 62500000000)) := by
  have h := reflection_log_1593_neg
  have he : Real.log (86575730471 / 62500000000) = -Real.log (62500000000 / 86575730471) := by
    rw [show ((86575730471 / 62500000000) : ℝ) = ((62500000000 / 86575730471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1594_neg : (32605833 / 100000000) ≤ -Real.log (125000000000 / 173187022901) ∧
    -Real.log (125000000000 / 173187022901) ≤ (326058331 / 1000000000) := by
  have h := checkLog_sound (w := (48187022901 / 298187022901)) (n := 12)
    (lo := (32605833 / 100000000)) (hi := (326058331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173187022901 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173187022901 / 125000000000) = 1/(125000000000 / 173187022901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1594 : Bounds (32605833 / 100000000) (326058331 / 1000000000) (Real.log (173187022901 / 125000000000)) := by
  have h := reflection_log_1594_neg
  have he : Real.log (173187022901 / 125000000000) = -Real.log (125000000000 / 173187022901) := by
    rw [show ((173187022901 / 125000000000) : ℝ) = ((125000000000 / 173187022901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1595_neg : (149884449 / 1000000000) ≤ -Real.log (10000 / 11617) ∧
    -Real.log (10000 / 11617) ≤ (2997689 / 20000000) := by
  have h := checkLog_sound (w := (1617 / 21617)) (n := 12)
    (lo := (149884449 / 1000000000)) (hi := (2997689 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11617 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11617 / 10000) = 1/(10000 / 11617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1595 : Bounds (149884449 / 1000000000) (2997689 / 20000000) (Real.log (11617 / 10000)) := by
  have h := reflection_log_1595_neg
  have he : Real.log (11617 / 10000) = -Real.log (10000 / 11617) := by
    rw [show ((11617 / 10000) : ℝ) = ((10000 / 11617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1596_neg : (176379247 / 1000000000) ≤ -Real.log (8383 / 10000) ∧
    -Real.log (8383 / 10000) ≤ (11023703 / 62500000) := by
  have h := checkLog_sound (w := (1617 / 18383)) (n := 12)
    (lo := (176379247 / 1000000000)) (hi := (11023703 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8383) = 1/(8383 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1596 : Bounds (-11023703 / 62500000) (-176379247 / 1000000000) (Real.log (8383 / 10000)) := by
  have h := reflection_log_1596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1597_neg : (80843 / 500000000) ≤ -Real.log (10000000 / 10001617) ∧
    -Real.log (10000000 / 10001617) ≤ (161687 / 1000000000) := by
  have h := checkLog_sound (w := (1617 / 20001617)) (n := 12)
    (lo := (80843 / 500000000)) (hi := (161687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001617 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001617 / 10000000) = 1/(10000000 / 10001617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1597 : Bounds (80843 / 500000000) (161687 / 1000000000) (Real.log (10001617 / 10000000)) := by
  have h := reflection_log_1597_neg
  have he : Real.log (10001617 / 10000000) = -Real.log (10000000 / 10001617) := by
    rw [show ((10001617 / 10000000) : ℝ) = ((10000000 / 10001617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1598_neg : (161713 / 1000000000) ≤ -Real.log (9998383 / 10000000) ∧
    -Real.log (9998383 / 10000000) ≤ (80857 / 500000000) := by
  have h := checkLog_sound (w := (1617 / 19998383)) (n := 12)
    (lo := (161713 / 1000000000)) (hi := (80857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998383) = 1/(9998383 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1598 : Bounds (-80857 / 500000000) (-161713 / 1000000000) (Real.log (9998383 / 10000000)) := by
  have h := reflection_log_1598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1599_neg : (9747727 / 125000000) ≤ -Real.log (1000000 / 1081103) ∧
    -Real.log (1000000 / 1081103) ≤ (77981817 / 1000000000) := by
  have h := checkLog_sound (w := (81103 / 2081103)) (n := 12)
    (lo := (9747727 / 125000000)) (hi := (77981817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081103 / 1000000) = 1/(1000000 / 1081103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1599 : Bounds (9747727 / 125000000) (77981817 / 1000000000) (Real.log (1081103 / 1000000)) := by
  have h := reflection_log_1599_neg
  have he : Real.log (1081103 / 1000000) = -Real.log (1000000 / 1081103) := by
    rw [show ((1081103 / 1000000) : ℝ) = ((1000000 / 1081103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
