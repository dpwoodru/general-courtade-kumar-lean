import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0361
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

theorem reflection_log_1_neg : (104767879 / 500000000) ≤ -Real.log (10240 / 12627) ∧
    -Real.log (10240 / 12627) ≤ (209535759 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 22867)) (n := 12)
    (lo := (104767879 / 500000000)) (hi := (209535759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12627 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12627 / 10240) = 1/(10240 / 12627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104767879 / 500000000) (209535759 / 1000000000) (Real.log (12627 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12627 / 10240) = -Real.log (10240 / 12627) := by
    rw [show ((12627 / 10240) : ℝ) = ((10240 / 12627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53081199 / 200000000) ≤ -Real.log (7853 / 10240) ∧
    -Real.log (7853 / 10240) ≤ (66351499 / 250000000) := by
  have h := checkLog_sound (w := (2387 / 18093)) (n := 12)
    (lo := (53081199 / 200000000)) (hi := (66351499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7853) = 1/(7853 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-66351499 / 250000000) (-53081199 / 200000000) (Real.log (7853 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6540567 / 31250000) ≤ -Real.log (640 / 789) ∧
    -Real.log (640 / 789) ≤ (41859629 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1429)) (n := 12)
    (lo := (6540567 / 31250000)) (hi := (41859629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789 / 640) = 1/(640 / 789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6540567 / 31250000) (41859629 / 200000000) (Real.log (789 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (789 / 640) = -Real.log (640 / 789) := by
    rw [show ((789 / 640) : ℝ) = ((640 / 789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16564003 / 62500000) ≤ -Real.log (491 / 640) ∧
    -Real.log (491 / 640) ≤ (265024049 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1131)) (n := 12)
    (lo := (16564003 / 62500000)) (hi := (265024049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 491) = 1/(491 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-265024049 / 1000000000) (-16564003 / 62500000) (Real.log (491 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (382681479 / 1000000000) ≤ -Real.log (5120 / 7507) ∧
    -Real.log (5120 / 7507) ≤ (9567037 / 25000000) := by
  have h := checkLog_sound (w := (2387 / 12627)) (n := 12)
    (lo := (382681479 / 1000000000)) (hi := (9567037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7507 / 5120) = 1/(5120 / 7507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (382681479 / 1000000000) (9567037 / 25000000) (Real.log (7507 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7507 / 5120) = -Real.log (5120 / 7507) := by
    rw [show ((7507 / 5120) : ℝ) = ((5120 / 7507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156938633 / 250000000) ≤ -Real.log (2733 / 5120) ∧
    -Real.log (2733 / 5120) ≤ (627754533 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 7853)) (n := 12)
    (lo := (156938633 / 250000000)) (hi := (627754533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2733) = 1/(2733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-627754533 / 1000000000) (-156938633 / 250000000) (Real.log (2733 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95570443 / 250000000) ≤ -Real.log (320 / 469) ∧
    -Real.log (320 / 469) ≤ (382281773 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 789)) (n := 12)
    (lo := (95570443 / 250000000)) (hi := (382281773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469 / 320) = 1/(320 / 469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95570443 / 250000000) (382281773 / 1000000000) (Real.log (469 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (469 / 320) = -Real.log (320 / 469) := by
    rw [show ((469 / 320) : ℝ) = ((320 / 469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (626657439 / 1000000000) ≤ -Real.log (171 / 320) ∧
    -Real.log (171 / 320) ≤ (3916609 / 6250000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 171) = 1/(171 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3916609 / 6250000) (-626657439 / 1000000000) (Real.log (171 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35884361 / 125000000) ≤ -Real.log (250000 / 333131) ∧
    -Real.log (250000 / 333131) ≤ (287074889 / 1000000000) := by
  have h := checkLog_sound (w := (83131 / 583131)) (n := 12)
    (lo := (35884361 / 125000000)) (hi := (287074889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333131 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333131 / 250000) = 1/(250000 / 333131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35884361 / 125000000) (287074889 / 1000000000) (Real.log (333131 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (333131 / 250000) = -Real.log (250000 / 333131) := by
    rw [show ((333131 / 250000) : ℝ) = ((250000 / 333131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101062961 / 250000000) ≤ -Real.log (166869 / 250000) ∧
    -Real.log (166869 / 250000) ≤ (80850369 / 200000000) := by
  have h := checkLog_sound (w := (83131 / 416869)) (n := 12)
    (lo := (101062961 / 250000000)) (hi := (80850369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 166869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 166869) = 1/(166869 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-80850369 / 200000000) (-101062961 / 250000000) (Real.log (166869 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (287396031 / 1000000000) ≤ -Real.log (125000 / 166619) ∧
    -Real.log (125000 / 166619) ≤ (4490563 / 15625000) := by
  have h := checkLog_sound (w := (41619 / 291619)) (n := 12)
    (lo := (287396031 / 1000000000)) (hi := (4490563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166619 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166619 / 125000) = 1/(125000 / 166619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (287396031 / 1000000000) (4490563 / 15625000) (Real.log (166619 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (166619 / 125000) = -Real.log (125000 / 166619) := by
    rw [show ((166619 / 125000) : ℝ) = ((125000 / 166619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (404893271 / 1000000000) ≤ -Real.log (83381 / 125000) ∧
    -Real.log (83381 / 125000) ≤ (50611659 / 125000000) := by
  have h := checkLog_sound (w := (41619 / 208381)) (n := 12)
    (lo := (404893271 / 1000000000)) (hi := (50611659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 83381) = 1/(83381 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50611659 / 125000000) (-404893271 / 1000000000) (Real.log (83381 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (217167329 / 1000000000) ≤ -Real.log (125000 / 155319) ∧
    -Real.log (125000 / 155319) ≤ (21716733 / 100000000) := by
  have h := checkLog_sound (w := (30319 / 280319)) (n := 12)
    (lo := (217167329 / 1000000000)) (hi := (21716733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155319 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155319 / 125000) = 1/(125000 / 155319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (217167329 / 1000000000) (21716733 / 100000000) (Real.log (155319 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (155319 / 125000) = -Real.log (125000 / 155319) := by
    rw [show ((155319 / 125000) : ℝ) = ((125000 / 155319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27780039 / 100000000) ≤ -Real.log (94681 / 125000) ∧
    -Real.log (94681 / 125000) ≤ (277800391 / 1000000000) := by
  have h := checkLog_sound (w := (30319 / 219681)) (n := 12)
    (lo := (27780039 / 100000000)) (hi := (277800391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94681) = 1/(94681 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-277800391 / 1000000000) (-27780039 / 100000000) (Real.log (94681 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21743529 / 100000000) ≤ -Real.log (200000 / 248577) ∧
    -Real.log (200000 / 248577) ≤ (217435291 / 1000000000) := by
  have h := checkLog_sound (w := (48577 / 448577)) (n := 12)
    (lo := (21743529 / 100000000)) (hi := (217435291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248577 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248577 / 200000) = 1/(200000 / 248577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21743529 / 100000000) (217435291 / 1000000000) (Real.log (248577 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (248577 / 200000) = -Real.log (200000 / 248577) := by
    rw [show ((248577 / 200000) : ℝ) = ((200000 / 248577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (278240121 / 1000000000) ≤ -Real.log (151423 / 200000) ∧
    -Real.log (151423 / 200000) ≤ (139120061 / 500000000) := by
  have h := checkLog_sound (w := (48577 / 351423)) (n := 12)
    (lo := (278240121 / 1000000000)) (hi := (139120061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151423) = 1/(151423 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-139120061 / 500000000) (-278240121 / 1000000000) (Real.log (151423 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (172831683 / 250000000) ≤ -Real.log (500000000000 / 998181208013) ∧
    -Real.log (500000000000 / 998181208013) ≤ (691326733 / 1000000000) := by
  have h := checkLog_sound (w := (498181208013 / 1498181208013)) (n := 12)
    (lo := (172831683 / 250000000)) (hi := (691326733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((998181208013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(998181208013 / 500000000000) = 1/(500000000000 / 998181208013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (172831683 / 250000000) (691326733 / 1000000000) (Real.log (998181208013 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (998181208013 / 500000000000) = -Real.log (500000000000 / 998181208013) := by
    rw [show ((998181208013 / 500000000000) : ℝ) = ((500000000000 / 998181208013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (692289303 / 1000000000) ≤ -Real.log (3906250000 / 7805800707) ∧
    -Real.log (3906250000 / 7805800707) ≤ (86536163 / 125000000) := by
  have h := checkLog_sound (w := (3899550707 / 11712050707)) (n := 12)
    (lo := (692289303 / 1000000000)) (hi := (86536163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7805800707 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7805800707 / 3906250000) = 1/(3906250000 / 7805800707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (692289303 / 1000000000) (86536163 / 125000000) (Real.log (7805800707 / 3906250000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7805800707 / 3906250000) = -Real.log (3906250000 / 7805800707) := by
    rw [show ((7805800707 / 3906250000) : ℝ) = ((3906250000 / 7805800707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12374193 / 25000000) ≤ -Real.log (250000000000 / 410111321173) ∧
    -Real.log (250000000000 / 410111321173) ≤ (494967721 / 1000000000) := by
  have h := checkLog_sound (w := (160111321173 / 660111321173)) (n := 12)
    (lo := (12374193 / 25000000)) (hi := (494967721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410111321173 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410111321173 / 250000000000) = 1/(250000000000 / 410111321173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (12374193 / 25000000) (494967721 / 1000000000) (Real.log (410111321173 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (410111321173 / 250000000000) = -Real.log (250000000000 / 410111321173) := by
    rw [show ((410111321173 / 250000000000) : ℝ) = ((250000000000 / 410111321173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (495675411 / 1000000000) ≤ -Real.log (20000000000 / 32832132503) ∧
    -Real.log (20000000000 / 32832132503) ≤ (123918853 / 250000000) := by
  have h := checkLog_sound (w := (12832132503 / 52832132503)) (n := 12)
    (lo := (495675411 / 1000000000)) (hi := (123918853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32832132503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32832132503 / 20000000000) = 1/(20000000000 / 32832132503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (495675411 / 1000000000) (123918853 / 250000000) (Real.log (32832132503 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (32832132503 / 20000000000) = -Real.log (20000000000 / 32832132503) := by
    rw [show ((32832132503 / 20000000000) : ℝ) = ((20000000000 / 32832132503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0361
