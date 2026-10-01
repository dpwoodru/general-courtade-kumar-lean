import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (153153193 / 500000000) ≤ -Real.log (1024 / 1391) ∧
    -Real.log (1024 / 1391) ≤ (306306387 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2415)) (n := 12)
    (lo := (153153193 / 500000000)) (hi := (306306387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1024) = 1/(1024 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (153153193 / 500000000) (306306387 / 1000000000) (Real.log (1391 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1391 / 1024) = -Real.log (1024 / 1391) := by
    rw [show ((1391 / 1024) : ℝ) = ((1024 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (443787787 / 1000000000) ≤ -Real.log (657 / 1024) ∧
    -Real.log (657 / 1024) ≤ (110946947 / 250000000) := by
  have h := checkLog_sound (w := (367 / 1681)) (n := 12)
    (lo := (443787787 / 1000000000)) (hi := (110946947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 657) = 1/(657 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-110946947 / 250000000) (-443787787 / 1000000000) (Real.log (657 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (76468737 / 250000000) ≤ -Real.log (640 / 869) ∧
    -Real.log (640 / 869) ≤ (305874949 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1509)) (n := 12)
    (lo := (76468737 / 250000000)) (hi := (305874949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869 / 640) = 1/(640 / 869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (76468737 / 250000000) (305874949 / 1000000000) (Real.log (869 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (869 / 640) = -Real.log (640 / 869) := by
    rw [show ((869 / 640) : ℝ) = ((640 / 869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (442874961 / 1000000000) ≤ -Real.log (411 / 640) ∧
    -Real.log (411 / 640) ≤ (221437481 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 411) = 1/(411 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-221437481 / 500000000) (-442874961 / 1000000000) (Real.log (411 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (226687663 / 1000000000) ≤ -Real.log (500000 / 627219) ∧
    -Real.log (500000 / 627219) ≤ (14167979 / 62500000) := by
  have h := checkLog_sound (w := (127219 / 1127219)) (n := 12)
    (lo := (226687663 / 1000000000)) (hi := (14167979 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627219 / 500000) = 1/(500000 / 627219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (226687663 / 1000000000) (14167979 / 62500000) (Real.log (627219 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (627219 / 500000) = -Real.log (500000 / 627219) := by
    rw [show ((627219 / 500000) : ℝ) = ((500000 / 627219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (146808491 / 500000000) ≤ -Real.log (372781 / 500000) ∧
    -Real.log (372781 / 500000) ≤ (293616983 / 1000000000) := by
  have h := checkLog_sound (w := (127219 / 872781)) (n := 12)
    (lo := (146808491 / 500000000)) (hi := (293616983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 372781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 372781) = 1/(372781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-293616983 / 1000000000) (-146808491 / 500000000) (Real.log (372781 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56756003 / 250000000) ≤ -Real.log (50000 / 62743) ∧
    -Real.log (50000 / 62743) ≤ (227024013 / 1000000000) := by
  have h := checkLog_sound (w := (12743 / 112743)) (n := 12)
    (lo := (56756003 / 250000000)) (hi := (227024013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62743 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62743 / 50000) = 1/(50000 / 62743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56756003 / 250000000) (227024013 / 1000000000) (Real.log (62743 / 50000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (62743 / 50000) = -Real.log (50000 / 62743) := by
    rw [show ((62743 / 50000) : ℝ) = ((50000 / 62743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (147091579 / 500000000) ≤ -Real.log (37257 / 50000) ∧
    -Real.log (37257 / 50000) ≤ (294183159 / 1000000000) := by
  have h := checkLog_sound (w := (12743 / 87257)) (n := 12)
    (lo := (147091579 / 500000000)) (hi := (294183159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37257) = 1/(37257 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-294183159 / 1000000000) (-147091579 / 500000000) (Real.log (37257 / 50000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21027829 / 125000000) ≤ -Real.log (1250 / 1479) ∧
    -Real.log (1250 / 1479) ≤ (168222633 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2729)) (n := 12)
    (lo := (21027829 / 125000000)) (hi := (168222633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479 / 1250) = 1/(1250 / 1479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21027829 / 125000000) (168222633 / 1000000000) (Real.log (1479 / 1250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1479 / 1250) = -Real.log (1250 / 1479) := by
    rw [show ((1479 / 1250) : ℝ) = ((1250 / 1479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (50590253 / 250000000) ≤ -Real.log (1021 / 1250) ∧
    -Real.log (1021 / 1250) ≤ (202361013 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2271)) (n := 12)
    (lo := (50590253 / 250000000)) (hi := (202361013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1021) = 1/(1021 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-202361013 / 1000000000) (-50590253 / 250000000) (Real.log (1021 / 1250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (168489669 / 1000000000) ≤ -Real.log (250000 / 295879) ∧
    -Real.log (250000 / 295879) ≤ (16848967 / 100000000) := by
  have h := checkLog_sound (w := (45879 / 545879)) (n := 12)
    (lo := (168489669 / 1000000000)) (hi := (16848967 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295879 / 250000) = 1/(250000 / 295879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (168489669 / 1000000000) (16848967 / 100000000) (Real.log (295879 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295879 / 250000) = -Real.log (250000 / 295879) := by
    rw [show ((295879 / 250000) : ℝ) = ((250000 / 295879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (101373981 / 500000000) ≤ -Real.log (204121 / 250000) ∧
    -Real.log (204121 / 250000) ≤ (202747963 / 1000000000) := by
  have h := checkLog_sound (w := (45879 / 454121)) (n := 12)
    (lo := (101373981 / 500000000)) (hi := (202747963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204121) = 1/(204121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-202747963 / 1000000000) (-101373981 / 500000000) (Real.log (204121 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (74874991 / 100000000) ≤ -Real.log (500000000000 / 1057177615571) ∧
    -Real.log (500000000000 / 1057177615571) ≤ (93593739 / 125000000) := by
  have h := checkLog_sound (w := (57177615571 / 2057177615571)) (n := 12)
    (lo := (5560273 / 100000000)) (hi := (55602731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057177615571 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057177615571 / 1000000000000) = 1/(500000000000 / 1057177615571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (74874991 / 100000000) (93593739 / 125000000) (Real.log (1057177615571 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1057177615571 / 500000000000) = -Real.log (500000000000 / 1057177615571) := by
    rw [show ((1057177615571 / 500000000000) : ℝ) = ((500000000000 / 1057177615571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (187523543 / 250000000) ≤ -Real.log (250000000000 / 529299847793) ∧
    -Real.log (250000000000 / 529299847793) ≤ (375047087 / 500000000) := by
  have h := checkLog_sound (w := (29299847793 / 1029299847793)) (n := 12)
    (lo := (3559187 / 62500000)) (hi := (56946993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529299847793 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529299847793 / 500000000000) = 1/(250000000000 / 529299847793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (187523543 / 250000000) (375047087 / 500000000) (Real.log (529299847793 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (529299847793 / 250000000000) = -Real.log (250000000000 / 529299847793) := by
    rw [show ((529299847793 / 250000000000) : ℝ) = ((250000000000 / 529299847793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (260152323 / 500000000) ≤ -Real.log (500000000000 / 841270075459) ∧
    -Real.log (500000000000 / 841270075459) ≤ (520304647 / 1000000000) := by
  have h := checkLog_sound (w := (341270075459 / 1341270075459)) (n := 12)
    (lo := (260152323 / 500000000)) (hi := (520304647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841270075459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841270075459 / 500000000000) = 1/(500000000000 / 841270075459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (260152323 / 500000000) (520304647 / 1000000000) (Real.log (841270075459 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (841270075459 / 500000000000) = -Real.log (500000000000 / 841270075459) := by
    rw [show ((841270075459 / 500000000000) : ℝ) = ((500000000000 / 841270075459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (521207171 / 1000000000) ≤ -Real.log (500000000000 / 842029685697) ∧
    -Real.log (500000000000 / 842029685697) ≤ (130301793 / 250000000) := by
  have h := checkLog_sound (w := (342029685697 / 1342029685697)) (n := 12)
    (lo := (521207171 / 1000000000)) (hi := (130301793 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842029685697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842029685697 / 500000000000) = 1/(500000000000 / 842029685697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (521207171 / 1000000000) (130301793 / 250000000) (Real.log (842029685697 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (842029685697 / 500000000000) = -Real.log (500000000000 / 842029685697) := by
    rw [show ((842029685697 / 500000000000) : ℝ) = ((500000000000 / 842029685697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (92645911 / 250000000) ≤ -Real.log (500000000000 / 724289911851) ∧
    -Real.log (500000000000 / 724289911851) ≤ (74116729 / 200000000) := by
  have h := checkLog_sound (w := (224289911851 / 1224289911851)) (n := 12)
    (lo := (92645911 / 250000000)) (hi := (74116729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724289911851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724289911851 / 500000000000) = 1/(500000000000 / 724289911851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92645911 / 250000000) (74116729 / 200000000) (Real.log (724289911851 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (724289911851 / 500000000000) = -Real.log (500000000000 / 724289911851) := by
    rw [show ((724289911851 / 500000000000) : ℝ) = ((500000000000 / 724289911851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (371237631 / 1000000000) ≤ -Real.log (250000000000 / 362381871537) ∧
    -Real.log (250000000000 / 362381871537) ≤ (1450147 / 3906250) := by
  have h := checkLog_sound (w := (112381871537 / 612381871537)) (n := 12)
    (lo := (371237631 / 1000000000)) (hi := (1450147 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362381871537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362381871537 / 250000000000) = 1/(250000000000 / 362381871537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (371237631 / 1000000000) (1450147 / 3906250) (Real.log (362381871537 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (362381871537 / 250000000000) = -Real.log (250000000000 / 362381871537) := by
    rw [show ((362381871537 / 250000000000) : ℝ) = ((250000000000 / 362381871537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34258293 / 1000000000) ≤ -Real.log (60395117359 / 62500000000) ∧
    -Real.log (60395117359 / 62500000000) ≤ (17129147 / 500000000) := by
  have h := checkLog_sound (w := (2104882641 / 122895117359)) (n := 12)
    (lo := (34258293 / 1000000000)) (hi := (17129147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60395117359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60395117359) = 1/(60395117359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17129147 / 500000000) (-34258293 / 1000000000) (Real.log (60395117359 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (34138379 / 1000000000) ≤ -Real.log (1510059 / 1562500) ∧
    -Real.log (1510059 / 1562500) ≤ (1706919 / 50000000) := by
  have h := checkLog_sound (w := (52441 / 3072559)) (n := 12)
    (lo := (34138379 / 1000000000)) (hi := (1706919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562500 / 1510059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562500 / 1510059) = 1/(1510059 / 1562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1706919 / 50000000) (-34138379 / 1000000000) (Real.log (1510059 / 1562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell184
