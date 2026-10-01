import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7936_neg : (53575889 / 200000000) ≤ -Real.log (153 / 200) ∧
    -Real.log (153 / 200) ≤ (133939723 / 500000000) := by
  have h := checkLog_sound (w := (47 / 353)) (n := 12)
    (lo := (53575889 / 200000000)) (hi := (133939723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 153) = 1/(153 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7936 : Bounds (-133939723 / 500000000) (-53575889 / 200000000) (Real.log (153 / 200)) := by
  have h := reflection_log_7936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7937_neg : (58743 / 250000000) ≤ -Real.log (200000 / 200047) ∧
    -Real.log (200000 / 200047) ≤ (234973 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 400047)) (n := 12)
    (lo := (58743 / 250000000)) (hi := (234973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200047 / 200000) = 1/(200000 / 200047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7937 : Bounds (58743 / 250000000) (234973 / 1000000000) (Real.log (200047 / 200000)) := by
  have h := reflection_log_7937_neg
  have he : Real.log (200047 / 200000) = -Real.log (200000 / 200047) := by
    rw [show ((200047 / 200000) : ℝ) = ((200000 / 200047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7938_neg : (235027 / 1000000000) ≤ -Real.log (199953 / 200000) ∧
    -Real.log (199953 / 200000) ≤ (58757 / 250000000) := by
  have h := checkLog_sound (w := (47 / 399953)) (n := 12)
    (lo := (235027 / 1000000000)) (hi := (58757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199953) = 1/(199953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7938 : Bounds (-58757 / 250000000) (-235027 / 1000000000) (Real.log (199953 / 200000)) := by
  have h := reflection_log_7938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7939_neg : (6988943 / 62500000) ≤ -Real.log (200000 / 223663) ∧
    -Real.log (200000 / 223663) ≤ (111823089 / 1000000000) := by
  have h := checkLog_sound (w := (23663 / 423663)) (n := 12)
    (lo := (6988943 / 62500000)) (hi := (111823089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223663 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223663 / 200000) = 1/(200000 / 223663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7939 : Bounds (6988943 / 62500000) (111823089 / 1000000000) (Real.log (223663 / 200000)) := by
  have h := reflection_log_7939_neg
  have he : Real.log (223663 / 200000) = -Real.log (200000 / 223663) := by
    rw [show ((223663 / 200000) : ℝ) = ((200000 / 223663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7940_neg : (125920429 / 1000000000) ≤ -Real.log (176337 / 200000) ∧
    -Real.log (176337 / 200000) ≤ (12592043 / 100000000) := by
  have h := checkLog_sound (w := (23663 / 376337)) (n := 12)
    (lo := (125920429 / 1000000000)) (hi := (12592043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 176337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 176337) = 1/(176337 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7940 : Bounds (-12592043 / 100000000) (-125920429 / 1000000000) (Real.log (176337 / 200000)) := by
  have h := reflection_log_7940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7941_neg : (22452409 / 200000000) ≤ -Real.log (500000 / 559403) ∧
    -Real.log (500000 / 559403) ≤ (56131023 / 500000000) := by
  have h := checkLog_sound (w := (59403 / 1059403)) (n := 12)
    (lo := (22452409 / 200000000)) (hi := (56131023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559403 / 500000) = 1/(500000 / 559403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7941 : Bounds (22452409 / 200000000) (56131023 / 500000000) (Real.log (559403 / 500000)) := by
  have h := reflection_log_7941_neg
  have he : Real.log (559403 / 500000) = -Real.log (500000 / 559403) := by
    rw [show ((559403 / 500000) : ℝ) = ((500000 / 559403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7942_neg : (3952421 / 31250000) ≤ -Real.log (440597 / 500000) ∧
    -Real.log (440597 / 500000) ≤ (126477473 / 1000000000) := by
  have h := checkLog_sound (w := (59403 / 940597)) (n := 12)
    (lo := (3952421 / 31250000)) (hi := (126477473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440597) = 1/(440597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7942 : Bounds (-126477473 / 1000000000) (-3952421 / 31250000) (Real.log (440597 / 500000)) := by
  have h := reflection_log_7942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7943_neg : (14215427 / 1000000000) ≤ -Real.log (246471283591 / 250000000000) ∧
    -Real.log (246471283591 / 250000000000) ≤ (3553857 / 250000000) := by
  have h := checkLog_sound (w := (3528716409 / 496471283591)) (n := 12)
    (lo := (14215427 / 1000000000)) (hi := (3553857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246471283591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246471283591) = 1/(246471283591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7943 : Bounds (-3553857 / 250000000) (-14215427 / 1000000000) (Real.log (246471283591 / 250000000000)) := by
  have h := reflection_log_7943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7944_neg : (14097341 / 1000000000) ≤ -Real.log (39440062431 / 40000000000) ∧
    -Real.log (39440062431 / 40000000000) ≤ (7048671 / 500000000) := by
  have h := checkLog_sound (w := (559937569 / 79440062431)) (n := 12)
    (lo := (14097341 / 1000000000)) (hi := (7048671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39440062431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39440062431) = 1/(39440062431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7944 : Bounds (-7048671 / 500000000) (-14097341 / 1000000000) (Real.log (39440062431 / 40000000000)) := by
  have h := reflection_log_7944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7945_neg : (237743517 / 1000000000) ≤ -Real.log (250000000000 / 317095958307) ∧
    -Real.log (250000000000 / 317095958307) ≤ (118871759 / 500000000) := by
  have h := checkLog_sound (w := (67095958307 / 567095958307)) (n := 12)
    (lo := (237743517 / 1000000000)) (hi := (118871759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317095958307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317095958307 / 250000000000) = 1/(250000000000 / 317095958307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7945 : Bounds (237743517 / 1000000000) (118871759 / 500000000) (Real.log (317095958307 / 250000000000)) := by
  have h := reflection_log_7945_neg
  have he : Real.log (317095958307 / 250000000000) = -Real.log (250000000000 / 317095958307) := by
    rw [show ((317095958307 / 250000000000) : ℝ) = ((250000000000 / 317095958307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7946_neg : (119369759 / 500000000) ≤ -Real.log (250000000000 / 317411943341) ∧
    -Real.log (250000000000 / 317411943341) ≤ (238739519 / 1000000000) := by
  have h := checkLog_sound (w := (67411943341 / 567411943341)) (n := 12)
    (lo := (119369759 / 500000000)) (hi := (238739519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317411943341 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317411943341 / 250000000000) = 1/(250000000000 / 317411943341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7946 : Bounds (119369759 / 500000000) (238739519 / 1000000000) (Real.log (317411943341 / 250000000000)) := by
  have h := reflection_log_7946_neg
  have he : Real.log (317411943341 / 250000000000) = -Real.log (250000000000 / 317411943341) := by
    rw [show ((317411943341 / 250000000000) : ℝ) = ((250000000000 / 317411943341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7947_neg : (477892093 / 1000000000) ≤ -Real.log (250000000000 / 403167864141) ∧
    -Real.log (250000000000 / 403167864141) ≤ (238946047 / 500000000) := by
  have h := checkLog_sound (w := (153167864141 / 653167864141)) (n := 12)
    (lo := (477892093 / 1000000000)) (hi := (238946047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403167864141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403167864141 / 250000000000) = 1/(250000000000 / 403167864141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7947 : Bounds (477892093 / 1000000000) (238946047 / 500000000) (Real.log (403167864141 / 250000000000)) := by
  have h := reflection_log_7947_neg
  have he : Real.log (403167864141 / 250000000000) = -Real.log (250000000000 / 403167864141) := by
    rw [show ((403167864141 / 250000000000) : ℝ) = ((250000000000 / 403167864141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7948_neg : (95790083 / 200000000) ≤ -Real.log (125000000000 / 201797385621) ∧
    -Real.log (125000000000 / 201797385621) ≤ (29934401 / 62500000) := by
  have h := checkLog_sound (w := (76797385621 / 326797385621)) (n := 12)
    (lo := (95790083 / 200000000)) (hi := (29934401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201797385621 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201797385621 / 125000000000) = 1/(125000000000 / 201797385621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7948 : Bounds (95790083 / 200000000) (29934401 / 62500000) (Real.log (201797385621 / 125000000000)) := by
  have h := reflection_log_7948_neg
  have he : Real.log (201797385621 / 125000000000) = -Real.log (125000000000 / 201797385621) := by
    rw [show ((201797385621 / 125000000000) : ℝ) = ((125000000000 / 201797385621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7949_neg : (105737873 / 500000000) ≤ -Real.log (2000 / 2471) ∧
    -Real.log (2000 / 2471) ≤ (211475747 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 4471)) (n := 12)
    (lo := (105737873 / 500000000)) (hi := (211475747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2471 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2471 / 2000) = 1/(2000 / 2471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7949 : Bounds (105737873 / 500000000) (211475747 / 1000000000) (Real.log (2471 / 2000)) := by
  have h := reflection_log_7949_neg
  have he : Real.log (2471 / 2000) = -Real.log (2000 / 2471) := by
    rw [show ((2471 / 2000) : ℝ) = ((2000 / 2471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7950_neg : (268533253 / 1000000000) ≤ -Real.log (1529 / 2000) ∧
    -Real.log (1529 / 2000) ≤ (134266627 / 500000000) := by
  have h := checkLog_sound (w := (471 / 3529)) (n := 12)
    (lo := (268533253 / 1000000000)) (hi := (134266627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1529) = 1/(1529 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7950 : Bounds (-134266627 / 500000000) (-268533253 / 1000000000) (Real.log (1529 / 2000)) := by
  have h := reflection_log_7950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7951_neg : (14717 / 62500000) ≤ -Real.log (2000000 / 2000471) ∧
    -Real.log (2000000 / 2000471) ≤ (235473 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 4000471)) (n := 12)
    (lo := (14717 / 62500000)) (hi := (235473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000471 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000471 / 2000000) = 1/(2000000 / 2000471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7951 : Bounds (14717 / 62500000) (235473 / 1000000000) (Real.log (2000471 / 2000000)) := by
  have h := reflection_log_7951_neg
  have he : Real.log (2000471 / 2000000) = -Real.log (2000000 / 2000471) := by
    rw [show ((2000471 / 2000000) : ℝ) = ((2000000 / 2000471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7952_neg : (235527 / 1000000000) ≤ -Real.log (1999529 / 2000000) ∧
    -Real.log (1999529 / 2000000) ≤ (29441 / 125000000) := by
  have h := checkLog_sound (w := (471 / 3999529)) (n := 12)
    (lo := (235527 / 1000000000)) (hi := (29441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999529) = 1/(1999529 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7952 : Bounds (-29441 / 125000000) (-235527 / 1000000000) (Real.log (1999529 / 2000000)) := by
  have h := reflection_log_7952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7953_neg : (22410753 / 200000000) ≤ -Real.log (1000000 / 1118573) ∧
    -Real.log (1000000 / 1118573) ≤ (56026883 / 500000000) := by
  have h := checkLog_sound (w := (118573 / 2118573)) (n := 12)
    (lo := (22410753 / 200000000)) (hi := (56026883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1118573 / 1000000) = 1/(1000000 / 1118573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7953 : Bounds (22410753 / 200000000) (56026883 / 500000000) (Real.log (1118573 / 1000000)) := by
  have h := reflection_log_7953_neg
  have he : Real.log (1118573 / 1000000) = -Real.log (1000000 / 1118573) := by
    rw [show ((1118573 / 1000000) : ℝ) = ((1000000 / 1118573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7954_neg : (126213093 / 1000000000) ≤ -Real.log (881427 / 1000000) ∧
    -Real.log (881427 / 1000000) ≤ (63106547 / 500000000) := by
  have h := checkLog_sound (w := (118573 / 1881427)) (n := 12)
    (lo := (126213093 / 1000000000)) (hi := (63106547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 881427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 881427) = 1/(881427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7954 : Bounds (-63106547 / 500000000) (-126213093 / 1000000000) (Real.log (881427 / 1000000)) := by
  have h := reflection_log_7954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7955_neg : (112492621 / 1000000000) ≤ -Real.log (125000 / 139883) ∧
    -Real.log (125000 / 139883) ≤ (56246311 / 500000000) := by
  have h := checkLog_sound (w := (14883 / 264883)) (n := 12)
    (lo := (112492621 / 1000000000)) (hi := (56246311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139883 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139883 / 125000) = 1/(125000 / 139883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7955 : Bounds (112492621 / 1000000000) (56246311 / 500000000) (Real.log (139883 / 125000)) := by
  have h := reflection_log_7955_neg
  have he : Real.log (139883 / 125000) = -Real.log (125000 / 139883) := by
    rw [show ((139883 / 125000) : ℝ) = ((125000 / 139883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7956_neg : (1267703 / 10000000) ≤ -Real.log (110117 / 125000) ∧
    -Real.log (110117 / 125000) ≤ (126770301 / 1000000000) := by
  have h := checkLog_sound (w := (14883 / 235117)) (n := 12)
    (lo := (1267703 / 10000000)) (hi := (126770301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 110117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 110117) = 1/(110117 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7956 : Bounds (-126770301 / 1000000000) (-1267703 / 10000000) (Real.log (110117 / 125000)) := by
  have h := reflection_log_7956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7957_neg : (7138839 / 500000000) ≤ -Real.log (15403496311 / 15625000000) ∧
    -Real.log (15403496311 / 15625000000) ≤ (14277679 / 1000000000) := by
  have h := checkLog_sound (w := (221503689 / 31028496311)) (n := 12)
    (lo := (7138839 / 500000000)) (hi := (14277679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15403496311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15403496311) = 1/(15403496311 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7957 : Bounds (-14277679 / 1000000000) (-7138839 / 500000000) (Real.log (15403496311 / 15625000000)) := by
  have h := reflection_log_7957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7958_neg : (442479 / 31250000) ≤ -Real.log (985940443671 / 1000000000000) ∧
    -Real.log (985940443671 / 1000000000000) ≤ (14159329 / 1000000000) := by
  have h := checkLog_sound (w := (14059556329 / 1985940443671)) (n := 12)
    (lo := (442479 / 31250000)) (hi := (14159329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985940443671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985940443671) = 1/(985940443671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7958 : Bounds (-14159329 / 1000000000) (-442479 / 31250000) (Real.log (985940443671 / 1000000000000)) := by
  have h := reflection_log_7958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7959_neg : (238266859 / 1000000000) ≤ -Real.log (125000000000 / 158630975679) ∧
    -Real.log (125000000000 / 158630975679) ≤ (11913343 / 50000000) := by
  have h := checkLog_sound (w := (33630975679 / 283630975679)) (n := 12)
    (lo := (238266859 / 1000000000)) (hi := (11913343 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158630975679 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158630975679 / 125000000000) = 1/(125000000000 / 158630975679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7959 : Bounds (238266859 / 1000000000) (11913343 / 50000000) (Real.log (158630975679 / 125000000000)) := by
  have h := reflection_log_7959_neg
  have he : Real.log (158630975679 / 125000000000) = -Real.log (125000000000 / 158630975679) := by
    rw [show ((158630975679 / 125000000000) : ℝ) = ((125000000000 / 158630975679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7960_neg : (119631461 / 500000000) ≤ -Real.log (250000000000 / 317578121453) ∧
    -Real.log (250000000000 / 317578121453) ≤ (239262923 / 1000000000) := by
  have h := checkLog_sound (w := (67578121453 / 567578121453)) (n := 12)
    (lo := (119631461 / 500000000)) (hi := (239262923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317578121453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317578121453 / 250000000000) = 1/(250000000000 / 317578121453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7960 : Bounds (119631461 / 500000000) (239262923 / 1000000000) (Real.log (317578121453 / 250000000000)) := by
  have h := reflection_log_7960_neg
  have he : Real.log (317578121453 / 250000000000) = -Real.log (250000000000 / 317578121453) := by
    rw [show ((317578121453 / 250000000000) : ℝ) = ((250000000000 / 317578121453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7961_neg : (95790083 / 200000000) ≤ -Real.log (500000000000 / 807189542483) ∧
    -Real.log (500000000000 / 807189542483) ≤ (29934401 / 62500000) := by
  have h := checkLog_sound (w := (307189542483 / 1307189542483)) (n := 12)
    (lo := (95790083 / 200000000)) (hi := (29934401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807189542483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807189542483 / 500000000000) = 1/(500000000000 / 807189542483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7961 : Bounds (95790083 / 200000000) (29934401 / 62500000) (Real.log (807189542483 / 500000000000)) := by
  have h := reflection_log_7961_neg
  have he : Real.log (807189542483 / 500000000000) = -Real.log (500000000000 / 807189542483) := by
    rw [show ((807189542483 / 500000000000) : ℝ) = ((500000000000 / 807189542483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7962_neg : (480009 / 1000000) ≤ -Real.log (500000000000 / 808044473513) ∧
    -Real.log (500000000000 / 808044473513) ≤ (480009001 / 1000000000) := by
  have h := checkLog_sound (w := (308044473513 / 1308044473513)) (n := 12)
    (lo := (480009 / 1000000)) (hi := (480009001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808044473513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808044473513 / 500000000000) = 1/(500000000000 / 808044473513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7962 : Bounds (480009 / 1000000) (480009001 / 1000000000) (Real.log (808044473513 / 500000000000)) := by
  have h := reflection_log_7962_neg
  have he : Real.log (808044473513 / 500000000000) = -Real.log (500000000000 / 808044473513) := by
    rw [show ((808044473513 / 500000000000) : ℝ) = ((500000000000 / 808044473513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7963_neg : (211880359 / 1000000000) ≤ -Real.log (250 / 309) ∧
    -Real.log (250 / 309) ≤ (5297009 / 25000000) := by
  have h := checkLog_sound (w := (59 / 559)) (n := 12)
    (lo := (211880359 / 1000000000)) (hi := (5297009 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 250) = 1/(250 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7963 : Bounds (211880359 / 1000000000) (5297009 / 25000000) (Real.log (309 / 250)) := by
  have h := reflection_log_7963_neg
  have he : Real.log (309 / 250) = -Real.log (250 / 309) := by
    rw [show ((309 / 250) : ℝ) = ((250 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7964_neg : (269187489 / 1000000000) ≤ -Real.log (191 / 250) ∧
    -Real.log (191 / 250) ≤ (26918749 / 100000000) := by
  have h := checkLog_sound (w := (59 / 441)) (n := 12)
    (lo := (269187489 / 1000000000)) (hi := (26918749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 191) = 1/(191 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7964 : Bounds (-26918749 / 100000000) (-269187489 / 1000000000) (Real.log (191 / 250)) := by
  have h := reflection_log_7964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7965_neg : (58993 / 250000000) ≤ -Real.log (250000 / 250059) ∧
    -Real.log (250000 / 250059) ≤ (235973 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 500059)) (n := 12)
    (lo := (58993 / 250000000)) (hi := (235973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250059 / 250000) = 1/(250000 / 250059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7965 : Bounds (58993 / 250000000) (235973 / 1000000000) (Real.log (250059 / 250000)) := by
  have h := reflection_log_7965_neg
  have he : Real.log (250059 / 250000) = -Real.log (250000 / 250059) := by
    rw [show ((250059 / 250000) : ℝ) = ((250000 / 250059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7966_neg : (236027 / 1000000000) ≤ -Real.log (249941 / 250000) ∧
    -Real.log (249941 / 250000) ≤ (59007 / 250000000) := by
  have h := checkLog_sound (w := (59 / 499941)) (n := 12)
    (lo := (236027 / 1000000000)) (hi := (59007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249941) = 1/(249941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7966 : Bounds (-59007 / 250000000) (-236027 / 1000000000) (Real.log (249941 / 250000)) := by
  have h := reflection_log_7966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7967_neg : (14035437 / 125000000) ≤ -Real.log (100000 / 111883) ∧
    -Real.log (100000 / 111883) ≤ (112283497 / 1000000000) := by
  have h := checkLog_sound (w := (11883 / 211883)) (n := 12)
    (lo := (14035437 / 125000000)) (hi := (112283497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111883 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111883 / 100000) = 1/(100000 / 111883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7967 : Bounds (14035437 / 125000000) (112283497 / 1000000000) (Real.log (111883 / 100000)) := by
  have h := reflection_log_7967_neg
  have he : Real.log (111883 / 100000) = -Real.log (100000 / 111883) := by
    rw [show ((111883 / 100000) : ℝ) = ((100000 / 111883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7968_neg : (126504709 / 1000000000) ≤ -Real.log (88117 / 100000) ∧
    -Real.log (88117 / 100000) ≤ (12650471 / 100000000) := by
  have h := checkLog_sound (w := (11883 / 188117)) (n := 12)
    (lo := (126504709 / 1000000000)) (hi := (12650471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 88117) = 1/(88117 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7968 : Bounds (-12650471 / 100000000) (-126504709 / 1000000000) (Real.log (88117 / 100000)) := by
  have h := reflection_log_7968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7969_neg : (14090393 / 125000000) ≤ -Real.log (500000 / 559661) ∧
    -Real.log (500000 / 559661) ≤ (22544629 / 200000000) := by
  have h := checkLog_sound (w := (59661 / 1059661)) (n := 12)
    (lo := (14090393 / 125000000)) (hi := (22544629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559661 / 500000) = 1/(500000 / 559661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7969 : Bounds (14090393 / 125000000) (22544629 / 200000000) (Real.log (559661 / 500000)) := by
  have h := reflection_log_7969_neg
  have he : Real.log (559661 / 500000) = -Real.log (500000 / 559661) := by
    rw [show ((559661 / 500000) : ℝ) = ((500000 / 559661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7970_neg : (127063213 / 1000000000) ≤ -Real.log (440339 / 500000) ∧
    -Real.log (440339 / 500000) ≤ (63531607 / 500000000) := by
  have h := checkLog_sound (w := (59661 / 940339)) (n := 12)
    (lo := (127063213 / 1000000000)) (hi := (63531607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440339) = 1/(440339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7970 : Bounds (-63531607 / 500000000) (-127063213 / 1000000000) (Real.log (440339 / 500000)) := by
  have h := reflection_log_7970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7971_neg : (3585017 / 250000000) ≤ -Real.log (246440565079 / 250000000000) ∧
    -Real.log (246440565079 / 250000000000) ≤ (14340069 / 1000000000) := by
  have h := checkLog_sound (w := (3559434921 / 496440565079)) (n := 12)
    (lo := (3585017 / 250000000)) (hi := (14340069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246440565079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246440565079) = 1/(246440565079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7971 : Bounds (-14340069 / 1000000000) (-3585017 / 250000000) (Real.log (246440565079 / 250000000000)) := by
  have h := reflection_log_7971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7972_neg : (3555303 / 250000000) ≤ -Real.log (9858794311 / 10000000000) ∧
    -Real.log (9858794311 / 10000000000) ≤ (14221213 / 1000000000) := by
  have h := checkLog_sound (w := (141205689 / 19858794311)) (n := 12)
    (lo := (3555303 / 250000000)) (hi := (14221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9858794311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9858794311) = 1/(9858794311 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7972 : Bounds (-14221213 / 1000000000) (-3555303 / 250000000) (Real.log (9858794311 / 10000000000)) := by
  have h := reflection_log_7972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7973_neg : (47757641 / 200000000) ≤ -Real.log (7812500000 / 9919606177) ∧
    -Real.log (7812500000 / 9919606177) ≤ (119394103 / 500000000) := by
  have h := checkLog_sound (w := (2107106177 / 17732106177)) (n := 12)
    (lo := (47757641 / 200000000)) (hi := (119394103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9919606177 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9919606177 / 7812500000) = 1/(7812500000 / 9919606177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7973 : Bounds (47757641 / 200000000) (119394103 / 500000000) (Real.log (9919606177 / 7812500000)) := by
  have h := reflection_log_7973_neg
  have he : Real.log (9919606177 / 7812500000) = -Real.log (7812500000 / 9919606177) := by
    rw [show ((9919606177 / 7812500000) : ℝ) = ((7812500000 / 9919606177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7974_neg : (119893179 / 500000000) ≤ -Real.log (250000000000 / 317744396931) ∧
    -Real.log (250000000000 / 317744396931) ≤ (239786359 / 1000000000) := by
  have h := checkLog_sound (w := (67744396931 / 567744396931)) (n := 12)
    (lo := (119893179 / 500000000)) (hi := (239786359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317744396931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317744396931 / 250000000000) = 1/(250000000000 / 317744396931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7974 : Bounds (119893179 / 500000000) (239786359 / 1000000000) (Real.log (317744396931 / 250000000000)) := by
  have h := reflection_log_7974_neg
  have he : Real.log (317744396931 / 250000000000) = -Real.log (250000000000 / 317744396931) := by
    rw [show ((317744396931 / 250000000000) : ℝ) = ((250000000000 / 317744396931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7975_neg : (480009 / 1000000) ≤ -Real.log (62500000000 / 101005559189) ∧
    -Real.log (62500000000 / 101005559189) ≤ (480009001 / 1000000000) := by
  have h := checkLog_sound (w := (38505559189 / 163505559189)) (n := 12)
    (lo := (480009 / 1000000)) (hi := (480009001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101005559189 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101005559189 / 62500000000) = 1/(62500000000 / 101005559189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7975 : Bounds (480009 / 1000000) (480009001 / 1000000000) (Real.log (101005559189 / 62500000000)) := by
  have h := reflection_log_7975_neg
  have he : Real.log (101005559189 / 62500000000) = -Real.log (62500000000 / 101005559189) := by
    rw [show ((101005559189 / 62500000000) : ℝ) = ((62500000000 / 101005559189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7976_neg : (60133481 / 125000000) ≤ -Real.log (500000000000 / 808900523561) ∧
    -Real.log (500000000000 / 808900523561) ≤ (481067849 / 1000000000) := by
  have h := checkLog_sound (w := (308900523561 / 1308900523561)) (n := 12)
    (lo := (60133481 / 125000000)) (hi := (481067849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((808900523561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(808900523561 / 500000000000) = 1/(500000000000 / 808900523561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7976 : Bounds (60133481 / 125000000) (481067849 / 1000000000) (Real.log (808900523561 / 500000000000)) := by
  have h := reflection_log_7976_neg
  have he : Real.log (808900523561 / 500000000000) = -Real.log (500000000000 / 808900523561) := by
    rw [show ((808900523561 / 500000000000) : ℝ) = ((500000000000 / 808900523561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7977_neg : (212284807 / 1000000000) ≤ -Real.log (2000 / 2473) ∧
    -Real.log (2000 / 2473) ≤ (26535601 / 125000000) := by
  have h := checkLog_sound (w := (473 / 4473)) (n := 12)
    (lo := (212284807 / 1000000000)) (hi := (26535601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2473 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2473 / 2000) = 1/(2000 / 2473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7977 : Bounds (212284807 / 1000000000) (26535601 / 125000000) (Real.log (2473 / 2000)) := by
  have h := reflection_log_7977_neg
  have he : Real.log (2473 / 2000) = -Real.log (2000 / 2473) := by
    rw [show ((2473 / 2000) : ℝ) = ((2000 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7978_neg : (134921077 / 500000000) ≤ -Real.log (1527 / 2000) ∧
    -Real.log (1527 / 2000) ≤ (53968431 / 200000000) := by
  have h := checkLog_sound (w := (473 / 3527)) (n := 12)
    (lo := (134921077 / 500000000)) (hi := (53968431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1527) = 1/(1527 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7978 : Bounds (-53968431 / 200000000) (-134921077 / 500000000) (Real.log (1527 / 2000)) := by
  have h := reflection_log_7978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7979_neg : (29559 / 125000000) ≤ -Real.log (2000000 / 2000473) ∧
    -Real.log (2000000 / 2000473) ≤ (236473 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 4000473)) (n := 12)
    (lo := (29559 / 125000000)) (hi := (236473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000473 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000473 / 2000000) = 1/(2000000 / 2000473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7979 : Bounds (29559 / 125000000) (236473 / 1000000000) (Real.log (2000473 / 2000000)) := by
  have h := reflection_log_7979_neg
  have he : Real.log (2000473 / 2000000) = -Real.log (2000000 / 2000473) := by
    rw [show ((2000473 / 2000000) : ℝ) = ((2000000 / 2000473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7980_neg : (236527 / 1000000000) ≤ -Real.log (1999527 / 2000000) ∧
    -Real.log (1999527 / 2000000) ≤ (14783 / 62500000) := by
  have h := checkLog_sound (w := (473 / 3999527)) (n := 12)
    (lo := (236527 / 1000000000)) (hi := (14783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999527) = 1/(1999527 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7980 : Bounds (-14783 / 62500000) (-236527 / 1000000000) (Real.log (1999527 / 2000000)) := by
  have h := reflection_log_7980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7981_neg : (112514067 / 1000000000) ≤ -Real.log (62500 / 69943) ∧
    -Real.log (62500 / 69943) ≤ (28128517 / 250000000) := by
  have h := checkLog_sound (w := (7443 / 132443)) (n := 12)
    (lo := (112514067 / 1000000000)) (hi := (28128517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69943 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69943 / 62500) = 1/(62500 / 69943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7981 : Bounds (112514067 / 1000000000) (28128517 / 250000000) (Real.log (69943 / 62500)) := by
  have h := reflection_log_7981_neg
  have he : Real.log (69943 / 62500) = -Real.log (62500 / 69943) := by
    rw [show ((69943 / 62500) : ℝ) = ((62500 / 69943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7982_neg : (15849693 / 125000000) ≤ -Real.log (55057 / 62500) ∧
    -Real.log (55057 / 62500) ≤ (25359509 / 200000000) := by
  have h := checkLog_sound (w := (7443 / 117557)) (n := 12)
    (lo := (15849693 / 125000000)) (hi := (25359509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 55057) = 1/(55057 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7982 : Bounds (-25359509 / 200000000) (-15849693 / 125000000) (Real.log (55057 / 62500)) := by
  have h := reflection_log_7982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7983_neg : (56476807 / 500000000) ≤ -Real.log (50000 / 55979) ∧
    -Real.log (50000 / 55979) ≤ (22590723 / 200000000) := by
  have h := checkLog_sound (w := (5979 / 105979)) (n := 12)
    (lo := (56476807 / 500000000)) (hi := (22590723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55979 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55979 / 50000) = 1/(50000 / 55979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7983 : Bounds (56476807 / 500000000) (22590723 / 200000000) (Real.log (55979 / 50000)) := by
  have h := reflection_log_7983_neg
  have he : Real.log (55979 / 50000) = -Real.log (50000 / 55979) := by
    rw [show ((55979 / 50000) : ℝ) = ((50000 / 55979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7984_neg : (31839053 / 250000000) ≤ -Real.log (44021 / 50000) ∧
    -Real.log (44021 / 50000) ≤ (127356213 / 1000000000) := by
  have h := checkLog_sound (w := (5979 / 94021)) (n := 12)
    (lo := (31839053 / 250000000)) (hi := (127356213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44021) = 1/(44021 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7984 : Bounds (-127356213 / 1000000000) (-31839053 / 250000000) (Real.log (44021 / 50000)) := by
  have h := reflection_log_7984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7985_neg : (14402597 / 1000000000) ≤ -Real.log (2464251559 / 2500000000) ∧
    -Real.log (2464251559 / 2500000000) ≤ (7201299 / 500000000) := by
  have h := checkLog_sound (w := (35748441 / 4964251559)) (n := 12)
    (lo := (14402597 / 1000000000)) (hi := (7201299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2464251559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2464251559) = 1/(2464251559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7985 : Bounds (-7201299 / 500000000) (-14402597 / 1000000000) (Real.log (2464251559 / 2500000000)) := by
  have h := reflection_log_7985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7986_neg : (3570869 / 250000000) ≤ -Real.log (3850851751 / 3906250000) ∧
    -Real.log (3850851751 / 3906250000) ≤ (14283477 / 1000000000) := by
  have h := checkLog_sound (w := (55398249 / 7757101751)) (n := 12)
    (lo := (3570869 / 250000000)) (hi := (14283477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3850851751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3850851751) = 1/(3850851751 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7986 : Bounds (-14283477 / 1000000000) (-3570869 / 250000000) (Real.log (3850851751 / 3906250000)) := by
  have h := reflection_log_7986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7987_neg : (59827903 / 250000000) ≤ -Real.log (25000000000 / 31759358483) ∧
    -Real.log (25000000000 / 31759358483) ≤ (239311613 / 1000000000) := by
  have h := checkLog_sound (w := (6759358483 / 56759358483)) (n := 12)
    (lo := (59827903 / 250000000)) (hi := (239311613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31759358483 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31759358483 / 25000000000) = 1/(25000000000 / 31759358483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7987 : Bounds (59827903 / 250000000) (239311613 / 1000000000) (Real.log (31759358483 / 25000000000)) := by
  have h := reflection_log_7987_neg
  have he : Real.log (31759358483 / 25000000000) = -Real.log (25000000000 / 31759358483) := by
    rw [show ((31759358483 / 25000000000) : ℝ) = ((25000000000 / 31759358483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7988_neg : (240309827 / 1000000000) ≤ -Real.log (12500000000 / 15895538493) ∧
    -Real.log (12500000000 / 15895538493) ≤ (60077457 / 250000000) := by
  have h := checkLog_sound (w := (3395538493 / 28395538493)) (n := 12)
    (lo := (240309827 / 1000000000)) (hi := (60077457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15895538493 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15895538493 / 12500000000) = 1/(12500000000 / 15895538493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7988 : Bounds (240309827 / 1000000000) (60077457 / 250000000) (Real.log (15895538493 / 12500000000)) := by
  have h := reflection_log_7988_neg
  have he : Real.log (15895538493 / 12500000000) = -Real.log (12500000000 / 15895538493) := by
    rw [show ((15895538493 / 12500000000) : ℝ) = ((12500000000 / 15895538493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7989_neg : (60133481 / 125000000) ≤ -Real.log (12500000000 / 20222513089) ∧
    -Real.log (12500000000 / 20222513089) ≤ (481067849 / 1000000000) := by
  have h := checkLog_sound (w := (7722513089 / 32722513089)) (n := 12)
    (lo := (60133481 / 125000000)) (hi := (481067849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20222513089 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20222513089 / 12500000000) = 1/(12500000000 / 20222513089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7989 : Bounds (60133481 / 125000000) (481067849 / 1000000000) (Real.log (20222513089 / 12500000000)) := by
  have h := reflection_log_7989_neg
  have he : Real.log (20222513089 / 12500000000) = -Real.log (12500000000 / 20222513089) := by
    rw [show ((20222513089 / 12500000000) : ℝ) = ((12500000000 / 20222513089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7990_neg : (241063481 / 500000000) ≤ -Real.log (500000000000 / 809757694827) ∧
    -Real.log (500000000000 / 809757694827) ≤ (482126963 / 1000000000) := by
  have h := checkLog_sound (w := (309757694827 / 1309757694827)) (n := 12)
    (lo := (241063481 / 500000000)) (hi := (482126963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((809757694827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(809757694827 / 500000000000) = 1/(500000000000 / 809757694827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7990 : Bounds (241063481 / 500000000) (482126963 / 1000000000) (Real.log (809757694827 / 500000000000)) := by
  have h := reflection_log_7990_neg
  have he : Real.log (809757694827 / 500000000000) = -Real.log (500000000000 / 809757694827) := by
    rw [show ((809757694827 / 500000000000) : ℝ) = ((500000000000 / 809757694827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7991_neg : (212689093 / 1000000000) ≤ -Real.log (1000 / 1237) ∧
    -Real.log (1000 / 1237) ≤ (106344547 / 500000000) := by
  have h := checkLog_sound (w := (237 / 2237)) (n := 12)
    (lo := (212689093 / 1000000000)) (hi := (106344547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237 / 1000) = 1/(1000 / 1237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7991 : Bounds (212689093 / 1000000000) (106344547 / 500000000) (Real.log (1237 / 1000)) := by
  have h := reflection_log_7991_neg
  have he : Real.log (1237 / 1000) = -Real.log (1000 / 1237) := by
    rw [show ((1237 / 1000) : ℝ) = ((1000 / 1237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7992_neg : (270497247 / 1000000000) ≤ -Real.log (763 / 1000) ∧
    -Real.log (763 / 1000) ≤ (8453039 / 31250000) := by
  have h := checkLog_sound (w := (237 / 1763)) (n := 12)
    (lo := (270497247 / 1000000000)) (hi := (8453039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 763) = 1/(763 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7992 : Bounds (-8453039 / 31250000) (-270497247 / 1000000000) (Real.log (763 / 1000)) := by
  have h := reflection_log_7992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7993_neg : (236971 / 1000000000) ≤ -Real.log (1000000 / 1000237) ∧
    -Real.log (1000000 / 1000237) ≤ (59243 / 250000000) := by
  have h := checkLog_sound (w := (237 / 2000237)) (n := 12)
    (lo := (236971 / 1000000000)) (hi := (59243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000237 / 1000000) = 1/(1000000 / 1000237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7993 : Bounds (236971 / 1000000000) (59243 / 250000000) (Real.log (1000237 / 1000000)) := by
  have h := reflection_log_7993_neg
  have he : Real.log (1000237 / 1000000) = -Real.log (1000000 / 1000237) := by
    rw [show ((1000237 / 1000000) : ℝ) = ((1000000 / 1000237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7994_neg : (59257 / 250000000) ≤ -Real.log (999763 / 1000000) ∧
    -Real.log (999763 / 1000000) ≤ (237029 / 1000000000) := by
  have h := checkLog_sound (w := (237 / 1999763)) (n := 12)
    (lo := (59257 / 250000000)) (hi := (237029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999763) = 1/(999763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7994 : Bounds (-237029 / 1000000000) (-59257 / 250000000) (Real.log (999763 / 1000000)) := by
  have h := reflection_log_7994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7995_neg : (28185923 / 250000000) ≤ -Real.log (200000 / 223869) ∧
    -Real.log (200000 / 223869) ≤ (112743693 / 1000000000) := by
  have h := checkLog_sound (w := (23869 / 423869)) (n := 12)
    (lo := (28185923 / 250000000)) (hi := (112743693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223869 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223869 / 200000) = 1/(200000 / 223869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7995 : Bounds (28185923 / 250000000) (112743693 / 1000000000) (Real.log (223869 / 200000)) := by
  have h := reflection_log_7995_neg
  have he : Real.log (223869 / 200000) = -Real.log (200000 / 223869) := by
    rw [show ((223869 / 200000) : ℝ) = ((200000 / 223869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7996_neg : (12708933 / 100000000) ≤ -Real.log (176131 / 200000) ∧
    -Real.log (176131 / 200000) ≤ (127089331 / 1000000000) := by
  have h := checkLog_sound (w := (23869 / 376131)) (n := 12)
    (lo := (12708933 / 100000000)) (hi := (127089331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 176131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 176131) = 1/(176131 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7996 : Bounds (-127089331 / 1000000000) (-12708933 / 100000000) (Real.log (176131 / 200000)) := by
  have h := reflection_log_7996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7997_neg : (113184031 / 1000000000) ≤ -Real.log (500000 / 559919) ∧
    -Real.log (500000 / 559919) ≤ (3537001 / 31250000) := by
  have h := checkLog_sound (w := (59919 / 1059919)) (n := 12)
    (lo := (113184031 / 1000000000)) (hi := (3537001 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559919 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(559919 / 500000) = 1/(500000 / 559919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7997 : Bounds (113184031 / 1000000000) (3537001 / 31250000) (Real.log (559919 / 500000)) := by
  have h := reflection_log_7997_neg
  have he : Real.log (559919 / 500000) = -Real.log (500000 / 559919) := by
    rw [show ((559919 / 500000) : ℝ) = ((500000 / 559919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7998_neg : (127649297 / 1000000000) ≤ -Real.log (440081 / 500000) ∧
    -Real.log (440081 / 500000) ≤ (63824649 / 500000000) := by
  have h := checkLog_sound (w := (59919 / 940081)) (n := 12)
    (lo := (127649297 / 1000000000)) (hi := (63824649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 440081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 440081) = 1/(440081 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7998 : Bounds (-63824649 / 500000000) (-127649297 / 1000000000) (Real.log (440081 / 500000)) := by
  have h := reflection_log_7998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7999_neg : (2893053 / 200000000) ≤ -Real.log (246409713439 / 250000000000) ∧
    -Real.log (246409713439 / 250000000000) ≤ (7232633 / 500000000) := by
  have h := checkLog_sound (w := (3590286561 / 496409713439)) (n := 12)
    (lo := (2893053 / 200000000)) (hi := (7232633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246409713439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246409713439) = 1/(246409713439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7999 : Bounds (-7232633 / 500000000) (-2893053 / 200000000) (Real.log (246409713439 / 250000000000)) := by
  have h := reflection_log_7999_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
