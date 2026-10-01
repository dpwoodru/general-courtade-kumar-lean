import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4288_neg : (47621491 / 500000000) ≤ -Real.log (28411 / 31250) ∧
    -Real.log (28411 / 31250) ≤ (95242983 / 1000000000) := by
  have h := checkLog_sound (w := (2839 / 59661)) (n := 12)
    (lo := (47621491 / 500000000)) (hi := (95242983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28411) = 1/(28411 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4288 : Bounds (-95242983 / 1000000000) (-47621491 / 500000000) (Real.log (28411 / 31250)) := by
  have h := reflection_log_4288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4289_neg : (43583557 / 500000000) ≤ -Real.log (1000000 / 1091079) ∧
    -Real.log (1000000 / 1091079) ≤ (17433423 / 200000000) := by
  have h := checkLog_sound (w := (91079 / 2091079)) (n := 12)
    (lo := (43583557 / 500000000)) (hi := (17433423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091079 / 1000000) = 1/(1000000 / 1091079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4289 : Bounds (43583557 / 500000000) (17433423 / 200000000) (Real.log (1091079 / 1000000)) := by
  have h := reflection_log_4289_neg
  have he : Real.log (1091079 / 1000000) = -Real.log (1000000 / 1091079) := by
    rw [show ((1091079 / 1000000) : ℝ) = ((1000000 / 1091079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4290_neg : (95497097 / 1000000000) ≤ -Real.log (908921 / 1000000) ∧
    -Real.log (908921 / 1000000) ≤ (47748549 / 500000000) := by
  have h := checkLog_sound (w := (91079 / 1908921)) (n := 12)
    (lo := (95497097 / 1000000000)) (hi := (47748549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908921) = 1/(908921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4290 : Bounds (-47748549 / 500000000) (-95497097 / 1000000000) (Real.log (908921 / 1000000)) := by
  have h := reflection_log_4290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4291_neg : (4164991 / 500000000) ≤ -Real.log (991704615759 / 1000000000000) ∧
    -Real.log (991704615759 / 1000000000000) ≤ (8329983 / 1000000000) := by
  have h := checkLog_sound (w := (8295384241 / 1991704615759)) (n := 12)
    (lo := (4164991 / 500000000)) (hi := (8329983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991704615759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991704615759) = 1/(991704615759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4291 : Bounds (-8329983 / 1000000000) (-4164991 / 500000000) (Real.log (991704615759 / 1000000000000)) := by
  have h := reflection_log_4291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4292_neg : (4143803 / 500000000) ≤ -Real.log (968502579 / 976562500) ∧
    -Real.log (968502579 / 976562500) ≤ (8287607 / 1000000000) := by
  have h := checkLog_sound (w := (8059921 / 1945065079)) (n := 12)
    (lo := (4143803 / 500000000)) (hi := (8287607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 968502579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 968502579) = 1/(968502579 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4292 : Bounds (-8287607 / 1000000000) (-4143803 / 500000000) (Real.log (968502579 / 976562500)) := by
  have h := reflection_log_4292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4293_neg : (182198357 / 1000000000) ≤ -Real.log (500000000000 / 599926084967) ∧
    -Real.log (500000000000 / 599926084967) ≤ (91099179 / 500000000) := by
  have h := checkLog_sound (w := (99926084967 / 1099926084967)) (n := 12)
    (lo := (182198357 / 1000000000)) (hi := (91099179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599926084967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599926084967 / 500000000000) = 1/(500000000000 / 599926084967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4293 : Bounds (182198357 / 1000000000) (91099179 / 500000000) (Real.log (599926084967 / 500000000000)) := by
  have h := reflection_log_4293_neg
  have he : Real.log (599926084967 / 500000000000) = -Real.log (500000000000 / 599926084967) := by
    rw [show ((599926084967 / 500000000000) : ℝ) = ((500000000000 / 599926084967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4294_neg : (45666053 / 250000000) ≤ -Real.log (31250000000 / 37512851777) ∧
    -Real.log (31250000000 / 37512851777) ≤ (182664213 / 1000000000) := by
  have h := checkLog_sound (w := (6262851777 / 68762851777)) (n := 12)
    (lo := (45666053 / 250000000)) (hi := (182664213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37512851777 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37512851777 / 31250000000) = 1/(31250000000 / 37512851777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4294 : Bounds (45666053 / 250000000) (182664213 / 1000000000) (Real.log (37512851777 / 31250000000)) := by
  have h := reflection_log_4294_neg
  have he : Real.log (37512851777 / 31250000000) = -Real.log (31250000000 / 37512851777) := by
    rw [show ((37512851777 / 31250000000) : ℝ) = ((31250000000 / 37512851777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4295_neg : (182912981 / 500000000) ≤ -Real.log (100000000000 / 144170430961) ∧
    -Real.log (100000000000 / 144170430961) ≤ (365825963 / 1000000000) := by
  have h := checkLog_sound (w := (44170430961 / 244170430961)) (n := 12)
    (lo := (182912981 / 500000000)) (hi := (365825963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144170430961 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144170430961 / 100000000000) = 1/(100000000000 / 144170430961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4295 : Bounds (182912981 / 500000000) (365825963 / 1000000000) (Real.log (144170430961 / 100000000000)) := by
  have h := reflection_log_4295_neg
  have he : Real.log (144170430961 / 100000000000) = -Real.log (100000000000 / 144170430961) := by
    rw [show ((144170430961 / 100000000000) : ℝ) = ((100000000000 / 144170430961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4296_neg : (166361537 / 1000000000) ≤ -Real.log (1000 / 1181) ∧
    -Real.log (1000 / 1181) ≤ (83180769 / 500000000) := by
  have h := checkLog_sound (w := (181 / 2181)) (n := 12)
    (lo := (166361537 / 1000000000)) (hi := (83180769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 1000) = 1/(1000 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4296 : Bounds (166361537 / 1000000000) (83180769 / 500000000) (Real.log (1181 / 1000)) := by
  have h := reflection_log_4296_neg
  have he : Real.log (1181 / 1000) = -Real.log (1000 / 1181) := by
    rw [show ((1181 / 1000) : ℝ) = ((1000 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4297_neg : (39934239 / 200000000) ≤ -Real.log (819 / 1000) ∧
    -Real.log (819 / 1000) ≤ (49917799 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1819)) (n := 12)
    (lo := (39934239 / 200000000)) (hi := (49917799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 819) = 1/(819 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4297 : Bounds (-49917799 / 250000000) (-39934239 / 200000000) (Real.log (819 / 1000)) := by
  have h := reflection_log_4297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4298_neg : (180983 / 1000000000) ≤ -Real.log (1000000 / 1000181) ∧
    -Real.log (1000000 / 1000181) ≤ (22623 / 125000000) := by
  have h := checkLog_sound (w := (181 / 2000181)) (n := 12)
    (lo := (180983 / 1000000000)) (hi := (22623 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000181 / 1000000) = 1/(1000000 / 1000181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4298 : Bounds (180983 / 1000000000) (22623 / 125000000) (Real.log (1000181 / 1000000)) := by
  have h := reflection_log_4298_neg
  have he : Real.log (1000181 / 1000000) = -Real.log (1000000 / 1000181) := by
    rw [show ((1000181 / 1000000) : ℝ) = ((1000000 / 1000181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4299_neg : (22627 / 125000000) ≤ -Real.log (999819 / 1000000) ∧
    -Real.log (999819 / 1000000) ≤ (181017 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1999819)) (n := 12)
    (lo := (22627 / 125000000)) (hi := (181017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999819) = 1/(999819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4299 : Bounds (-181017 / 1000000000) (-22627 / 125000000) (Real.log (999819 / 1000000)) := by
  have h := reflection_log_4299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4300_neg : (43501063 / 500000000) ≤ -Real.log (1000000 / 1090899) ∧
    -Real.log (1000000 / 1090899) ≤ (87002127 / 1000000000) := by
  have h := checkLog_sound (w := (90899 / 2090899)) (n := 12)
    (lo := (43501063 / 500000000)) (hi := (87002127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090899 / 1000000) = 1/(1000000 / 1090899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4300 : Bounds (43501063 / 500000000) (87002127 / 1000000000) (Real.log (1090899 / 1000000)) := by
  have h := reflection_log_4300_neg
  have he : Real.log (1090899 / 1000000) = -Real.log (1000000 / 1090899) := by
    rw [show ((1090899 / 1000000) : ℝ) = ((1000000 / 1090899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4301_neg : (95299079 / 1000000000) ≤ -Real.log (909101 / 1000000) ∧
    -Real.log (909101 / 1000000) ≤ (2382477 / 25000000) := by
  have h := checkLog_sound (w := (90899 / 1909101)) (n := 12)
    (lo := (95299079 / 1000000000)) (hi := (2382477 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909101) = 1/(909101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4301 : Bounds (-2382477 / 25000000) (-95299079 / 1000000000) (Real.log (909101 / 1000000)) := by
  have h := reflection_log_4301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4302_neg : (2725433 / 31250000) ≤ -Real.log (100000 / 109113) ∧
    -Real.log (100000 / 109113) ≤ (87213857 / 1000000000) := by
  have h := checkLog_sound (w := (9113 / 209113)) (n := 12)
    (lo := (2725433 / 31250000)) (hi := (87213857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109113 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109113 / 100000) = 1/(100000 / 109113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4302 : Bounds (2725433 / 31250000) (87213857 / 1000000000) (Real.log (109113 / 100000)) := by
  have h := reflection_log_4302_neg
  have he : Real.log (109113 / 100000) = -Real.log (100000 / 109113) := by
    rw [show ((109113 / 100000) : ℝ) = ((100000 / 109113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4303_neg : (95553209 / 1000000000) ≤ -Real.log (90887 / 100000) ∧
    -Real.log (90887 / 100000) ≤ (9555321 / 100000000) := by
  have h := checkLog_sound (w := (9113 / 190887)) (n := 12)
    (lo := (95553209 / 1000000000)) (hi := (9555321 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90887) = 1/(90887 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4303 : Bounds (-9555321 / 100000000) (-95553209 / 1000000000) (Real.log (90887 / 100000)) := by
  have h := reflection_log_4303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4304_neg : (1042419 / 125000000) ≤ -Real.log (9916953231 / 10000000000) ∧
    -Real.log (9916953231 / 10000000000) ≤ (8339353 / 1000000000) := by
  have h := checkLog_sound (w := (83046769 / 19916953231)) (n := 12)
    (lo := (1042419 / 125000000)) (hi := (8339353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9916953231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9916953231) = 1/(9916953231 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4304 : Bounds (-8339353 / 1000000000) (-1042419 / 125000000) (Real.log (9916953231 / 10000000000)) := by
  have h := reflection_log_4304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4305_neg : (1037119 / 125000000) ≤ -Real.log (991737371799 / 1000000000000) ∧
    -Real.log (991737371799 / 1000000000000) ≤ (8296953 / 1000000000) := by
  have h := checkLog_sound (w := (8262628201 / 1991737371799)) (n := 12)
    (lo := (1037119 / 125000000)) (hi := (8296953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991737371799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991737371799) = 1/(991737371799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4305 : Bounds (-8296953 / 1000000000) (-1037119 / 125000000) (Real.log (991737371799 / 1000000000000)) := by
  have h := reflection_log_4305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4306_neg : (91150603 / 500000000) ≤ -Real.log (100000000000 / 119997558027) ∧
    -Real.log (100000000000 / 119997558027) ≤ (182301207 / 1000000000) := by
  have h := checkLog_sound (w := (19997558027 / 219997558027)) (n := 12)
    (lo := (91150603 / 500000000)) (hi := (182301207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119997558027 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119997558027 / 100000000000) = 1/(100000000000 / 119997558027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4306 : Bounds (91150603 / 500000000) (182301207 / 1000000000) (Real.log (119997558027 / 100000000000)) := by
  have h := reflection_log_4306_neg
  have he : Real.log (119997558027 / 100000000000) = -Real.log (100000000000 / 119997558027) := by
    rw [show ((119997558027 / 100000000000) : ℝ) = ((100000000000 / 119997558027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4307_neg : (36553413 / 200000000) ≤ -Real.log (50000000000 / 60026736497) ∧
    -Real.log (50000000000 / 60026736497) ≤ (91383533 / 500000000) := by
  have h := checkLog_sound (w := (10026736497 / 110026736497)) (n := 12)
    (lo := (36553413 / 200000000)) (hi := (91383533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60026736497 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60026736497 / 50000000000) = 1/(50000000000 / 60026736497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4307 : Bounds (36553413 / 200000000) (91383533 / 500000000) (Real.log (60026736497 / 50000000000)) := by
  have h := reflection_log_4307_neg
  have he : Real.log (60026736497 / 50000000000) = -Real.log (50000000000 / 60026736497) := by
    rw [show ((60026736497 / 50000000000) : ℝ) = ((50000000000 / 60026736497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4308_neg : (182912981 / 500000000) ≤ -Real.log (125000000000 / 180213038701) ∧
    -Real.log (125000000000 / 180213038701) ≤ (365825963 / 1000000000) := by
  have h := checkLog_sound (w := (55213038701 / 305213038701)) (n := 12)
    (lo := (182912981 / 500000000)) (hi := (365825963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180213038701 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180213038701 / 125000000000) = 1/(125000000000 / 180213038701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4308 : Bounds (182912981 / 500000000) (365825963 / 1000000000) (Real.log (180213038701 / 125000000000)) := by
  have h := reflection_log_4308_neg
  have he : Real.log (180213038701 / 125000000000) = -Real.log (125000000000 / 180213038701) := by
    rw [show ((180213038701 / 125000000000) : ℝ) = ((125000000000 / 180213038701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4309_neg : (91508183 / 250000000) ≤ -Real.log (250000000000 / 360500610501) ∧
    -Real.log (250000000000 / 360500610501) ≤ (366032733 / 1000000000) := by
  have h := checkLog_sound (w := (110500610501 / 610500610501)) (n := 12)
    (lo := (91508183 / 250000000)) (hi := (366032733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360500610501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360500610501 / 250000000000) = 1/(250000000000 / 360500610501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4309 : Bounds (91508183 / 250000000) (366032733 / 1000000000) (Real.log (360500610501 / 250000000000)) := by
  have h := reflection_log_4309_neg
  have he : Real.log (360500610501 / 250000000000) = -Real.log (250000000000 / 360500610501) := by
    rw [show ((360500610501 / 250000000000) : ℝ) = ((250000000000 / 360500610501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4310_neg : (166446207 / 1000000000) ≤ -Real.log (10000 / 11811) ∧
    -Real.log (10000 / 11811) ≤ (1300361 / 7812500) := by
  have h := checkLog_sound (w := (1811 / 21811)) (n := 12)
    (lo := (166446207 / 1000000000)) (hi := (1300361 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11811 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11811 / 10000) = 1/(10000 / 11811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4310 : Bounds (166446207 / 1000000000) (1300361 / 7812500) (Real.log (11811 / 10000)) := by
  have h := reflection_log_4310_neg
  have he : Real.log (11811 / 10000) = -Real.log (10000 / 11811) := by
    rw [show ((11811 / 10000) : ℝ) = ((10000 / 11811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4311_neg : (99896651 / 500000000) ≤ -Real.log (8189 / 10000) ∧
    -Real.log (8189 / 10000) ≤ (199793303 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 18189)) (n := 12)
    (lo := (99896651 / 500000000)) (hi := (199793303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8189) = 1/(8189 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4311 : Bounds (-199793303 / 1000000000) (-99896651 / 500000000) (Real.log (8189 / 10000)) := by
  have h := reflection_log_4311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4312_neg : (181083 / 1000000000) ≤ -Real.log (10000000 / 10001811) ∧
    -Real.log (10000000 / 10001811) ≤ (45271 / 250000000) := by
  have h := checkLog_sound (w := (1811 / 20001811)) (n := 12)
    (lo := (181083 / 1000000000)) (hi := (45271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001811 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001811 / 10000000) = 1/(10000000 / 10001811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4312 : Bounds (181083 / 1000000000) (45271 / 250000000) (Real.log (10001811 / 10000000)) := by
  have h := reflection_log_4312_neg
  have he : Real.log (10001811 / 10000000) = -Real.log (10000000 / 10001811) := by
    rw [show ((10001811 / 10000000) : ℝ) = ((10000000 / 10001811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4313_neg : (45279 / 250000000) ≤ -Real.log (9998189 / 10000000) ∧
    -Real.log (9998189 / 10000000) ≤ (181117 / 1000000000) := by
  have h := checkLog_sound (w := (1811 / 19998189)) (n := 12)
    (lo := (45279 / 250000000)) (hi := (181117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998189) = 1/(9998189 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4313 : Bounds (-181117 / 1000000000) (-45279 / 250000000) (Real.log (9998189 / 10000000)) := by
  have h := reflection_log_4313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4314_neg : (87047959 / 1000000000) ≤ -Real.log (1000000 / 1090949) ∧
    -Real.log (1000000 / 1090949) ≤ (2176199 / 25000000) := by
  have h := checkLog_sound (w := (90949 / 2090949)) (n := 12)
    (lo := (87047959 / 1000000000)) (hi := (2176199 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090949 / 1000000) = 1/(1000000 / 1090949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4314 : Bounds (87047959 / 1000000000) (2176199 / 25000000) (Real.log (1090949 / 1000000)) := by
  have h := reflection_log_4314_neg
  have he : Real.log (1090949 / 1000000) = -Real.log (1000000 / 1090949) := by
    rw [show ((1090949 / 1000000) : ℝ) = ((1000000 / 1090949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4315_neg : (595963 / 6250000) ≤ -Real.log (909051 / 1000000) ∧
    -Real.log (909051 / 1000000) ≤ (95354081 / 1000000000) := by
  have h := checkLog_sound (w := (90949 / 1909051)) (n := 12)
    (lo := (595963 / 6250000)) (hi := (95354081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909051) = 1/(909051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4315 : Bounds (-95354081 / 1000000000) (-595963 / 6250000) (Real.log (909051 / 1000000)) := by
  have h := reflection_log_4315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4316_neg : (17452119 / 200000000) ≤ -Real.log (1000000 / 1091181) ∧
    -Real.log (1000000 / 1091181) ≤ (21815149 / 250000000) := by
  have h := checkLog_sound (w := (91181 / 2091181)) (n := 12)
    (lo := (17452119 / 200000000)) (hi := (21815149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091181 / 1000000) = 1/(1000000 / 1091181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4316 : Bounds (17452119 / 200000000) (21815149 / 250000000) (Real.log (1091181 / 1000000)) := by
  have h := reflection_log_4316_neg
  have he : Real.log (1091181 / 1000000) = -Real.log (1000000 / 1091181) := by
    rw [show ((1091181 / 1000000) : ℝ) = ((1000000 / 1091181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4317_neg : (23902331 / 250000000) ≤ -Real.log (908819 / 1000000) ∧
    -Real.log (908819 / 1000000) ≤ (3824373 / 40000000) := by
  have h := checkLog_sound (w := (91181 / 1908819)) (n := 12)
    (lo := (23902331 / 250000000)) (hi := (3824373 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908819) = 1/(908819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4317 : Bounds (-3824373 / 40000000) (-23902331 / 250000000) (Real.log (908819 / 1000000)) := by
  have h := reflection_log_4317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4318_neg : (1043591 / 125000000) ≤ -Real.log (991686025239 / 1000000000000) ∧
    -Real.log (991686025239 / 1000000000000) ≤ (8348729 / 1000000000) := by
  have h := checkLog_sound (w := (8313974761 / 1991686025239)) (n := 12)
    (lo := (1043591 / 125000000)) (hi := (8348729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991686025239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991686025239) = 1/(991686025239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4318 : Bounds (-8348729 / 1000000000) (-1043591 / 125000000) (Real.log (991686025239 / 1000000000000)) := by
  have h := reflection_log_4318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4319_neg : (8306121 / 1000000000) ≤ -Real.log (991728279399 / 1000000000000) ∧
    -Real.log (991728279399 / 1000000000000) ≤ (4153061 / 500000000) := by
  have h := checkLog_sound (w := (8271720601 / 1991728279399)) (n := 12)
    (lo := (8306121 / 1000000000)) (hi := (4153061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991728279399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991728279399) = 1/(991728279399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4319 : Bounds (-4153061 / 500000000) (-8306121 / 1000000000) (Real.log (991728279399 / 1000000000000)) := by
  have h := reflection_log_4319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4320_neg : (4560051 / 25000000) ≤ -Real.log (12500000000 / 15001207303) ∧
    -Real.log (12500000000 / 15001207303) ≤ (182402041 / 1000000000) := by
  have h := checkLog_sound (w := (2501207303 / 27501207303)) (n := 12)
    (lo := (4560051 / 25000000)) (hi := (182402041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15001207303 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15001207303 / 12500000000) = 1/(12500000000 / 15001207303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4320 : Bounds (4560051 / 25000000) (182402041 / 1000000000) (Real.log (15001207303 / 12500000000)) := by
  have h := reflection_log_4320_neg
  have he : Real.log (15001207303 / 12500000000) = -Real.log (12500000000 / 15001207303) := by
    rw [show ((15001207303 / 12500000000) : ℝ) = ((12500000000 / 15001207303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4321_neg : (1142937 / 6250000) ≤ -Real.log (500000000000 / 600329108437) ∧
    -Real.log (500000000000 / 600329108437) ≤ (182869921 / 1000000000) := by
  have h := checkLog_sound (w := (100329108437 / 1100329108437)) (n := 12)
    (lo := (1142937 / 6250000)) (hi := (182869921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600329108437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600329108437 / 500000000000) = 1/(500000000000 / 600329108437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4321 : Bounds (1142937 / 6250000) (182869921 / 1000000000) (Real.log (600329108437 / 500000000000)) := by
  have h := reflection_log_4321_neg
  have he : Real.log (600329108437 / 500000000000) = -Real.log (500000000000 / 600329108437) := by
    rw [show ((600329108437 / 500000000000) : ℝ) = ((500000000000 / 600329108437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4322_neg : (91508183 / 250000000) ≤ -Real.log (500000000000 / 721001221001) ∧
    -Real.log (500000000000 / 721001221001) ≤ (366032733 / 1000000000) := by
  have h := checkLog_sound (w := (221001221001 / 1221001221001)) (n := 12)
    (lo := (91508183 / 250000000)) (hi := (366032733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721001221001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721001221001 / 500000000000) = 1/(500000000000 / 721001221001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4322 : Bounds (91508183 / 250000000) (366032733 / 1000000000) (Real.log (721001221001 / 500000000000)) := by
  have h := reflection_log_4322_neg
  have he : Real.log (721001221001 / 500000000000) = -Real.log (500000000000 / 721001221001) := by
    rw [show ((721001221001 / 500000000000) : ℝ) = ((500000000000 / 721001221001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4323_neg : (36623951 / 100000000) ≤ -Real.log (100000000000 / 144230064721) ∧
    -Real.log (100000000000 / 144230064721) ≤ (366239511 / 1000000000) := by
  have h := checkLog_sound (w := (44230064721 / 244230064721)) (n := 12)
    (lo := (36623951 / 100000000)) (hi := (366239511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144230064721 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144230064721 / 100000000000) = 1/(100000000000 / 144230064721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4323 : Bounds (36623951 / 100000000) (366239511 / 1000000000) (Real.log (144230064721 / 100000000000)) := by
  have h := reflection_log_4323_neg
  have he : Real.log (144230064721 / 100000000000) = -Real.log (100000000000 / 144230064721) := by
    rw [show ((144230064721 / 100000000000) : ℝ) = ((100000000000 / 144230064721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4324_neg : (16653087 / 100000000) ≤ -Real.log (2500 / 2953) ∧
    -Real.log (2500 / 2953) ≤ (166530871 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 5453)) (n := 12)
    (lo := (16653087 / 100000000)) (hi := (166530871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2953 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2953 / 2500) = 1/(2500 / 2953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4324 : Bounds (16653087 / 100000000) (166530871 / 1000000000) (Real.log (2953 / 2500)) := by
  have h := reflection_log_4324_neg
  have he : Real.log (2953 / 2500) = -Real.log (2500 / 2953) := by
    rw [show ((2953 / 2500) : ℝ) = ((2500 / 2953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4325_neg : (7996617 / 40000000) ≤ -Real.log (2047 / 2500) ∧
    -Real.log (2047 / 2500) ≤ (99957713 / 500000000) := by
  have h := checkLog_sound (w := (453 / 4547)) (n := 12)
    (lo := (7996617 / 40000000)) (hi := (99957713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2047) = 1/(2047 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4325 : Bounds (-99957713 / 500000000) (-7996617 / 40000000) (Real.log (2047 / 2500)) := by
  have h := reflection_log_4325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4326_neg : (181183 / 1000000000) ≤ -Real.log (2500000 / 2500453) ∧
    -Real.log (2500000 / 2500453) ≤ (2831 / 15625000) := by
  have h := checkLog_sound (w := (453 / 5000453)) (n := 12)
    (lo := (181183 / 1000000000)) (hi := (2831 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500453 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500453 / 2500000) = 1/(2500000 / 2500453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4326 : Bounds (181183 / 1000000000) (2831 / 15625000) (Real.log (2500453 / 2500000)) := by
  have h := reflection_log_4326_neg
  have he : Real.log (2500453 / 2500000) = -Real.log (2500000 / 2500453) := by
    rw [show ((2500453 / 2500000) : ℝ) = ((2500000 / 2500453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4327_neg : (5663 / 31250000) ≤ -Real.log (2499547 / 2500000) ∧
    -Real.log (2499547 / 2500000) ≤ (181217 / 1000000000) := by
  have h := checkLog_sound (w := (453 / 4999547)) (n := 12)
    (lo := (5663 / 31250000)) (hi := (181217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499547) = 1/(2499547 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4327 : Bounds (-181217 / 1000000000) (-5663 / 31250000) (Real.log (2499547 / 2500000)) := by
  have h := reflection_log_4327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4328_neg : (43547353 / 500000000) ≤ -Real.log (1000 / 1091) ∧
    -Real.log (1000 / 1091) ≤ (87094707 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 2091)) (n := 12)
    (lo := (43547353 / 500000000)) (hi := (87094707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 1000) = 1/(1000 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4328 : Bounds (43547353 / 500000000) (87094707 / 1000000000) (Real.log (1091 / 1000)) := by
  have h := reflection_log_4328_neg
  have he : Real.log (1091 / 1000) = -Real.log (1000 / 1091) := by
    rw [show ((1091 / 1000) : ℝ) = ((1000 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4329_neg : (11926273 / 125000000) ≤ -Real.log (909 / 1000) ∧
    -Real.log (909 / 1000) ≤ (19082037 / 200000000) := by
  have h := checkLog_sound (w := (91 / 1909)) (n := 12)
    (lo := (11926273 / 125000000)) (hi := (19082037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 909) = 1/(909 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4329 : Bounds (-19082037 / 200000000) (-11926273 / 125000000) (Real.log (909 / 1000)) := by
  have h := reflection_log_4329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4330_neg : (87307333 / 1000000000) ≤ -Real.log (31250 / 34101) ∧
    -Real.log (31250 / 34101) ≤ (43653667 / 500000000) := by
  have h := checkLog_sound (w := (2851 / 65351)) (n := 12)
    (lo := (87307333 / 1000000000)) (hi := (43653667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34101 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34101 / 31250) = 1/(31250 / 34101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4330 : Bounds (87307333 / 1000000000) (43653667 / 500000000) (Real.log (34101 / 31250)) := by
  have h := reflection_log_4330_neg
  have he : Real.log (34101 / 31250) = -Real.log (31250 / 34101) := by
    rw [show ((34101 / 31250) : ℝ) = ((31250 / 34101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4331_neg : (47832721 / 500000000) ≤ -Real.log (28399 / 31250) ∧
    -Real.log (28399 / 31250) ≤ (95665443 / 1000000000) := by
  have h := checkLog_sound (w := (2851 / 59649)) (n := 12)
    (lo := (47832721 / 500000000)) (hi := (95665443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28399) = 1/(28399 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4331 : Bounds (-95665443 / 1000000000) (-47832721 / 500000000) (Real.log (28399 / 31250)) := by
  have h := reflection_log_4331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4332_neg : (8358109 / 1000000000) ≤ -Real.log (968434299 / 976562500) ∧
    -Real.log (968434299 / 976562500) ≤ (835811 / 100000000) := by
  have h := checkLog_sound (w := (8128201 / 1944996799)) (n := 12)
    (lo := (8358109 / 1000000000)) (hi := (835811 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 968434299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 968434299) = 1/(968434299 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4332 : Bounds (-835811 / 100000000) (-8358109 / 1000000000) (Real.log (968434299 / 976562500)) := by
  have h := reflection_log_4332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4333_neg : (8315477 / 1000000000) ≤ -Real.log (991719 / 1000000) ∧
    -Real.log (991719 / 1000000) ≤ (4157739 / 500000000) := by
  have h := checkLog_sound (w := (8281 / 1991719)) (n := 12)
    (lo := (8315477 / 1000000000)) (hi := (4157739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 991719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 991719) = 1/(991719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4333 : Bounds (-4157739 / 500000000) (-8315477 / 1000000000) (Real.log (991719 / 1000000)) := by
  have h := reflection_log_4333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4334_neg : (182504891 / 1000000000) ≤ -Real.log (500000000000 / 600110011001) ∧
    -Real.log (500000000000 / 600110011001) ≤ (45626223 / 250000000) := by
  have h := checkLog_sound (w := (100110011001 / 1100110011001)) (n := 12)
    (lo := (182504891 / 1000000000)) (hi := (45626223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600110011001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600110011001 / 500000000000) = 1/(500000000000 / 600110011001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4334 : Bounds (182504891 / 1000000000) (45626223 / 250000000) (Real.log (600110011001 / 500000000000)) := by
  have h := reflection_log_4334_neg
  have he : Real.log (600110011001 / 500000000000) = -Real.log (500000000000 / 600110011001) := by
    rw [show ((600110011001 / 500000000000) : ℝ) = ((500000000000 / 600110011001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4335_neg : (22871597 / 125000000) ≤ -Real.log (250000000000 / 300195429417) ∧
    -Real.log (250000000000 / 300195429417) ≤ (182972777 / 1000000000) := by
  have h := checkLog_sound (w := (50195429417 / 550195429417)) (n := 12)
    (lo := (22871597 / 125000000)) (hi := (182972777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300195429417 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300195429417 / 250000000000) = 1/(250000000000 / 300195429417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4335 : Bounds (22871597 / 125000000) (182972777 / 1000000000) (Real.log (300195429417 / 250000000000)) := by
  have h := reflection_log_4335_neg
  have he : Real.log (300195429417 / 250000000000) = -Real.log (250000000000 / 300195429417) := by
    rw [show ((300195429417 / 250000000000) : ℝ) = ((250000000000 / 300195429417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4336_neg : (36623951 / 100000000) ≤ -Real.log (125000000000 / 180287580901) ∧
    -Real.log (125000000000 / 180287580901) ≤ (366239511 / 1000000000) := by
  have h := checkLog_sound (w := (55287580901 / 305287580901)) (n := 12)
    (lo := (36623951 / 100000000)) (hi := (366239511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180287580901 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180287580901 / 125000000000) = 1/(125000000000 / 180287580901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4336 : Bounds (36623951 / 100000000) (366239511 / 1000000000) (Real.log (180287580901 / 125000000000)) := by
  have h := reflection_log_4336_neg
  have he : Real.log (180287580901 / 125000000000) = -Real.log (125000000000 / 180287580901) := by
    rw [show ((180287580901 / 125000000000) : ℝ) = ((125000000000 / 180287580901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4337_neg : (45805787 / 125000000) ≤ -Real.log (500000000000 / 721299462629) ∧
    -Real.log (500000000000 / 721299462629) ≤ (366446297 / 1000000000) := by
  have h := checkLog_sound (w := (221299462629 / 1221299462629)) (n := 12)
    (lo := (45805787 / 125000000)) (hi := (366446297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721299462629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721299462629 / 500000000000) = 1/(500000000000 / 721299462629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4337 : Bounds (45805787 / 125000000) (366446297 / 1000000000) (Real.log (721299462629 / 500000000000)) := by
  have h := reflection_log_4337_neg
  have he : Real.log (721299462629 / 500000000000) = -Real.log (500000000000 / 721299462629) := by
    rw [show ((721299462629 / 500000000000) : ℝ) = ((500000000000 / 721299462629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4338_neg : (83307763 / 500000000) ≤ -Real.log (10000 / 11813) ∧
    -Real.log (10000 / 11813) ≤ (166615527 / 1000000000) := by
  have h := checkLog_sound (w := (1813 / 21813)) (n := 12)
    (lo := (83307763 / 500000000)) (hi := (166615527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11813 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11813 / 10000) = 1/(10000 / 11813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4338 : Bounds (83307763 / 500000000) (166615527 / 1000000000) (Real.log (11813 / 10000)) := by
  have h := reflection_log_4338_neg
  have he : Real.log (11813 / 10000) = -Real.log (10000 / 11813) := by
    rw [show ((11813 / 10000) : ℝ) = ((10000 / 11813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4339_neg : (100018781 / 500000000) ≤ -Real.log (8187 / 10000) ∧
    -Real.log (8187 / 10000) ≤ (200037563 / 1000000000) := by
  have h := checkLog_sound (w := (1813 / 18187)) (n := 12)
    (lo := (100018781 / 500000000)) (hi := (200037563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8187) = 1/(8187 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4339 : Bounds (-200037563 / 1000000000) (-100018781 / 500000000) (Real.log (8187 / 10000)) := by
  have h := reflection_log_4339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4340_neg : (181283 / 1000000000) ≤ -Real.log (10000000 / 10001813) ∧
    -Real.log (10000000 / 10001813) ≤ (45321 / 250000000) := by
  have h := checkLog_sound (w := (1813 / 20001813)) (n := 12)
    (lo := (181283 / 1000000000)) (hi := (45321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001813 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001813 / 10000000) = 1/(10000000 / 10001813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4340 : Bounds (181283 / 1000000000) (45321 / 250000000) (Real.log (10001813 / 10000000)) := by
  have h := reflection_log_4340_neg
  have he : Real.log (10001813 / 10000000) = -Real.log (10000000 / 10001813) := by
    rw [show ((10001813 / 10000000) : ℝ) = ((10000000 / 10001813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4341_neg : (45329 / 250000000) ≤ -Real.log (9998187 / 10000000) ∧
    -Real.log (9998187 / 10000000) ≤ (181317 / 1000000000) := by
  have h := checkLog_sound (w := (1813 / 19998187)) (n := 12)
    (lo := (45329 / 250000000)) (hi := (181317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998187) = 1/(9998187 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4341 : Bounds (-181317 / 1000000000) (-45329 / 250000000) (Real.log (9998187 / 10000000)) := by
  have h := reflection_log_4341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4342_neg : (87141451 / 1000000000) ≤ -Real.log (1000000 / 1091051) ∧
    -Real.log (1000000 / 1091051) ≤ (21785363 / 250000000) := by
  have h := checkLog_sound (w := (91051 / 2091051)) (n := 12)
    (lo := (87141451 / 1000000000)) (hi := (21785363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091051 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091051 / 1000000) = 1/(1000000 / 1091051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4342 : Bounds (87141451 / 1000000000) (21785363 / 250000000) (Real.log (1091051 / 1000000)) := by
  have h := reflection_log_4342_neg
  have he : Real.log (1091051 / 1000000) = -Real.log (1000000 / 1091051) := by
    rw [show ((1091051 / 1000000) : ℝ) = ((1000000 / 1091051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4343_neg : (95466291 / 1000000000) ≤ -Real.log (908949 / 1000000) ∧
    -Real.log (908949 / 1000000) ≤ (23866573 / 250000000) := by
  have h := checkLog_sound (w := (91051 / 1908949)) (n := 12)
    (lo := (95466291 / 1000000000)) (hi := (23866573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908949) = 1/(908949 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4343 : Bounds (-23866573 / 250000000) (-95466291 / 1000000000) (Real.log (908949 / 1000000)) := by
  have h := reflection_log_4343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4344_neg : (21838517 / 250000000) ≤ -Real.log (1000000 / 1091283) ∧
    -Real.log (1000000 / 1091283) ≤ (87354069 / 1000000000) := by
  have h := checkLog_sound (w := (91283 / 2091283)) (n := 12)
    (lo := (21838517 / 250000000)) (hi := (87354069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091283 / 1000000) = 1/(1000000 / 1091283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4344 : Bounds (21838517 / 250000000) (87354069 / 1000000000) (Real.log (1091283 / 1000000)) := by
  have h := reflection_log_4344_neg
  have he : Real.log (1091283 / 1000000) = -Real.log (1000000 / 1091283) := by
    rw [show ((1091283 / 1000000) : ℝ) = ((1000000 / 1091283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4345_neg : (23930391 / 250000000) ≤ -Real.log (908717 / 1000000) ∧
    -Real.log (908717 / 1000000) ≤ (19144313 / 200000000) := by
  have h := checkLog_sound (w := (91283 / 1908717)) (n := 12)
    (lo := (23930391 / 250000000)) (hi := (19144313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 908717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 908717) = 1/(908717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4345 : Bounds (-19144313 / 200000000) (-23930391 / 250000000) (Real.log (908717 / 1000000)) := by
  have h := reflection_log_4345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4346_neg : (1045937 / 125000000) ≤ -Real.log (991667413911 / 1000000000000) ∧
    -Real.log (991667413911 / 1000000000000) ≤ (8367497 / 1000000000) := by
  have h := checkLog_sound (w := (8332586089 / 1991667413911)) (n := 12)
    (lo := (1045937 / 125000000)) (hi := (8367497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991667413911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991667413911) = 1/(991667413911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4346 : Bounds (-8367497 / 1000000000) (-1045937 / 125000000) (Real.log (991667413911 / 1000000000000)) := by
  have h := reflection_log_4346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4347_neg : (208121 / 25000000) ≤ -Real.log (991709715399 / 1000000000000) ∧
    -Real.log (991709715399 / 1000000000000) ≤ (8324841 / 1000000000) := by
  have h := checkLog_sound (w := (8290284601 / 1991709715399)) (n := 12)
    (lo := (208121 / 25000000)) (hi := (8324841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991709715399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991709715399) = 1/(991709715399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4347 : Bounds (-8324841 / 1000000000) (-208121 / 25000000) (Real.log (991709715399 / 1000000000000)) := by
  have h := reflection_log_4347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4348_neg : (182607743 / 1000000000) ≤ -Real.log (62500000000 / 75021467101) ∧
    -Real.log (62500000000 / 75021467101) ≤ (1426623 / 7812500) := by
  have h := checkLog_sound (w := (12521467101 / 137521467101)) (n := 12)
    (lo := (182607743 / 1000000000)) (hi := (1426623 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75021467101 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75021467101 / 62500000000) = 1/(62500000000 / 75021467101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4348 : Bounds (182607743 / 1000000000) (1426623 / 7812500) (Real.log (75021467101 / 62500000000)) := by
  have h := reflection_log_4348_neg
  have he : Real.log (75021467101 / 62500000000) = -Real.log (62500000000 / 75021467101) := by
    rw [show ((75021467101 / 62500000000) : ℝ) = ((62500000000 / 75021467101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4349_neg : (11442227 / 62500000) ≤ -Real.log (250000000000 / 300226308081) ∧
    -Real.log (250000000000 / 300226308081) ≤ (183075633 / 1000000000) := by
  have h := checkLog_sound (w := (50226308081 / 550226308081)) (n := 12)
    (lo := (11442227 / 62500000)) (hi := (183075633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300226308081 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300226308081 / 250000000000) = 1/(250000000000 / 300226308081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4349 : Bounds (11442227 / 62500000) (183075633 / 1000000000) (Real.log (300226308081 / 250000000000)) := by
  have h := reflection_log_4349_neg
  have he : Real.log (300226308081 / 250000000000) = -Real.log (250000000000 / 300226308081) := by
    rw [show ((300226308081 / 250000000000) : ℝ) = ((250000000000 / 300226308081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4350_neg : (45805787 / 125000000) ≤ -Real.log (125000000000 / 180324865657) ∧
    -Real.log (125000000000 / 180324865657) ≤ (366446297 / 1000000000) := by
  have h := checkLog_sound (w := (55324865657 / 305324865657)) (n := 12)
    (lo := (45805787 / 125000000)) (hi := (366446297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180324865657 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180324865657 / 125000000000) = 1/(125000000000 / 180324865657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4350 : Bounds (45805787 / 125000000) (366446297 / 1000000000) (Real.log (180324865657 / 125000000000)) := by
  have h := reflection_log_4350_neg
  have he : Real.log (180324865657 / 125000000000) = -Real.log (125000000000 / 180324865657) := by
    rw [show ((180324865657 / 125000000000) : ℝ) = ((125000000000 / 180324865657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4351_neg : (366653089 / 1000000000) ≤ -Real.log (100000000000 / 144289727617) ∧
    -Real.log (100000000000 / 144289727617) ≤ (36665309 / 100000000) := by
  have h := checkLog_sound (w := (44289727617 / 244289727617)) (n := 12)
    (lo := (366653089 / 1000000000)) (hi := (36665309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144289727617 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144289727617 / 100000000000) = 1/(100000000000 / 144289727617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4351 : Bounds (366653089 / 1000000000) (36665309 / 100000000) (Real.log (144289727617 / 100000000000)) := by
  have h := reflection_log_4351_neg
  have he : Real.log (144289727617 / 100000000000) = -Real.log (100000000000 / 144289727617) := by
    rw [show ((144289727617 / 100000000000) : ℝ) = ((100000000000 / 144289727617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
