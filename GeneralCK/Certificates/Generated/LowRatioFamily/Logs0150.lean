import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9600_neg : (161585247 / 1000000000) ≤ -Real.log (425397 / 500000) ∧
    -Real.log (425397 / 500000) ≤ (5049539 / 31250000) := by
  have h := checkLog_sound (w := (74603 / 925397)) (n := 12)
    (lo := (161585247 / 1000000000)) (hi := (5049539 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425397) = 1/(425397 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9600 : Bounds (-5049539 / 31250000) (-161585247 / 1000000000) (Real.log (425397 / 500000)) := by
  have h := reflection_log_9600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9601_neg : (27910471 / 200000000) ≤ -Real.log (1000000 / 1149759) ∧
    -Real.log (1000000 / 1149759) ≤ (34888089 / 250000000) := by
  have h := checkLog_sound (w := (149759 / 2149759)) (n := 12)
    (lo := (27910471 / 200000000)) (hi := (34888089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149759 / 1000000) = 1/(1000000 / 1149759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9601 : Bounds (27910471 / 200000000) (34888089 / 250000000) (Real.log (1149759 / 1000000)) := by
  have h := reflection_log_9601_neg
  have he : Real.log (1149759 / 1000000) = -Real.log (1000000 / 1149759) := by
    rw [show ((1149759 / 1000000) : ℝ) = ((1000000 / 1149759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9602_neg : (2027943 / 12500000) ≤ -Real.log (850241 / 1000000) ∧
    -Real.log (850241 / 1000000) ≤ (162235441 / 1000000000) := by
  have h := checkLog_sound (w := (149759 / 1850241)) (n := 12)
    (lo := (2027943 / 12500000)) (hi := (162235441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850241) = 1/(850241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9602 : Bounds (-162235441 / 1000000000) (-2027943 / 12500000) (Real.log (850241 / 1000000)) := by
  have h := reflection_log_9602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9603_neg : (4536617 / 200000000) ≤ -Real.log (977572241919 / 1000000000000) ∧
    -Real.log (977572241919 / 1000000000000) ≤ (11341543 / 500000000) := by
  have h := checkLog_sound (w := (22427758081 / 1977572241919)) (n := 12)
    (lo := (4536617 / 200000000)) (hi := (11341543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977572241919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977572241919) = 1/(977572241919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9603 : Bounds (-11341543 / 500000000) (-4536617 / 200000000) (Real.log (977572241919 / 1000000000000)) := by
  have h := reflection_log_9603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9604_neg : (11256989 / 500000000) ≤ -Real.log (244434392391 / 250000000000) ∧
    -Real.log (244434392391 / 250000000000) ≤ (22513979 / 1000000000) := by
  have h := checkLog_sound (w := (5565607609 / 494434392391)) (n := 12)
    (lo := (11256989 / 500000000)) (hi := (22513979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244434392391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244434392391) = 1/(244434392391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9604 : Bounds (-22513979 / 1000000000) (-11256989 / 500000000) (Real.log (244434392391 / 250000000000)) := by
  have h := reflection_log_9604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9605_neg : (75164129 / 250000000) ≤ -Real.log (500000000000 / 675372651899) ∧
    -Real.log (500000000000 / 675372651899) ≤ (300656517 / 1000000000) := by
  have h := checkLog_sound (w := (175372651899 / 1175372651899)) (n := 12)
    (lo := (75164129 / 250000000)) (hi := (300656517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675372651899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675372651899 / 500000000000) = 1/(500000000000 / 675372651899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9605 : Bounds (75164129 / 250000000) (300656517 / 1000000000) (Real.log (675372651899 / 500000000000)) := by
  have h := reflection_log_9605_neg
  have he : Real.log (675372651899 / 500000000000) = -Real.log (500000000000 / 675372651899) := by
    rw [show ((675372651899 / 500000000000) : ℝ) = ((500000000000 / 675372651899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9606_neg : (60357559 / 200000000) ≤ -Real.log (50000000000 / 67613711877) ∧
    -Real.log (50000000000 / 67613711877) ≤ (75446949 / 250000000) := by
  have h := checkLog_sound (w := (17613711877 / 117613711877)) (n := 12)
    (lo := (60357559 / 200000000)) (hi := (75446949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67613711877 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67613711877 / 50000000000) = 1/(50000000000 / 67613711877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9606 : Bounds (60357559 / 200000000) (75446949 / 250000000) (Real.log (67613711877 / 50000000000)) := by
  have h := reflection_log_9606_neg
  have he : Real.log (67613711877 / 50000000000) = -Real.log (50000000000 / 67613711877) := by
    rw [show ((67613711877 / 50000000000) : ℝ) = ((50000000000 / 67613711877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9607_neg : (605878237 / 1000000000) ≤ -Real.log (5000000000 / 9164305949) ∧
    -Real.log (5000000000 / 9164305949) ≤ (302939119 / 500000000) := by
  have h := checkLog_sound (w := (4164305949 / 14164305949)) (n := 12)
    (lo := (605878237 / 1000000000)) (hi := (302939119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9164305949 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9164305949 / 5000000000) = 1/(5000000000 / 9164305949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9607 : Bounds (605878237 / 1000000000) (302939119 / 500000000) (Real.log (9164305949 / 5000000000)) := by
  have h := reflection_log_9607_neg
  have he : Real.log (9164305949 / 5000000000) = -Real.log (5000000000 / 9164305949) := by
    rw [show ((9164305949 / 5000000000) : ℝ) = ((5000000000 / 9164305949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9608_neg : (606973027 / 1000000000) ≤ -Real.log (500000000000 / 917434443657) ∧
    -Real.log (500000000000 / 917434443657) ≤ (151743257 / 250000000) := by
  have h := checkLog_sound (w := (417434443657 / 1417434443657)) (n := 12)
    (lo := (606973027 / 1000000000)) (hi := (151743257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917434443657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917434443657 / 500000000000) = 1/(500000000000 / 917434443657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9608 : Bounds (606973027 / 1000000000) (151743257 / 250000000) (Real.log (917434443657 / 500000000000)) := by
  have h := reflection_log_9608_neg
  have he : Real.log (917434443657 / 500000000000) = -Real.log (500000000000 / 917434443657) := by
    rw [show ((917434443657 / 500000000000) : ℝ) = ((500000000000 / 917434443657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9609_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9609 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_9609_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9610_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9610 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_9610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9611_neg : (73739 / 250000000) ≤ -Real.log (200000 / 200059) ∧
    -Real.log (200000 / 200059) ≤ (294957 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 400059)) (n := 12)
    (lo := (73739 / 250000000)) (hi := (294957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200059 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200059 / 200000) = 1/(200000 / 200059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9611 : Bounds (73739 / 250000000) (294957 / 1000000000) (Real.log (200059 / 200000)) := by
  have h := reflection_log_9611_neg
  have he : Real.log (200059 / 200000) = -Real.log (200000 / 200059) := by
    rw [show ((200059 / 200000) : ℝ) = ((200000 / 200059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9612_neg : (295043 / 1000000000) ≤ -Real.log (199941 / 200000) ∧
    -Real.log (199941 / 200000) ≤ (73761 / 250000000) := by
  have h := checkLog_sound (w := (59 / 399941)) (n := 12)
    (lo := (295043 / 1000000000)) (hi := (73761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199941) = 1/(199941 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9612 : Bounds (-73761 / 250000000) (-295043 / 1000000000) (Real.log (199941 / 200000)) := by
  have h := reflection_log_9612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9613_neg : (69649613 / 500000000) ≤ -Real.log (250000 / 287367) ∧
    -Real.log (250000 / 287367) ≤ (139299227 / 1000000000) := by
  have h := checkLog_sound (w := (37367 / 537367)) (n := 12)
    (lo := (69649613 / 500000000)) (hi := (139299227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287367 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287367 / 250000) = 1/(250000 / 287367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9613 : Bounds (69649613 / 500000000) (139299227 / 1000000000) (Real.log (287367 / 250000)) := by
  have h := reflection_log_9613_neg
  have he : Real.log (287367 / 250000) = -Real.log (250000 / 287367) := by
    rw [show ((287367 / 250000) : ℝ) = ((250000 / 287367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9614_neg : (80946621 / 500000000) ≤ -Real.log (212633 / 250000) ∧
    -Real.log (212633 / 250000) ≤ (161893243 / 1000000000) := by
  have h := checkLog_sound (w := (37367 / 462633)) (n := 12)
    (lo := (80946621 / 500000000)) (hi := (161893243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212633) = 1/(212633 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9614 : Bounds (-161893243 / 1000000000) (-80946621 / 500000000) (Real.log (212633 / 250000)) := by
  have h := reflection_log_9614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9615_neg : (139780203 / 1000000000) ≤ -Real.log (1000000 / 1150021) ∧
    -Real.log (1000000 / 1150021) ≤ (34945051 / 250000000) := by
  have h := checkLog_sound (w := (150021 / 2150021)) (n := 12)
    (lo := (139780203 / 1000000000)) (hi := (34945051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150021 / 1000000) = 1/(1000000 / 1150021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9615 : Bounds (139780203 / 1000000000) (34945051 / 250000000) (Real.log (1150021 / 1000000)) := by
  have h := reflection_log_9615_neg
  have he : Real.log (1150021 / 1000000) = -Real.log (1000000 / 1150021) := by
    rw [show ((1150021 / 1000000) : ℝ) = ((1000000 / 1150021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9616_neg : (32508727 / 200000000) ≤ -Real.log (849979 / 1000000) ∧
    -Real.log (849979 / 1000000) ≤ (40635909 / 250000000) := by
  have h := checkLog_sound (w := (150021 / 1849979)) (n := 12)
    (lo := (32508727 / 200000000)) (hi := (40635909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849979) = 1/(849979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9616 : Bounds (-40635909 / 250000000) (-32508727 / 200000000) (Real.log (849979 / 1000000)) := by
  have h := reflection_log_9616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9617_neg : (2845429 / 125000000) ≤ -Real.log (977493699559 / 1000000000000) ∧
    -Real.log (977493699559 / 1000000000000) ≤ (22763433 / 1000000000) := by
  have h := checkLog_sound (w := (22506300441 / 1977493699559)) (n := 12)
    (lo := (2845429 / 125000000)) (hi := (22763433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977493699559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977493699559) = 1/(977493699559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9617 : Bounds (-22763433 / 1000000000) (-2845429 / 125000000) (Real.log (977493699559 / 1000000000000)) := by
  have h := reflection_log_9617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9618_neg : (706063 / 31250000) ≤ -Real.log (61103707311 / 62500000000) ∧
    -Real.log (61103707311 / 62500000000) ≤ (22594017 / 1000000000) := by
  have h := checkLog_sound (w := (1396292689 / 123603707311)) (n := 12)
    (lo := (706063 / 31250000)) (hi := (22594017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61103707311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61103707311) = 1/(61103707311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9618 : Bounds (-22594017 / 1000000000) (-706063 / 31250000) (Real.log (61103707311 / 62500000000)) := by
  have h := reflection_log_9618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9619_neg : (301192469 / 1000000000) ≤ -Real.log (31250000000 / 42233419789) ∧
    -Real.log (31250000000 / 42233419789) ≤ (30119247 / 100000000) := by
  have h := checkLog_sound (w := (10983419789 / 73483419789)) (n := 12)
    (lo := (301192469 / 1000000000)) (hi := (30119247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42233419789 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42233419789 / 31250000000) = 1/(31250000000 / 42233419789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9619 : Bounds (301192469 / 1000000000) (30119247 / 100000000) (Real.log (42233419789 / 31250000000)) := by
  have h := reflection_log_9619_neg
  have he : Real.log (42233419789 / 31250000000) = -Real.log (31250000000 / 42233419789) := by
    rw [show ((42233419789 / 31250000000) : ℝ) = ((31250000000 / 42233419789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9620_neg : (151161919 / 500000000) ≤ -Real.log (250000000000 / 338249827349) ∧
    -Real.log (250000000000 / 338249827349) ≤ (302323839 / 1000000000) := by
  have h := checkLog_sound (w := (88249827349 / 588249827349)) (n := 12)
    (lo := (151161919 / 500000000)) (hi := (302323839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338249827349 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338249827349 / 250000000000) = 1/(250000000000 / 338249827349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9620 : Bounds (151161919 / 500000000) (302323839 / 1000000000) (Real.log (338249827349 / 250000000000)) := by
  have h := reflection_log_9620_neg
  have he : Real.log (338249827349 / 250000000000) = -Real.log (250000000000 / 338249827349) := by
    rw [show ((338249827349 / 250000000000) : ℝ) = ((250000000000 / 338249827349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9621_neg : (606973027 / 1000000000) ≤ -Real.log (62500000000 / 114679305457) ∧
    -Real.log (62500000000 / 114679305457) ≤ (151743257 / 250000000) := by
  have h := checkLog_sound (w := (52179305457 / 177179305457)) (n := 12)
    (lo := (606973027 / 1000000000)) (hi := (151743257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114679305457 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114679305457 / 62500000000) = 1/(62500000000 / 114679305457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9621 : Bounds (606973027 / 1000000000) (151743257 / 250000000) (Real.log (114679305457 / 62500000000)) := by
  have h := reflection_log_9621_neg
  have he : Real.log (114679305457 / 62500000000) = -Real.log (62500000000 / 114679305457) := by
    rw [show ((114679305457 / 62500000000) : ℝ) = ((62500000000 / 114679305457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9622_neg : (608068171 / 1000000000) ≤ -Real.log (500000000000 / 918439716313) ∧
    -Real.log (500000000000 / 918439716313) ≤ (152017043 / 250000000) := by
  have h := checkLog_sound (w := (418439716313 / 1418439716313)) (n := 12)
    (lo := (608068171 / 1000000000)) (hi := (152017043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918439716313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918439716313 / 500000000000) = 1/(500000000000 / 918439716313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9622 : Bounds (608068171 / 1000000000) (152017043 / 250000000) (Real.log (918439716313 / 500000000000)) := by
  have h := reflection_log_9622_neg
  have he : Real.log (918439716313 / 500000000000) = -Real.log (500000000000 / 918439716313) := by
    rw [show ((918439716313 / 500000000000) : ℝ) = ((500000000000 / 918439716313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9623_neg : (258896721 / 1000000000) ≤ -Real.log (2000 / 2591) ∧
    -Real.log (2000 / 2591) ≤ (129448361 / 500000000) := by
  have h := checkLog_sound (w := (591 / 4591)) (n := 12)
    (lo := (258896721 / 1000000000)) (hi := (129448361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2591 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2591 / 2000) = 1/(2000 / 2591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9623 : Bounds (258896721 / 1000000000) (129448361 / 500000000) (Real.log (2591 / 2000)) := by
  have h := reflection_log_9623_neg
  have he : Real.log (2591 / 2000) = -Real.log (2000 / 2591) := by
    rw [show ((2591 / 2000) : ℝ) = ((2000 / 2591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9624_neg : (350266947 / 1000000000) ≤ -Real.log (1409 / 2000) ∧
    -Real.log (1409 / 2000) ≤ (87566737 / 250000000) := by
  have h := checkLog_sound (w := (591 / 3409)) (n := 12)
    (lo := (350266947 / 1000000000)) (hi := (87566737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1409) = 1/(1409 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9624 : Bounds (-87566737 / 250000000) (-350266947 / 1000000000) (Real.log (1409 / 2000)) := by
  have h := reflection_log_9624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9625_neg : (9233 / 31250000) ≤ -Real.log (2000000 / 2000591) ∧
    -Real.log (2000000 / 2000591) ≤ (295457 / 1000000000) := by
  have h := checkLog_sound (w := (591 / 4000591)) (n := 12)
    (lo := (9233 / 31250000)) (hi := (295457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000591 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000591 / 2000000) = 1/(2000000 / 2000591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9625 : Bounds (9233 / 31250000) (295457 / 1000000000) (Real.log (2000591 / 2000000)) := by
  have h := reflection_log_9625_neg
  have he : Real.log (2000591 / 2000000) = -Real.log (2000000 / 2000591) := by
    rw [show ((2000591 / 2000000) : ℝ) = ((2000000 / 2000591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9626_neg : (295543 / 1000000000) ≤ -Real.log (1999409 / 2000000) ∧
    -Real.log (1999409 / 2000000) ≤ (36943 / 125000000) := by
  have h := checkLog_sound (w := (591 / 3999409)) (n := 12)
    (lo := (295543 / 1000000000)) (hi := (36943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999409) = 1/(1999409 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9626 : Bounds (-36943 / 125000000) (-295543 / 1000000000) (Real.log (1999409 / 2000000)) := by
  have h := reflection_log_9626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9627_neg : (34881783 / 250000000) ≤ -Real.log (100000 / 114973) ∧
    -Real.log (100000 / 114973) ≤ (139527133 / 1000000000) := by
  have h := checkLog_sound (w := (14973 / 214973)) (n := 12)
    (lo := (34881783 / 250000000)) (hi := (139527133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114973 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114973 / 100000) = 1/(100000 / 114973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9627 : Bounds (34881783 / 250000000) (139527133 / 1000000000) (Real.log (114973 / 100000)) := by
  have h := reflection_log_9627_neg
  have he : Real.log (114973 / 100000) = -Real.log (100000 / 114973) := by
    rw [show ((114973 / 100000) : ℝ) = ((100000 / 114973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9628_neg : (40550333 / 250000000) ≤ -Real.log (85027 / 100000) ∧
    -Real.log (85027 / 100000) ≤ (162201333 / 1000000000) := by
  have h := checkLog_sound (w := (14973 / 185027)) (n := 12)
    (lo := (40550333 / 250000000)) (hi := (162201333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85027) = 1/(85027 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9628 : Bounds (-162201333 / 1000000000) (-40550333 / 250000000) (Real.log (85027 / 100000)) := by
  have h := reflection_log_9628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9629_neg : (35002217 / 250000000) ≤ -Real.log (250000 / 287571) ∧
    -Real.log (250000 / 287571) ≤ (140008869 / 1000000000) := by
  have h := checkLog_sound (w := (37571 / 537571)) (n := 12)
    (lo := (35002217 / 250000000)) (hi := (140008869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287571 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287571 / 250000) = 1/(250000 / 287571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9629 : Bounds (35002217 / 250000000) (140008869 / 1000000000) (Real.log (287571 / 250000)) := by
  have h := reflection_log_9629_neg
  have he : Real.log (287571 / 250000) = -Real.log (250000 / 287571) := by
    rw [show ((287571 / 250000) : ℝ) = ((250000 / 287571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9630_neg : (81426551 / 500000000) ≤ -Real.log (212429 / 250000) ∧
    -Real.log (212429 / 250000) ≤ (162853103 / 1000000000) := by
  have h := checkLog_sound (w := (37571 / 462429)) (n := 12)
    (lo := (81426551 / 500000000)) (hi := (162853103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212429) = 1/(212429 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9630 : Bounds (-162853103 / 1000000000) (-81426551 / 500000000) (Real.log (212429 / 250000)) := by
  have h := reflection_log_9630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9631_neg : (11422117 / 500000000) ≤ -Real.log (61088419959 / 62500000000) ∧
    -Real.log (61088419959 / 62500000000) ≤ (4568847 / 200000000) := by
  have h := checkLog_sound (w := (1411580041 / 123588419959)) (n := 12)
    (lo := (11422117 / 500000000)) (hi := (4568847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61088419959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61088419959) = 1/(61088419959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9631 : Bounds (-4568847 / 200000000) (-11422117 / 500000000) (Real.log (61088419959 / 62500000000)) := by
  have h := reflection_log_9631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9632_neg : (113371 / 5000000) ≤ -Real.log (9775809271 / 10000000000) ∧
    -Real.log (9775809271 / 10000000000) ≤ (22674201 / 1000000000) := by
  have h := checkLog_sound (w := (224190729 / 19775809271)) (n := 12)
    (lo := (113371 / 5000000)) (hi := (22674201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9775809271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9775809271) = 1/(9775809271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9632 : Bounds (-22674201 / 1000000000) (-113371 / 5000000) (Real.log (9775809271 / 10000000000)) := by
  have h := reflection_log_9632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9633_neg : (60345693 / 200000000) ≤ -Real.log (1562500000 / 2112803139) ∧
    -Real.log (1562500000 / 2112803139) ≤ (150864233 / 500000000) := by
  have h := checkLog_sound (w := (550303139 / 3675303139)) (n := 12)
    (lo := (60345693 / 200000000)) (hi := (150864233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2112803139 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2112803139 / 1562500000) = 1/(1562500000 / 2112803139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9633 : Bounds (60345693 / 200000000) (150864233 / 500000000) (Real.log (2112803139 / 1562500000)) := by
  have h := reflection_log_9633_neg
  have he : Real.log (2112803139 / 1562500000) = -Real.log (1562500000 / 2112803139) := by
    rw [show ((2112803139 / 1562500000) : ℝ) = ((1562500000 / 2112803139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9634_neg : (302861971 / 1000000000) ≤ -Real.log (500000000000 / 676863799199) ∧
    -Real.log (500000000000 / 676863799199) ≤ (75715493 / 250000000) := by
  have h := checkLog_sound (w := (176863799199 / 1176863799199)) (n := 12)
    (lo := (302861971 / 1000000000)) (hi := (75715493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676863799199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676863799199 / 500000000000) = 1/(500000000000 / 676863799199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9634 : Bounds (302861971 / 1000000000) (75715493 / 250000000) (Real.log (676863799199 / 500000000000)) := by
  have h := reflection_log_9634_neg
  have he : Real.log (676863799199 / 500000000000) = -Real.log (500000000000 / 676863799199) := by
    rw [show ((676863799199 / 500000000000) : ℝ) = ((500000000000 / 676863799199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9635_neg : (608068171 / 1000000000) ≤ -Real.log (62500000000 / 114804964539) ∧
    -Real.log (62500000000 / 114804964539) ≤ (152017043 / 250000000) := by
  have h := checkLog_sound (w := (52304964539 / 177304964539)) (n := 12)
    (lo := (608068171 / 1000000000)) (hi := (152017043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114804964539 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114804964539 / 62500000000) = 1/(62500000000 / 114804964539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9635 : Bounds (608068171 / 1000000000) (152017043 / 250000000) (Real.log (114804964539 / 62500000000)) := by
  have h := reflection_log_9635_neg
  have he : Real.log (114804964539 / 62500000000) = -Real.log (62500000000 / 114804964539) := by
    rw [show ((114804964539 / 62500000000) : ℝ) = ((62500000000 / 114804964539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9636_neg : (152290917 / 250000000) ≤ -Real.log (250000000000 / 459723207949) ∧
    -Real.log (250000000000 / 459723207949) ≤ (609163669 / 1000000000) := by
  have h := checkLog_sound (w := (209723207949 / 709723207949)) (n := 12)
    (lo := (152290917 / 250000000)) (hi := (609163669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459723207949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459723207949 / 250000000000) = 1/(250000000000 / 459723207949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9636 : Bounds (152290917 / 250000000) (609163669 / 1000000000) (Real.log (459723207949 / 250000000000)) := by
  have h := reflection_log_9636_neg
  have he : Real.log (459723207949 / 250000000000) = -Real.log (250000000000 / 459723207949) := by
    rw [show ((459723207949 / 250000000000) : ℝ) = ((250000000000 / 459723207949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9637_neg : (259282597 / 1000000000) ≤ -Real.log (125 / 162) ∧
    -Real.log (125 / 162) ≤ (129641299 / 500000000) := by
  have h := checkLog_sound (w := (37 / 287)) (n := 12)
    (lo := (259282597 / 1000000000)) (hi := (129641299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162 / 125) = 1/(125 / 162) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9637 : Bounds (259282597 / 1000000000) (129641299 / 500000000) (Real.log (162 / 125)) := by
  have h := reflection_log_9637_neg
  have he : Real.log (162 / 125) = -Real.log (125 / 162) := by
    rw [show ((162 / 125) : ℝ) = ((125 / 162) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9638_neg : (175488461 / 500000000) ≤ -Real.log (88 / 125) ∧
    -Real.log (88 / 125) ≤ (350976923 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 88) = 1/(88 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9638 : Bounds (-350976923 / 1000000000) (-175488461 / 500000000) (Real.log (88 / 125)) := by
  have h := reflection_log_9638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9639_neg : (73989 / 250000000) ≤ -Real.log (125000 / 125037) ∧
    -Real.log (125000 / 125037) ≤ (295957 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 250037)) (n := 12)
    (lo := (73989 / 250000000)) (hi := (295957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125037 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125037 / 125000) = 1/(125000 / 125037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9639 : Bounds (73989 / 250000000) (295957 / 1000000000) (Real.log (125037 / 125000)) := by
  have h := reflection_log_9639_neg
  have he : Real.log (125037 / 125000) = -Real.log (125000 / 125037) := by
    rw [show ((125037 / 125000) : ℝ) = ((125000 / 125037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9640_neg : (296043 / 1000000000) ≤ -Real.log (124963 / 125000) ∧
    -Real.log (124963 / 125000) ≤ (74011 / 250000000) := by
  have h := checkLog_sound (w := (37 / 249963)) (n := 12)
    (lo := (296043 / 1000000000)) (hi := (74011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124963) = 1/(124963 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9640 : Bounds (-74011 / 250000000) (-296043 / 1000000000) (Real.log (124963 / 125000)) := by
  have h := reflection_log_9640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9641_neg : (27950997 / 200000000) ≤ -Real.log (125000 / 143749) ∧
    -Real.log (125000 / 143749) ≤ (69877493 / 500000000) := by
  have h := checkLog_sound (w := (18749 / 268749)) (n := 12)
    (lo := (27950997 / 200000000)) (hi := (69877493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143749 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143749 / 125000) = 1/(125000 / 143749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9641 : Bounds (27950997 / 200000000) (69877493 / 500000000) (Real.log (143749 / 125000)) := by
  have h := reflection_log_9641_neg
  have he : Real.log (143749 / 125000) = -Real.log (125000 / 143749) := by
    rw [show ((143749 / 125000) : ℝ) = ((125000 / 143749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9642_neg : (162509517 / 1000000000) ≤ -Real.log (106251 / 125000) ∧
    -Real.log (106251 / 125000) ≤ (81254759 / 500000000) := by
  have h := checkLog_sound (w := (18749 / 231251)) (n := 12)
    (lo := (162509517 / 1000000000)) (hi := (81254759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106251) = 1/(106251 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9642 : Bounds (-81254759 / 500000000) (-162509517 / 1000000000) (Real.log (106251 / 125000)) := by
  have h := reflection_log_9642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9643_neg : (140237481 / 1000000000) ≤ -Real.log (1000000 / 1150547) ∧
    -Real.log (1000000 / 1150547) ≤ (70118741 / 500000000) := by
  have h := checkLog_sound (w := (150547 / 2150547)) (n := 12)
    (lo := (140237481 / 1000000000)) (hi := (70118741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150547 / 1000000) = 1/(1000000 / 1150547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9643 : Bounds (140237481 / 1000000000) (70118741 / 500000000) (Real.log (1150547 / 1000000)) := by
  have h := reflection_log_9643_neg
  have he : Real.log (1150547 / 1000000) = -Real.log (1000000 / 1150547) := by
    rw [show ((1150547 / 1000000) : ℝ) = ((1000000 / 1150547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9644_neg : (81581333 / 500000000) ≤ -Real.log (849453 / 1000000) ∧
    -Real.log (849453 / 1000000) ≤ (163162667 / 1000000000) := by
  have h := checkLog_sound (w := (150547 / 1849453)) (n := 12)
    (lo := (81581333 / 500000000)) (hi := (163162667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849453) = 1/(849453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9644 : Bounds (-163162667 / 1000000000) (-81581333 / 500000000) (Real.log (849453 / 1000000)) := by
  have h := reflection_log_9644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9645_neg : (179103 / 7812500) ≤ -Real.log (977335600791 / 1000000000000) ∧
    -Real.log (977335600791 / 1000000000000) ≤ (4585037 / 200000000) := by
  have h := checkLog_sound (w := (22664399209 / 1977335600791)) (n := 12)
    (lo := (179103 / 7812500)) (hi := (4585037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977335600791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977335600791) = 1/(977335600791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9645 : Bounds (-4585037 / 200000000) (-179103 / 7812500) (Real.log (977335600791 / 1000000000000)) := by
  have h := reflection_log_9645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9646_neg : (22754531 / 1000000000) ≤ -Real.log (15273474999 / 15625000000) ∧
    -Real.log (15273474999 / 15625000000) ≤ (5688633 / 250000000) := by
  have h := checkLog_sound (w := (351525001 / 30898474999)) (n := 12)
    (lo := (22754531 / 1000000000)) (hi := (5688633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15273474999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15273474999) = 1/(15273474999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9646 : Bounds (-5688633 / 250000000) (-22754531 / 1000000000) (Real.log (15273474999 / 15625000000)) := by
  have h := reflection_log_9646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9647_neg : (302264503 / 1000000000) ≤ -Real.log (20000000000 / 27058380627) ∧
    -Real.log (20000000000 / 27058380627) ≤ (37783063 / 125000000) := by
  have h := checkLog_sound (w := (7058380627 / 47058380627)) (n := 12)
    (lo := (302264503 / 1000000000)) (hi := (37783063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27058380627 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27058380627 / 20000000000) = 1/(20000000000 / 27058380627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9647 : Bounds (302264503 / 1000000000) (37783063 / 125000000) (Real.log (27058380627 / 20000000000)) := by
  have h := reflection_log_9647_neg
  have he : Real.log (27058380627 / 20000000000) = -Real.log (20000000000 / 27058380627) := by
    rw [show ((27058380627 / 20000000000) : ℝ) = ((20000000000 / 27058380627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9648_neg : (303400147 / 1000000000) ≤ -Real.log (500000000000 / 677228169187) ∧
    -Real.log (500000000000 / 677228169187) ≤ (75850037 / 250000000) := by
  have h := checkLog_sound (w := (177228169187 / 1177228169187)) (n := 12)
    (lo := (303400147 / 1000000000)) (hi := (75850037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677228169187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677228169187 / 500000000000) = 1/(500000000000 / 677228169187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9648 : Bounds (303400147 / 1000000000) (75850037 / 250000000) (Real.log (677228169187 / 500000000000)) := by
  have h := reflection_log_9648_neg
  have he : Real.log (677228169187 / 500000000000) = -Real.log (500000000000 / 677228169187) := by
    rw [show ((677228169187 / 500000000000) : ℝ) = ((500000000000 / 677228169187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9649_neg : (152290917 / 250000000) ≤ -Real.log (500000000000 / 919446415897) ∧
    -Real.log (500000000000 / 919446415897) ≤ (609163669 / 1000000000) := by
  have h := checkLog_sound (w := (419446415897 / 1419446415897)) (n := 12)
    (lo := (152290917 / 250000000)) (hi := (609163669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919446415897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919446415897 / 500000000000) = 1/(500000000000 / 919446415897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9649 : Bounds (152290917 / 250000000) (609163669 / 1000000000) (Real.log (919446415897 / 500000000000)) := by
  have h := reflection_log_9649_neg
  have he : Real.log (919446415897 / 500000000000) = -Real.log (500000000000 / 919446415897) := by
    rw [show ((919446415897 / 500000000000) : ℝ) = ((500000000000 / 919446415897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9650_neg : (1907061 / 3125000) ≤ -Real.log (100000000000 / 184090909091) ∧
    -Real.log (100000000000 / 184090909091) ≤ (610259521 / 1000000000) := by
  have h := checkLog_sound (w := (84090909091 / 284090909091)) (n := 12)
    (lo := (1907061 / 3125000)) (hi := (610259521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184090909091 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184090909091 / 100000000000) = 1/(100000000000 / 184090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9650 : Bounds (1907061 / 3125000) (610259521 / 1000000000) (Real.log (184090909091 / 100000000000)) := by
  have h := reflection_log_9650_neg
  have he : Real.log (184090909091 / 100000000000) = -Real.log (100000000000 / 184090909091) := by
    rw [show ((184090909091 / 100000000000) : ℝ) = ((100000000000 / 184090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9651_neg : (10386733 / 40000000) ≤ -Real.log (2000 / 2593) ∧
    -Real.log (2000 / 2593) ≤ (129834163 / 500000000) := by
  have h := checkLog_sound (w := (593 / 4593)) (n := 12)
    (lo := (10386733 / 40000000)) (hi := (129834163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2593 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2593 / 2000) = 1/(2000 / 2593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9651 : Bounds (10386733 / 40000000) (129834163 / 500000000) (Real.log (2593 / 2000)) := by
  have h := reflection_log_9651_neg
  have he : Real.log (2593 / 2000) = -Real.log (2000 / 2593) := by
    rw [show ((2593 / 2000) : ℝ) = ((2000 / 2593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9652_neg : (175843701 / 500000000) ≤ -Real.log (1407 / 2000) ∧
    -Real.log (1407 / 2000) ≤ (351687403 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 3407)) (n := 12)
    (lo := (175843701 / 500000000)) (hi := (351687403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1407) = 1/(1407 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9652 : Bounds (-351687403 / 1000000000) (-175843701 / 500000000) (Real.log (1407 / 2000)) := by
  have h := reflection_log_9652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9653_neg : (37057 / 125000000) ≤ -Real.log (2000000 / 2000593) ∧
    -Real.log (2000000 / 2000593) ≤ (296457 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 4000593)) (n := 12)
    (lo := (37057 / 125000000)) (hi := (296457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000593 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000593 / 2000000) = 1/(2000000 / 2000593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9653 : Bounds (37057 / 125000000) (296457 / 1000000000) (Real.log (2000593 / 2000000)) := by
  have h := reflection_log_9653_neg
  have he : Real.log (2000593 / 2000000) = -Real.log (2000000 / 2000593) := by
    rw [show ((2000593 / 2000000) : ℝ) = ((2000000 / 2000593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9654_neg : (296543 / 1000000000) ≤ -Real.log (1999407 / 2000000) ∧
    -Real.log (1999407 / 2000000) ≤ (9267 / 31250000) := by
  have h := checkLog_sound (w := (593 / 3999407)) (n := 12)
    (lo := (296543 / 1000000000)) (hi := (9267 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999407) = 1/(1999407 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9654 : Bounds (-9267 / 31250000) (-296543 / 1000000000) (Real.log (1999407 / 2000000)) := by
  have h := reflection_log_9654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9655_neg : (17497957 / 125000000) ≤ -Real.log (200000 / 230051) ∧
    -Real.log (200000 / 230051) ≤ (139983657 / 1000000000) := by
  have h := checkLog_sound (w := (30051 / 430051)) (n := 12)
    (lo := (17497957 / 125000000)) (hi := (139983657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230051 / 200000) = 1/(200000 / 230051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9655 : Bounds (17497957 / 125000000) (139983657 / 1000000000) (Real.log (230051 / 200000)) := by
  have h := reflection_log_9655_neg
  have he : Real.log (230051 / 200000) = -Real.log (200000 / 230051) := by
    rw [show ((230051 / 200000) : ℝ) = ((200000 / 230051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9656_neg : (81409487 / 500000000) ≤ -Real.log (169949 / 200000) ∧
    -Real.log (169949 / 200000) ≤ (6512759 / 40000000) := by
  have h := checkLog_sound (w := (30051 / 369949)) (n := 12)
    (lo := (81409487 / 500000000)) (hi := (6512759 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169949) = 1/(169949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9656 : Bounds (-6512759 / 40000000) (-81409487 / 500000000) (Real.log (169949 / 200000)) := by
  have h := reflection_log_9656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9657_neg : (140465173 / 1000000000) ≤ -Real.log (1000000 / 1150809) ∧
    -Real.log (1000000 / 1150809) ≤ (70232587 / 500000000) := by
  have h := checkLog_sound (w := (150809 / 2150809)) (n := 12)
    (lo := (140465173 / 1000000000)) (hi := (70232587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150809 / 1000000) = 1/(1000000 / 1150809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9657 : Bounds (140465173 / 1000000000) (70232587 / 500000000) (Real.log (1150809 / 1000000)) := by
  have h := reflection_log_9657_neg
  have he : Real.log (1150809 / 1000000) = -Real.log (1000000 / 1150809) := by
    rw [show ((1150809 / 1000000) : ℝ) = ((1000000 / 1150809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9658_neg : (163471147 / 1000000000) ≤ -Real.log (849191 / 1000000) ∧
    -Real.log (849191 / 1000000) ≤ (40867787 / 250000000) := by
  have h := checkLog_sound (w := (150809 / 1849191)) (n := 12)
    (lo := (163471147 / 1000000000)) (hi := (40867787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849191) = 1/(849191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9658 : Bounds (-40867787 / 250000000) (-163471147 / 1000000000) (Real.log (849191 / 1000000)) := by
  have h := reflection_log_9658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9659_neg : (11502987 / 500000000) ≤ -Real.log (977256645519 / 1000000000000) ∧
    -Real.log (977256645519 / 1000000000000) ≤ (920239 / 40000000) := by
  have h := checkLog_sound (w := (22743354481 / 1977256645519)) (n := 12)
    (lo := (11502987 / 500000000)) (hi := (920239 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977256645519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977256645519) = 1/(977256645519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9659 : Bounds (-920239 / 40000000) (-11502987 / 500000000) (Real.log (977256645519 / 1000000000000)) := by
  have h := reflection_log_9659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9660_neg : (22835317 / 1000000000) ≤ -Real.log (39096937399 / 40000000000) ∧
    -Real.log (39096937399 / 40000000000) ≤ (11417659 / 500000000) := by
  have h := checkLog_sound (w := (903062601 / 79096937399)) (n := 12)
    (lo := (22835317 / 1000000000)) (hi := (11417659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39096937399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39096937399) = 1/(39096937399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9660 : Bounds (-11417659 / 500000000) (-22835317 / 1000000000) (Real.log (39096937399 / 40000000000)) := by
  have h := reflection_log_9660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9661_neg : (302802631 / 1000000000) ≤ -Real.log (20000000000 / 27072945413) ∧
    -Real.log (20000000000 / 27072945413) ≤ (37850329 / 125000000) := by
  have h := checkLog_sound (w := (7072945413 / 47072945413)) (n := 12)
    (lo := (302802631 / 1000000000)) (hi := (37850329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27072945413 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27072945413 / 20000000000) = 1/(20000000000 / 27072945413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9661 : Bounds (302802631 / 1000000000) (37850329 / 125000000) (Real.log (27072945413 / 20000000000)) := by
  have h := reflection_log_9661_neg
  have he : Real.log (27072945413 / 20000000000) = -Real.log (20000000000 / 27072945413) := by
    rw [show ((27072945413 / 20000000000) : ℝ) = ((20000000000 / 27072945413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9662_neg : (949801 / 3125000) ≤ -Real.log (500000000000 / 677591378147) ∧
    -Real.log (500000000000 / 677591378147) ≤ (303936321 / 1000000000) := by
  have h := checkLog_sound (w := (177591378147 / 1177591378147)) (n := 12)
    (lo := (949801 / 3125000)) (hi := (303936321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677591378147 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677591378147 / 500000000000) = 1/(500000000000 / 677591378147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9662 : Bounds (949801 / 3125000) (303936321 / 1000000000) (Real.log (677591378147 / 500000000000)) := by
  have h := reflection_log_9662_neg
  have he : Real.log (677591378147 / 500000000000) = -Real.log (500000000000 / 677591378147) := by
    rw [show ((677591378147 / 500000000000) : ℝ) = ((500000000000 / 677591378147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9663_neg : (1907061 / 3125000) ≤ -Real.log (250000000000 / 460227272727) ∧
    -Real.log (250000000000 / 460227272727) ≤ (610259521 / 1000000000) := by
  have h := checkLog_sound (w := (210227272727 / 710227272727)) (n := 12)
    (lo := (1907061 / 3125000)) (hi := (610259521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((460227272727 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(460227272727 / 250000000000) = 1/(250000000000 / 460227272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9663 : Bounds (1907061 / 3125000) (610259521 / 1000000000) (Real.log (460227272727 / 250000000000)) := by
  have h := reflection_log_9663_neg
  have he : Real.log (460227272727 / 250000000000) = -Real.log (250000000000 / 460227272727) := by
    rw [show ((460227272727 / 250000000000) : ℝ) = ((250000000000 / 460227272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
