import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10944_neg : (16236663 / 20000000) ≤ -Real.log (500000000000 / 1126016260163) ∧
    -Real.log (500000000000 / 1126016260163) ≤ (12684893 / 15625000) := by
  have h := checkLog_sound (w := (126016260163 / 2126016260163)) (n := 12)
    (lo := (11868597 / 100000000)) (hi := (118685971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1126016260163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1126016260163 / 1000000000000) = 1/(500000000000 / 1126016260163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10944 : Bounds (16236663 / 20000000) (12684893 / 15625000) (Real.log (1126016260163 / 500000000000)) := by
  have h := reflection_log_10944_neg
  have he : Real.log (1126016260163 / 500000000000) = -Real.log (500000000000 / 1126016260163) := by
    rw [show ((1126016260163 / 500000000000) : ℝ) = ((500000000000 / 1126016260163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10945_neg : (3264219 / 10000000) ≤ -Real.log (500 / 693) ∧
    -Real.log (500 / 693) ≤ (326421901 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1193)) (n := 12)
    (lo := (3264219 / 10000000)) (hi := (326421901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 500) = 1/(500 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10945 : Bounds (3264219 / 10000000) (326421901 / 1000000000) (Real.log (693 / 500)) := by
  have h := reflection_log_10945_neg
  have he : Real.log (693 / 500) = -Real.log (500 / 693) := by
    rw [show ((693 / 500) : ℝ) = ((500 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10946_neg : (9755207 / 20000000) ≤ -Real.log (307 / 500) ∧
    -Real.log (307 / 500) ≤ (487760351 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 807)) (n := 12)
    (lo := (9755207 / 20000000)) (hi := (487760351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 307) = 1/(307 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10946 : Bounds (-487760351 / 1000000000) (-9755207 / 20000000) (Real.log (307 / 500)) := by
  have h := reflection_log_10946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10947_neg : (15437 / 40000000) ≤ -Real.log (500000 / 500193) ∧
    -Real.log (500000 / 500193) ≤ (192963 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1000193)) (n := 12)
    (lo := (15437 / 40000000)) (hi := (192963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500193 / 500000) = 1/(500000 / 500193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10947 : Bounds (15437 / 40000000) (192963 / 500000000) (Real.log (500193 / 500000)) := by
  have h := reflection_log_10947_neg
  have he : Real.log (500193 / 500000) = -Real.log (500000 / 500193) := by
    rw [show ((500193 / 500000) : ℝ) = ((500000 / 500193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10948_neg : (193037 / 500000000) ≤ -Real.log (499807 / 500000) ∧
    -Real.log (499807 / 500000) ≤ (15443 / 40000000) := by
  have h := checkLog_sound (w := (193 / 999807)) (n := 12)
    (lo := (193037 / 500000000)) (hi := (15443 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499807) = 1/(499807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10948 : Bounds (-15443 / 40000000) (-193037 / 500000000) (Real.log (499807 / 500000)) := by
  have h := reflection_log_10948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10949_neg : (180399711 / 1000000000) ≤ -Real.log (15625 / 18714) ∧
    -Real.log (15625 / 18714) ≤ (5637491 / 31250000) := by
  have h := checkLog_sound (w := (3089 / 34339)) (n := 12)
    (lo := (180399711 / 1000000000)) (hi := (5637491 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18714 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18714 / 15625) = 1/(15625 / 18714) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10949 : Bounds (180399711 / 1000000000) (5637491 / 31250000) (Real.log (18714 / 15625)) := by
  have h := reflection_log_10949_neg
  have he : Real.log (18714 / 15625) = -Real.log (15625 / 18714) := by
    rw [show ((18714 / 15625) : ℝ) = ((15625 / 18714) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10950_neg : (22026769 / 100000000) ≤ -Real.log (12536 / 15625) ∧
    -Real.log (12536 / 15625) ≤ (220267691 / 1000000000) := by
  have h := checkLog_sound (w := (3089 / 28161)) (n := 12)
    (lo := (22026769 / 100000000)) (hi := (220267691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12536) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12536) = 1/(12536 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10950 : Bounds (-220267691 / 1000000000) (-22026769 / 100000000) (Real.log (12536 / 15625)) := by
  have h := reflection_log_10950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10951_neg : (181166723 / 1000000000) ≤ -Real.log (200000 / 239723) ∧
    -Real.log (200000 / 239723) ≤ (45291681 / 250000000) := by
  have h := checkLog_sound (w := (39723 / 439723)) (n := 12)
    (lo := (181166723 / 1000000000)) (hi := (45291681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239723 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239723 / 200000) = 1/(200000 / 239723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10951 : Bounds (181166723 / 1000000000) (45291681 / 250000000) (Real.log (239723 / 200000)) := by
  have h := reflection_log_10951_neg
  have he : Real.log (239723 / 200000) = -Real.log (200000 / 239723) := by
    rw [show ((239723 / 200000) : ℝ) = ((200000 / 239723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10952_neg : (110706899 / 500000000) ≤ -Real.log (160277 / 200000) ∧
    -Real.log (160277 / 200000) ≤ (221413799 / 1000000000) := by
  have h := checkLog_sound (w := (39723 / 360277)) (n := 12)
    (lo := (110706899 / 500000000)) (hi := (221413799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160277) = 1/(160277 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10952 : Bounds (-221413799 / 1000000000) (-110706899 / 500000000) (Real.log (160277 / 200000)) := by
  have h := reflection_log_10952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10953_neg : (20123537 / 500000000) ≤ -Real.log (38422083271 / 40000000000) ∧
    -Real.log (38422083271 / 40000000000) ≤ (1609883 / 40000000) := by
  have h := checkLog_sound (w := (1577916729 / 78422083271)) (n := 12)
    (lo := (20123537 / 500000000)) (hi := (1609883 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38422083271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38422083271) = 1/(38422083271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10953 : Bounds (-1609883 / 40000000) (-20123537 / 500000000) (Real.log (38422083271 / 40000000000)) := by
  have h := reflection_log_10953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10954_neg : (39867979 / 1000000000) ≤ -Real.log (234598704 / 244140625) ∧
    -Real.log (234598704 / 244140625) ≤ (1993399 / 50000000) := by
  have h := checkLog_sound (w := (9541921 / 478739329)) (n := 12)
    (lo := (39867979 / 1000000000)) (hi := (1993399 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 234598704) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 234598704) = 1/(234598704 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10954 : Bounds (-1993399 / 50000000) (-39867979 / 1000000000) (Real.log (234598704 / 244140625)) := by
  have h := reflection_log_10954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10955_neg : (400667401 / 1000000000) ≤ -Real.log (20000000000 / 29856413529) ∧
    -Real.log (20000000000 / 29856413529) ≤ (200333701 / 500000000) := by
  have h := checkLog_sound (w := (9856413529 / 49856413529)) (n := 12)
    (lo := (400667401 / 1000000000)) (hi := (200333701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29856413529 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29856413529 / 20000000000) = 1/(20000000000 / 29856413529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10955 : Bounds (400667401 / 1000000000) (200333701 / 500000000) (Real.log (29856413529 / 20000000000)) := by
  have h := reflection_log_10955_neg
  have he : Real.log (29856413529 / 20000000000) = -Real.log (20000000000 / 29856413529) := by
    rw [show ((29856413529 / 20000000000) : ℝ) = ((20000000000 / 29856413529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10956_neg : (402580521 / 1000000000) ≤ -Real.log (500000000000 / 747839677559) ∧
    -Real.log (500000000000 / 747839677559) ≤ (201290261 / 500000000) := by
  have h := checkLog_sound (w := (247839677559 / 1247839677559)) (n := 12)
    (lo := (402580521 / 1000000000)) (hi := (201290261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747839677559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747839677559 / 500000000000) = 1/(500000000000 / 747839677559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10956 : Bounds (402580521 / 1000000000) (201290261 / 500000000) (Real.log (747839677559 / 500000000000)) := by
  have h := reflection_log_10956_neg
  have he : Real.log (747839677559 / 500000000000) = -Real.log (500000000000 / 747839677559) := by
    rw [show ((747839677559 / 500000000000) : ℝ) = ((500000000000 / 747839677559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10957_neg : (16236663 / 20000000) ≤ -Real.log (250000000000 / 563008130081) ∧
    -Real.log (250000000000 / 563008130081) ≤ (12684893 / 15625000) := by
  have h := checkLog_sound (w := (63008130081 / 1063008130081)) (n := 12)
    (lo := (11868597 / 100000000)) (hi := (118685971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563008130081 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563008130081 / 500000000000) = 1/(250000000000 / 563008130081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10957 : Bounds (16236663 / 20000000) (12684893 / 15625000) (Real.log (563008130081 / 250000000000)) := by
  have h := reflection_log_10957_neg
  have he : Real.log (563008130081 / 250000000000) = -Real.log (250000000000 / 563008130081) := by
    rw [show ((563008130081 / 250000000000) : ℝ) = ((250000000000 / 563008130081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10958_neg : (814182251 / 1000000000) ≤ -Real.log (100000000000 / 225732899023) ∧
    -Real.log (100000000000 / 225732899023) ≤ (814182253 / 1000000000) := by
  have h := checkLog_sound (w := (25732899023 / 425732899023)) (n := 12)
    (lo := (121035071 / 1000000000)) (hi := (1891173 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225732899023 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(225732899023 / 200000000000) = 1/(100000000000 / 225732899023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10958 : Bounds (814182251 / 1000000000) (814182253 / 1000000000) (Real.log (225732899023 / 100000000000)) := by
  have h := reflection_log_10958_neg
  have he : Real.log (225732899023 / 100000000000) = -Real.log (100000000000 / 225732899023) := by
    rw [show ((225732899023 / 100000000000) : ℝ) = ((100000000000 / 225732899023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10959_neg : (327143141 / 1000000000) ≤ -Real.log (1000 / 1387) ∧
    -Real.log (1000 / 1387) ≤ (163571571 / 500000000) := by
  have h := checkLog_sound (w := (387 / 2387)) (n := 12)
    (lo := (327143141 / 1000000000)) (hi := (163571571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1387 / 1000) = 1/(1000 / 1387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10959 : Bounds (327143141 / 1000000000) (163571571 / 500000000) (Real.log (1387 / 1000)) := by
  have h := reflection_log_10959_neg
  have he : Real.log (1387 / 1000) = -Real.log (1000 / 1387) := by
    rw [show ((1387 / 1000) : ℝ) = ((1000 / 1387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10960_neg : (489390343 / 1000000000) ≤ -Real.log (613 / 1000) ∧
    -Real.log (613 / 1000) ≤ (61173793 / 125000000) := by
  have h := checkLog_sound (w := (387 / 1613)) (n := 12)
    (lo := (489390343 / 1000000000)) (hi := (61173793 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 613) = 1/(613 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10960 : Bounds (-61173793 / 125000000) (-489390343 / 1000000000) (Real.log (613 / 1000)) := by
  have h := reflection_log_10960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10961_neg : (15477 / 40000000) ≤ -Real.log (1000000 / 1000387) ∧
    -Real.log (1000000 / 1000387) ≤ (193463 / 500000000) := by
  have h := checkLog_sound (w := (387 / 2000387)) (n := 12)
    (lo := (15477 / 40000000)) (hi := (193463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000387 / 1000000) = 1/(1000000 / 1000387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10961 : Bounds (15477 / 40000000) (193463 / 500000000) (Real.log (1000387 / 1000000)) := by
  have h := reflection_log_10961_neg
  have he : Real.log (1000387 / 1000000) = -Real.log (1000000 / 1000387) := by
    rw [show ((1000387 / 1000000) : ℝ) = ((1000000 / 1000387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10962_neg : (193537 / 500000000) ≤ -Real.log (999613 / 1000000) ∧
    -Real.log (999613 / 1000000) ≤ (15483 / 40000000) := by
  have h := checkLog_sound (w := (387 / 1999613)) (n := 12)
    (lo := (193537 / 500000000)) (hi := (15483 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999613) = 1/(999613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10962 : Bounds (-15483 / 40000000) (-193537 / 500000000) (Real.log (999613 / 1000000)) := by
  have h := reflection_log_10962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10963_neg : (90426489 / 500000000) ≤ -Real.log (1000000 / 1198239) ∧
    -Real.log (1000000 / 1198239) ≤ (180852979 / 1000000000) := by
  have h := checkLog_sound (w := (198239 / 2198239)) (n := 12)
    (lo := (90426489 / 500000000)) (hi := (180852979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198239 / 1000000) = 1/(1000000 / 1198239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10963 : Bounds (90426489 / 500000000) (180852979 / 1000000000) (Real.log (1198239 / 1000000)) := by
  have h := reflection_log_10963_neg
  have he : Real.log (1198239 / 1000000) = -Real.log (1000000 / 1198239) := by
    rw [show ((1198239 / 1000000) : ℝ) = ((1000000 / 1198239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10964_neg : (2761809 / 12500000) ≤ -Real.log (801761 / 1000000) ∧
    -Real.log (801761 / 1000000) ≤ (220944721 / 1000000000) := by
  have h := checkLog_sound (w := (198239 / 1801761)) (n := 12)
    (lo := (2761809 / 12500000)) (hi := (220944721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801761) = 1/(801761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10964 : Bounds (-220944721 / 1000000000) (-2761809 / 12500000) (Real.log (801761 / 1000000)) := by
  have h := reflection_log_10964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10965_neg : (181620477 / 1000000000) ≤ -Real.log (1000000 / 1199159) ∧
    -Real.log (1000000 / 1199159) ≤ (90810239 / 500000000) := by
  have h := checkLog_sound (w := (199159 / 2199159)) (n := 12)
    (lo := (181620477 / 1000000000)) (hi := (90810239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199159 / 1000000) = 1/(1000000 / 1199159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10965 : Bounds (181620477 / 1000000000) (90810239 / 500000000) (Real.log (1199159 / 1000000)) := by
  have h := reflection_log_10965_neg
  have he : Real.log (1199159 / 1000000) = -Real.log (1000000 / 1199159) := by
    rw [show ((1199159 / 1000000) : ℝ) = ((1000000 / 1199159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10966_neg : (222092853 / 1000000000) ≤ -Real.log (800841 / 1000000) ∧
    -Real.log (800841 / 1000000) ≤ (111046427 / 500000000) := by
  have h := checkLog_sound (w := (199159 / 1800841)) (n := 12)
    (lo := (222092853 / 1000000000)) (hi := (111046427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800841) = 1/(800841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10966 : Bounds (-111046427 / 500000000) (-222092853 / 1000000000) (Real.log (800841 / 1000000)) := by
  have h := reflection_log_10966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10967_neg : (323779 / 8000000) ≤ -Real.log (960335692719 / 1000000000000) ∧
    -Real.log (960335692719 / 1000000000000) ≤ (5059047 / 125000000) := by
  have h := checkLog_sound (w := (39664307281 / 1960335692719)) (n := 12)
    (lo := (323779 / 8000000)) (hi := (5059047 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960335692719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960335692719) = 1/(960335692719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10967 : Bounds (-5059047 / 125000000) (-323779 / 8000000) (Real.log (960335692719 / 1000000000000)) := by
  have h := reflection_log_10967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10968_neg : (40091741 / 1000000000) ≤ -Real.log (960701298879 / 1000000000000) ∧
    -Real.log (960701298879 / 1000000000000) ≤ (20045871 / 500000000) := by
  have h := checkLog_sound (w := (39298701121 / 1960701298879)) (n := 12)
    (lo := (40091741 / 1000000000)) (hi := (20045871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960701298879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960701298879) = 1/(960701298879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10968 : Bounds (-20045871 / 500000000) (-40091741 / 1000000000) (Real.log (960701298879 / 1000000000000)) := by
  have h := reflection_log_10968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10969_neg : (401797699 / 1000000000) ≤ -Real.log (500000000000 / 747254481073) ∧
    -Real.log (500000000000 / 747254481073) ≤ (4017977 / 10000000) := by
  have h := checkLog_sound (w := (247254481073 / 1247254481073)) (n := 12)
    (lo := (401797699 / 1000000000)) (hi := (4017977 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747254481073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747254481073 / 500000000000) = 1/(500000000000 / 747254481073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10969 : Bounds (401797699 / 1000000000) (4017977 / 10000000) (Real.log (747254481073 / 500000000000)) := by
  have h := reflection_log_10969_neg
  have he : Real.log (747254481073 / 500000000000) = -Real.log (500000000000 / 747254481073) := by
    rw [show ((747254481073 / 500000000000) : ℝ) = ((500000000000 / 747254481073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10970_neg : (403713331 / 1000000000) ≤ -Real.log (250000000000 / 374343658729) ∧
    -Real.log (250000000000 / 374343658729) ≤ (100928333 / 250000000) := by
  have h := checkLog_sound (w := (124343658729 / 624343658729)) (n := 12)
    (lo := (403713331 / 1000000000)) (hi := (100928333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374343658729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374343658729 / 250000000000) = 1/(250000000000 / 374343658729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10970 : Bounds (403713331 / 1000000000) (100928333 / 250000000) (Real.log (374343658729 / 250000000000)) := by
  have h := reflection_log_10970_neg
  have he : Real.log (374343658729 / 250000000000) = -Real.log (250000000000 / 374343658729) := by
    rw [show ((374343658729 / 250000000000) : ℝ) = ((250000000000 / 374343658729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10971_neg : (814182251 / 1000000000) ≤ -Real.log (250000000000 / 564332247557) ∧
    -Real.log (250000000000 / 564332247557) ≤ (814182253 / 1000000000) := by
  have h := checkLog_sound (w := (64332247557 / 1064332247557)) (n := 12)
    (lo := (121035071 / 1000000000)) (hi := (1891173 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564332247557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(564332247557 / 500000000000) = 1/(250000000000 / 564332247557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10971 : Bounds (814182251 / 1000000000) (814182253 / 1000000000) (Real.log (564332247557 / 250000000000)) := by
  have h := reflection_log_10971_neg
  have he : Real.log (564332247557 / 250000000000) = -Real.log (250000000000 / 564332247557) := by
    rw [show ((564332247557 / 250000000000) : ℝ) = ((250000000000 / 564332247557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10972_neg : (816533483 / 1000000000) ≤ -Real.log (50000000000 / 113132137031) ∧
    -Real.log (50000000000 / 113132137031) ≤ (163306697 / 200000000) := by
  have h := checkLog_sound (w := (13132137031 / 213132137031)) (n := 12)
    (lo := (123386303 / 1000000000)) (hi := (1927911 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113132137031 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113132137031 / 100000000000) = 1/(50000000000 / 113132137031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10972 : Bounds (816533483 / 1000000000) (163306697 / 200000000) (Real.log (113132137031 / 50000000000)) := by
  have h := reflection_log_10972_neg
  have he : Real.log (113132137031 / 50000000000) = -Real.log (50000000000 / 113132137031) := by
    rw [show ((113132137031 / 50000000000) : ℝ) = ((50000000000 / 113132137031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10973_neg : (163931931 / 500000000) ≤ -Real.log (250 / 347) ∧
    -Real.log (250 / 347) ≤ (327863863 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 597)) (n := 12)
    (lo := (163931931 / 500000000)) (hi := (327863863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 250) = 1/(250 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10973 : Bounds (163931931 / 500000000) (327863863 / 1000000000) (Real.log (347 / 250)) := by
  have h := reflection_log_10973_neg
  have he : Real.log (347 / 250) = -Real.log (250 / 347) := by
    rw [show ((347 / 250) : ℝ) = ((250 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10974_neg : (122755749 / 250000000) ≤ -Real.log (153 / 250) ∧
    -Real.log (153 / 250) ≤ (491022997 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 403)) (n := 12)
    (lo := (122755749 / 250000000)) (hi := (491022997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 153) = 1/(153 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10974 : Bounds (-491022997 / 1000000000) (-122755749 / 250000000) (Real.log (153 / 250)) := by
  have h := reflection_log_10974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10975_neg : (96981 / 250000000) ≤ -Real.log (250000 / 250097) ∧
    -Real.log (250000 / 250097) ≤ (15517 / 40000000) := by
  have h := checkLog_sound (w := (97 / 500097)) (n := 12)
    (lo := (96981 / 250000000)) (hi := (15517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250097 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250097 / 250000) = 1/(250000 / 250097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10975 : Bounds (96981 / 250000000) (15517 / 40000000) (Real.log (250097 / 250000)) := by
  have h := reflection_log_10975_neg
  have he : Real.log (250097 / 250000) = -Real.log (250000 / 250097) := by
    rw [show ((250097 / 250000) : ℝ) = ((250000 / 250097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10976_neg : (15523 / 40000000) ≤ -Real.log (249903 / 250000) ∧
    -Real.log (249903 / 250000) ≤ (97019 / 250000000) := by
  have h := checkLog_sound (w := (97 / 499903)) (n := 12)
    (lo := (15523 / 40000000)) (hi := (97019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249903) = 1/(249903 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10976 : Bounds (-97019 / 250000000) (-15523 / 40000000) (Real.log (249903 / 250000)) := by
  have h := reflection_log_10976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10977_neg : (181306041 / 1000000000) ≤ -Real.log (500000 / 599391) ∧
    -Real.log (500000 / 599391) ≤ (90653021 / 500000000) := by
  have h := checkLog_sound (w := (99391 / 1099391)) (n := 12)
    (lo := (181306041 / 1000000000)) (hi := (90653021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599391 / 500000) = 1/(500000 / 599391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10977 : Bounds (181306041 / 1000000000) (90653021 / 500000000) (Real.log (599391 / 500000)) := by
  have h := reflection_log_10977_neg
  have he : Real.log (599391 / 500000) = -Real.log (500000 / 599391) := by
    rw [show ((599391 / 500000) : ℝ) = ((500000 / 599391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10978_neg : (221622209 / 1000000000) ≤ -Real.log (400609 / 500000) ∧
    -Real.log (400609 / 500000) ≤ (22162221 / 100000000) := by
  have h := checkLog_sound (w := (99391 / 900609)) (n := 12)
    (lo := (221622209 / 1000000000)) (hi := (22162221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400609) = 1/(400609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10978 : Bounds (-22162221 / 100000000) (-221622209 / 1000000000) (Real.log (400609 / 500000)) := by
  have h := reflection_log_10978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10979_neg : (91037013 / 500000000) ≤ -Real.log (1000000 / 1199703) ∧
    -Real.log (1000000 / 1199703) ≤ (182074027 / 1000000000) := by
  have h := checkLog_sound (w := (199703 / 2199703)) (n := 12)
    (lo := (91037013 / 500000000)) (hi := (182074027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199703 / 1000000) = 1/(1000000 / 1199703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10979 : Bounds (91037013 / 500000000) (182074027 / 1000000000) (Real.log (1199703 / 1000000)) := by
  have h := reflection_log_10979_neg
  have he : Real.log (1199703 / 1000000) = -Real.log (1000000 / 1199703) := by
    rw [show ((1199703 / 1000000) : ℝ) = ((1000000 / 1199703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10980_neg : (22277237 / 100000000) ≤ -Real.log (800297 / 1000000) ∧
    -Real.log (800297 / 1000000) ≤ (222772371 / 1000000000) := by
  have h := checkLog_sound (w := (199703 / 1800297)) (n := 12)
    (lo := (22277237 / 100000000)) (hi := (222772371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800297) = 1/(800297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10980 : Bounds (-222772371 / 1000000000) (-22277237 / 100000000) (Real.log (800297 / 1000000)) := by
  have h := reflection_log_10980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10981_neg : (5087293 / 125000000) ≤ -Real.log (960118711791 / 1000000000000) ∧
    -Real.log (960118711791 / 1000000000000) ≤ (8139669 / 200000000) := by
  have h := checkLog_sound (w := (39881288209 / 1960118711791)) (n := 12)
    (lo := (5087293 / 125000000)) (hi := (8139669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960118711791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960118711791) = 1/(960118711791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10981 : Bounds (-8139669 / 200000000) (-5087293 / 125000000) (Real.log (960118711791 / 1000000000000)) := by
  have h := reflection_log_10981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10982_neg : (40316167 / 1000000000) ≤ -Real.log (240121429119 / 250000000000) ∧
    -Real.log (240121429119 / 250000000000) ≤ (5039521 / 125000000) := by
  have h := checkLog_sound (w := (9878570881 / 490121429119)) (n := 12)
    (lo := (40316167 / 1000000000)) (hi := (5039521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240121429119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240121429119) = 1/(240121429119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10982 : Bounds (-5039521 / 125000000) (-40316167 / 1000000000) (Real.log (240121429119 / 250000000000)) := by
  have h := reflection_log_10982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10983_neg : (1611713 / 4000000) ≤ -Real.log (500000000000 / 748099768103) ∧
    -Real.log (500000000000 / 748099768103) ≤ (402928251 / 1000000000) := by
  have h := checkLog_sound (w := (248099768103 / 1248099768103)) (n := 12)
    (lo := (1611713 / 4000000)) (hi := (402928251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748099768103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748099768103 / 500000000000) = 1/(500000000000 / 748099768103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10983 : Bounds (1611713 / 4000000) (402928251 / 1000000000) (Real.log (748099768103 / 500000000000)) := by
  have h := reflection_log_10983_neg
  have he : Real.log (748099768103 / 500000000000) = -Real.log (500000000000 / 748099768103) := by
    rw [show ((748099768103 / 500000000000) : ℝ) = ((500000000000 / 748099768103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10984_neg : (101211599 / 250000000) ≤ -Real.log (12500000000 / 18738402743) ∧
    -Real.log (12500000000 / 18738402743) ≤ (404846397 / 1000000000) := by
  have h := checkLog_sound (w := (6238402743 / 31238402743)) (n := 12)
    (lo := (101211599 / 250000000)) (hi := (404846397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18738402743 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18738402743 / 12500000000) = 1/(12500000000 / 18738402743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10984 : Bounds (101211599 / 250000000) (404846397 / 1000000000) (Real.log (18738402743 / 12500000000)) := by
  have h := reflection_log_10984_neg
  have he : Real.log (18738402743 / 12500000000) = -Real.log (12500000000 / 18738402743) := by
    rw [show ((18738402743 / 12500000000) : ℝ) = ((12500000000 / 18738402743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10985_neg : (816533483 / 1000000000) ≤ -Real.log (500000000000 / 1131321370309) ∧
    -Real.log (500000000000 / 1131321370309) ≤ (163306697 / 200000000) := by
  have h := checkLog_sound (w := (131321370309 / 2131321370309)) (n := 12)
    (lo := (123386303 / 1000000000)) (hi := (1927911 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131321370309 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1131321370309 / 1000000000000) = 1/(500000000000 / 1131321370309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10985 : Bounds (816533483 / 1000000000) (163306697 / 200000000) (Real.log (1131321370309 / 500000000000)) := by
  have h := reflection_log_10985_neg
  have he : Real.log (1131321370309 / 500000000000) = -Real.log (500000000000 / 1131321370309) := by
    rw [show ((1131321370309 / 500000000000) : ℝ) = ((500000000000 / 1131321370309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10986_neg : (818886857 / 1000000000) ≤ -Real.log (100000000000 / 226797385621) ∧
    -Real.log (100000000000 / 226797385621) ≤ (818886859 / 1000000000) := by
  have h := checkLog_sound (w := (26797385621 / 426797385621)) (n := 12)
    (lo := (125739677 / 1000000000)) (hi := (62869839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226797385621 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226797385621 / 200000000000) = 1/(100000000000 / 226797385621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10986 : Bounds (818886857 / 1000000000) (818886859 / 1000000000) (Real.log (226797385621 / 100000000000)) := by
  have h := reflection_log_10986_neg
  have he : Real.log (226797385621 / 100000000000) = -Real.log (100000000000 / 226797385621) := by
    rw [show ((226797385621 / 100000000000) : ℝ) = ((100000000000 / 226797385621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10987_neg : (328584063 / 1000000000) ≤ -Real.log (1000 / 1389) ∧
    -Real.log (1000 / 1389) ≤ (2567063 / 7812500) := by
  have h := checkLog_sound (w := (389 / 2389)) (n := 12)
    (lo := (328584063 / 1000000000)) (hi := (2567063 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389 / 1000) = 1/(1000 / 1389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10987 : Bounds (328584063 / 1000000000) (2567063 / 7812500) (Real.log (1389 / 1000)) := by
  have h := reflection_log_10987_neg
  have he : Real.log (1389 / 1000) = -Real.log (1000 / 1389) := by
    rw [show ((1389 / 1000) : ℝ) = ((1000 / 1389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10988_neg : (492658319 / 1000000000) ≤ -Real.log (611 / 1000) ∧
    -Real.log (611 / 1000) ≤ (6158229 / 12500000) := by
  have h := checkLog_sound (w := (389 / 1611)) (n := 12)
    (lo := (492658319 / 1000000000)) (hi := (6158229 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 611) = 1/(611 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10988 : Bounds (-6158229 / 12500000) (-492658319 / 1000000000) (Real.log (611 / 1000)) := by
  have h := reflection_log_10988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10989_neg : (97231 / 250000000) ≤ -Real.log (1000000 / 1000389) ∧
    -Real.log (1000000 / 1000389) ≤ (15557 / 40000000) := by
  have h := checkLog_sound (w := (389 / 2000389)) (n := 12)
    (lo := (97231 / 250000000)) (hi := (15557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000389 / 1000000) = 1/(1000000 / 1000389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10989 : Bounds (97231 / 250000000) (15557 / 40000000) (Real.log (1000389 / 1000000)) := by
  have h := reflection_log_10989_neg
  have he : Real.log (1000389 / 1000000) = -Real.log (1000000 / 1000389) := by
    rw [show ((1000389 / 1000000) : ℝ) = ((1000000 / 1000389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10990_neg : (15563 / 40000000) ≤ -Real.log (999611 / 1000000) ∧
    -Real.log (999611 / 1000000) ≤ (97269 / 250000000) := by
  have h := checkLog_sound (w := (389 / 1999611)) (n := 12)
    (lo := (15563 / 40000000)) (hi := (97269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999611) = 1/(999611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10990 : Bounds (-97269 / 250000000) (-15563 / 40000000) (Real.log (999611 / 1000000)) := by
  have h := reflection_log_10990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10991_neg : (45439933 / 250000000) ≤ -Real.log (500000 / 599663) ∧
    -Real.log (500000 / 599663) ≤ (181759733 / 1000000000) := by
  have h := checkLog_sound (w := (99663 / 1099663)) (n := 12)
    (lo := (45439933 / 250000000)) (hi := (181759733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599663 / 500000) = 1/(500000 / 599663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10991 : Bounds (45439933 / 250000000) (181759733 / 1000000000) (Real.log (599663 / 500000)) := by
  have h := reflection_log_10991_neg
  have he : Real.log (599663 / 500000) = -Real.log (500000 / 599663) := by
    rw [show ((599663 / 500000) : ℝ) = ((500000 / 599663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10992_neg : (111150703 / 500000000) ≤ -Real.log (400337 / 500000) ∧
    -Real.log (400337 / 500000) ≤ (222301407 / 1000000000) := by
  have h := checkLog_sound (w := (99663 / 900337)) (n := 12)
    (lo := (111150703 / 500000000)) (hi := (222301407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 400337) = 1/(400337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10992 : Bounds (-222301407 / 1000000000) (-111150703 / 500000000) (Real.log (400337 / 500000)) := by
  have h := reflection_log_10992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10993_neg : (91264101 / 500000000) ≤ -Real.log (125000 / 150031) ∧
    -Real.log (125000 / 150031) ≤ (182528203 / 1000000000) := by
  have h := checkLog_sound (w := (25031 / 275031)) (n := 12)
    (lo := (91264101 / 500000000)) (hi := (182528203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150031 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150031 / 125000) = 1/(125000 / 150031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10993 : Bounds (91264101 / 500000000) (182528203 / 1000000000) (Real.log (150031 / 125000)) := by
  have h := reflection_log_10993_neg
  have he : Real.log (150031 / 125000) = -Real.log (125000 / 150031) := by
    rw [show ((150031 / 125000) : ℝ) = ((125000 / 150031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10994_neg : (223453599 / 1000000000) ≤ -Real.log (99969 / 125000) ∧
    -Real.log (99969 / 125000) ≤ (279317 / 1250000) := by
  have h := checkLog_sound (w := (25031 / 224969)) (n := 12)
    (lo := (223453599 / 1000000000)) (hi := (279317 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99969) = 1/(99969 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10994 : Bounds (-279317 / 1250000) (-223453599 / 1000000000) (Real.log (99969 / 125000)) := by
  have h := reflection_log_10994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10995_neg : (40925397 / 1000000000) ≤ -Real.log (14998449039 / 15625000000) ∧
    -Real.log (14998449039 / 15625000000) ≤ (20462699 / 500000000) := by
  have h := checkLog_sound (w := (626550961 / 30623449039)) (n := 12)
    (lo := (40925397 / 1000000000)) (hi := (20462699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14998449039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14998449039) = 1/(14998449039 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10995 : Bounds (-20462699 / 500000000) (-40925397 / 1000000000) (Real.log (14998449039 / 15625000000)) := by
  have h := reflection_log_10995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10996_neg : (40541673 / 1000000000) ≤ -Real.log (240067286431 / 250000000000) ∧
    -Real.log (240067286431 / 250000000000) ≤ (20270837 / 500000000) := by
  have h := checkLog_sound (w := (9932713569 / 490067286431)) (n := 12)
    (lo := (40541673 / 1000000000)) (hi := (20270837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240067286431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240067286431) = 1/(240067286431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10996 : Bounds (-20270837 / 500000000) (-40541673 / 1000000000) (Real.log (240067286431 / 250000000000)) := by
  have h := reflection_log_10996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10997_neg : (202030569 / 500000000) ≤ -Real.log (50000000000 / 74894776151) ∧
    -Real.log (50000000000 / 74894776151) ≤ (404061139 / 1000000000) := by
  have h := checkLog_sound (w := (24894776151 / 124894776151)) (n := 12)
    (lo := (202030569 / 500000000)) (hi := (404061139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74894776151 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74894776151 / 50000000000) = 1/(50000000000 / 74894776151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10997 : Bounds (202030569 / 500000000) (404061139 / 1000000000) (Real.log (74894776151 / 50000000000)) := by
  have h := reflection_log_10997_neg
  have he : Real.log (74894776151 / 50000000000) = -Real.log (50000000000 / 74894776151) := by
    rw [show ((74894776151 / 50000000000) : ℝ) = ((50000000000 / 74894776151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10998_neg : (405981801 / 1000000000) ≤ -Real.log (500000000000 / 750387620163) ∧
    -Real.log (500000000000 / 750387620163) ≤ (202990901 / 500000000) := by
  have h := checkLog_sound (w := (250387620163 / 1250387620163)) (n := 12)
    (lo := (405981801 / 1000000000)) (hi := (202990901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750387620163 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750387620163 / 500000000000) = 1/(500000000000 / 750387620163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10998 : Bounds (405981801 / 1000000000) (202990901 / 500000000) (Real.log (750387620163 / 500000000000)) := by
  have h := reflection_log_10998_neg
  have he : Real.log (750387620163 / 500000000000) = -Real.log (500000000000 / 750387620163) := by
    rw [show ((750387620163 / 500000000000) : ℝ) = ((500000000000 / 750387620163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10999_neg : (818886857 / 1000000000) ≤ -Real.log (62500000000 / 141748366013) ∧
    -Real.log (62500000000 / 141748366013) ≤ (818886859 / 1000000000) := by
  have h := checkLog_sound (w := (16748366013 / 266748366013)) (n := 12)
    (lo := (125739677 / 1000000000)) (hi := (62869839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141748366013 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(141748366013 / 125000000000) = 1/(62500000000 / 141748366013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10999 : Bounds (818886857 / 1000000000) (818886859 / 1000000000) (Real.log (141748366013 / 62500000000)) := by
  have h := reflection_log_10999_neg
  have he : Real.log (141748366013 / 62500000000) = -Real.log (62500000000 / 141748366013) := by
    rw [show ((141748366013 / 62500000000) : ℝ) = ((62500000000 / 141748366013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11000_neg : (821242383 / 1000000000) ≤ -Real.log (50000000000 / 113666121113) ∧
    -Real.log (50000000000 / 113666121113) ≤ (164248477 / 200000000) := by
  have h := checkLog_sound (w := (13666121113 / 213666121113)) (n := 12)
    (lo := (128095203 / 1000000000)) (hi := (32023801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113666121113 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113666121113 / 100000000000) = 1/(50000000000 / 113666121113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11000 : Bounds (821242383 / 1000000000) (164248477 / 200000000) (Real.log (113666121113 / 50000000000)) := by
  have h := reflection_log_11000_neg
  have he : Real.log (113666121113 / 50000000000) = -Real.log (50000000000 / 113666121113) := by
    rw [show ((113666121113 / 50000000000) : ℝ) = ((50000000000 / 113666121113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11001_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11001 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_11001_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11002_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11002 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_11002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11003_neg : (389923 / 1000000000) ≤ -Real.log (100000 / 100039) ∧
    -Real.log (100000 / 100039) ≤ (97481 / 250000000) := by
  have h := checkLog_sound (w := (39 / 200039)) (n := 12)
    (lo := (389923 / 1000000000)) (hi := (97481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100039 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100039 / 100000) = 1/(100000 / 100039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11003 : Bounds (389923 / 1000000000) (97481 / 250000000) (Real.log (100039 / 100000)) := by
  have h := reflection_log_11003_neg
  have he : Real.log (100039 / 100000) = -Real.log (100000 / 100039) := by
    rw [show ((100039 / 100000) : ℝ) = ((100000 / 100039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11004_neg : (97519 / 250000000) ≤ -Real.log (99961 / 100000) ∧
    -Real.log (99961 / 100000) ≤ (390077 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 199961)) (n := 12)
    (lo := (97519 / 250000000)) (hi := (390077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99961) = 1/(99961 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11004 : Bounds (-390077 / 1000000000) (-97519 / 250000000) (Real.log (99961 / 100000)) := by
  have h := reflection_log_11004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11005_neg : (182213217 / 1000000000) ≤ -Real.log (100000 / 119987) ∧
    -Real.log (100000 / 119987) ≤ (91106609 / 500000000) := by
  have h := checkLog_sound (w := (19987 / 219987)) (n := 12)
    (lo := (182213217 / 1000000000)) (hi := (91106609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119987 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119987 / 100000) = 1/(100000 / 119987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11005 : Bounds (182213217 / 1000000000) (91106609 / 500000000) (Real.log (119987 / 100000)) := by
  have h := reflection_log_11005_neg
  have he : Real.log (119987 / 100000) = -Real.log (100000 / 119987) := by
    rw [show ((119987 / 100000) : ℝ) = ((100000 / 119987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11006_neg : (27872633 / 125000000) ≤ -Real.log (80013 / 100000) ∧
    -Real.log (80013 / 100000) ≤ (44596213 / 200000000) := by
  have h := checkLog_sound (w := (19987 / 180013)) (n := 12)
    (lo := (27872633 / 125000000)) (hi := (44596213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80013) = 1/(80013 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11006 : Bounds (-44596213 / 200000000) (-27872633 / 125000000) (Real.log (80013 / 100000)) := by
  have h := reflection_log_11006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11007_neg : (182982171 / 1000000000) ≤ -Real.log (1000000 / 1200793) ∧
    -Real.log (1000000 / 1200793) ≤ (45745543 / 250000000) := by
  have h := checkLog_sound (w := (200793 / 2200793)) (n := 12)
    (lo := (182982171 / 1000000000)) (hi := (45745543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1200793 / 1000000) = 1/(1000000 / 1200793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11007 : Bounds (182982171 / 1000000000) (45745543 / 250000000) (Real.log (1200793 / 1000000)) := by
  have h := reflection_log_11007_neg
  have he : Real.log (1200793 / 1000000) = -Real.log (1000000 / 1200793) := by
    rw [show ((1200793 / 1000000) : ℝ) = ((1000000 / 1200793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
