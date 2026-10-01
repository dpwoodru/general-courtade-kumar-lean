import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell031
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

theorem reflection_log_1_neg : (238032163 / 1000000000) ≤ -Real.log (160 / 203) ∧
    -Real.log (160 / 203) ≤ (59508041 / 250000000) := by
  have h := checkLog_sound (w := (43 / 363)) (n := 12)
    (lo := (238032163 / 1000000000)) (hi := (59508041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203 / 160) = 1/(160 / 203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (238032163 / 1000000000) (59508041 / 250000000) (Real.log (203 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (203 / 160) = -Real.log (160 / 203) := by
    rw [show ((203 / 160) : ℝ) = ((160 / 203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7824997 / 25000000) ≤ -Real.log (117 / 160) ∧
    -Real.log (117 / 160) ≤ (312999881 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 117) = 1/(117 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-312999881 / 1000000000) (-7824997 / 25000000) (Real.log (117 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (118785117 / 500000000) ≤ -Real.log (5120 / 6493) ∧
    -Real.log (5120 / 6493) ≤ (47514047 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 11613)) (n := 12)
    (lo := (118785117 / 500000000)) (hi := (47514047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6493 / 5120) = 1/(5120 / 6493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (118785117 / 500000000) (47514047 / 200000000) (Real.log (6493 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6493 / 5120) = -Real.log (5120 / 6493) := by
    rw [show ((6493 / 5120) : ℝ) = ((5120 / 6493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (312198919 / 1000000000) ≤ -Real.log (3747 / 5120) ∧
    -Real.log (3747 / 5120) ≤ (7804973 / 25000000) := by
  have h := checkLog_sound (w := (1373 / 8867)) (n := 12)
    (lo := (312198919 / 1000000000)) (hi := (7804973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3747) = 1/(3747 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7804973 / 25000000) (-312198919 / 1000000000) (Real.log (3747 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174126401 / 1000000000) ≤ -Real.log (500000 / 595103) ∧
    -Real.log (500000 / 595103) ≤ (87063201 / 500000000) := by
  have h := checkLog_sound (w := (95103 / 1095103)) (n := 12)
    (lo := (174126401 / 1000000000)) (hi := (87063201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595103 / 500000) = 1/(500000 / 595103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174126401 / 1000000000) (87063201 / 500000000) (Real.log (595103 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (595103 / 500000) = -Real.log (500000 / 595103) := by
    rw [show ((595103 / 500000) : ℝ) = ((500000 / 595103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (26371923 / 125000000) ≤ -Real.log (404897 / 500000) ∧
    -Real.log (404897 / 500000) ≤ (42195077 / 200000000) := by
  have h := checkLog_sound (w := (95103 / 904897)) (n := 12)
    (lo := (26371923 / 125000000)) (hi := (42195077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404897) = 1/(404897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-42195077 / 200000000) (-26371923 / 125000000) (Real.log (404897 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174478379 / 1000000000) ≤ -Real.log (320 / 381) ∧
    -Real.log (320 / 381) ≤ (8723919 / 50000000) := by
  have h := checkLog_sound (w := (61 / 701)) (n := 12)
    (lo := (174478379 / 1000000000)) (hi := (8723919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 320) = 1/(320 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174478379 / 1000000000) (8723919 / 50000000) (Real.log (381 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (381 / 320) = -Real.log (320 / 381) := by
    rw [show ((381 / 320) : ℝ) = ((320 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (105746467 / 500000000) ≤ -Real.log (259 / 320) ∧
    -Real.log (259 / 320) ≤ (42298587 / 200000000) := by
  have h := checkLog_sound (w := (61 / 579)) (n := 12)
    (lo := (105746467 / 500000000)) (hi := (42298587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 259) = 1/(259 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-42298587 / 200000000) (-105746467 / 500000000) (Real.log (259 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15923539 / 125000000) ≤ -Real.log (500000 / 567929) ∧
    -Real.log (500000 / 567929) ≤ (127388313 / 1000000000) := by
  have h := checkLog_sound (w := (67929 / 1067929)) (n := 12)
    (lo := (15923539 / 125000000)) (hi := (127388313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567929 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567929 / 500000) = 1/(500000 / 567929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15923539 / 125000000) (127388313 / 1000000000) (Real.log (567929 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (567929 / 500000) = -Real.log (500000 / 567929) := by
    rw [show ((567929 / 500000) : ℝ) = ((500000 / 567929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (146018171 / 1000000000) ≤ -Real.log (432071 / 500000) ∧
    -Real.log (432071 / 500000) ≤ (36504543 / 250000000) := by
  have h := checkLog_sound (w := (67929 / 932071)) (n := 12)
    (lo := (146018171 / 1000000000)) (hi := (36504543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432071) = 1/(432071 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36504543 / 250000000) (-146018171 / 1000000000) (Real.log (432071 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31914419 / 250000000) ≤ -Real.log (250000 / 284041) ∧
    -Real.log (250000 / 284041) ≤ (127657677 / 1000000000) := by
  have h := checkLog_sound (w := (34041 / 534041)) (n := 12)
    (lo := (31914419 / 250000000)) (hi := (127657677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284041 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284041 / 250000) = 1/(250000 / 284041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31914419 / 250000000) (127657677 / 1000000000) (Real.log (284041 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284041 / 250000) = -Real.log (250000 / 284041) := by
    rw [show ((284041 / 250000) : ℝ) = ((250000 / 284041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146372343 / 1000000000) ≤ -Real.log (215959 / 250000) ∧
    -Real.log (215959 / 250000) ≤ (18296543 / 125000000) := by
  have h := checkLog_sound (w := (34041 / 465959)) (n := 12)
    (lo := (146372343 / 1000000000)) (hi := (18296543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215959) = 1/(215959 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-18296543 / 125000000) (-146372343 / 1000000000) (Real.log (215959 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (549769153 / 1000000000) ≤ -Real.log (31250000000 / 54151654657) ∧
    -Real.log (31250000000 / 54151654657) ≤ (274884577 / 500000000) := by
  have h := checkLog_sound (w := (22901654657 / 85401654657)) (n := 12)
    (lo := (549769153 / 1000000000)) (hi := (274884577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54151654657 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54151654657 / 31250000000) = 1/(31250000000 / 54151654657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (549769153 / 1000000000) (274884577 / 500000000) (Real.log (54151654657 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (54151654657 / 31250000000) = -Real.log (31250000000 / 54151654657) := by
    rw [show ((54151654657 / 31250000000) : ℝ) = ((31250000000 / 54151654657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137758011 / 250000000) ≤ -Real.log (250000000000 / 433760683761) ∧
    -Real.log (250000000000 / 433760683761) ≤ (110206409 / 200000000) := by
  have h := checkLog_sound (w := (183760683761 / 683760683761)) (n := 12)
    (lo := (137758011 / 250000000)) (hi := (110206409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433760683761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433760683761 / 250000000000) = 1/(250000000000 / 433760683761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (137758011 / 250000000) (110206409 / 200000000) (Real.log (433760683761 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (433760683761 / 250000000000) = -Real.log (250000000000 / 433760683761) := by
    rw [show ((433760683761 / 250000000000) : ℝ) = ((250000000000 / 433760683761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (192550893 / 500000000) ≤ -Real.log (500000000000 / 734881957633) ∧
    -Real.log (500000000000 / 734881957633) ≤ (385101787 / 1000000000) := by
  have h := checkLog_sound (w := (234881957633 / 1234881957633)) (n := 12)
    (lo := (192550893 / 500000000)) (hi := (385101787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734881957633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734881957633 / 500000000000) = 1/(500000000000 / 734881957633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192550893 / 500000000) (385101787 / 1000000000) (Real.log (734881957633 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (734881957633 / 500000000000) = -Real.log (500000000000 / 734881957633) := by
    rw [show ((734881957633 / 500000000000) : ℝ) = ((500000000000 / 734881957633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385971313 / 1000000000) ≤ -Real.log (250000000000 / 367760617761) ∧
    -Real.log (250000000000 / 367760617761) ≤ (192985657 / 500000000) := by
  have h := checkLog_sound (w := (117760617761 / 617760617761)) (n := 12)
    (lo := (385971313 / 1000000000)) (hi := (192985657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367760617761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367760617761 / 250000000000) = 1/(250000000000 / 367760617761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (385971313 / 1000000000) (192985657 / 500000000) (Real.log (367760617761 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (367760617761 / 250000000000) = -Real.log (250000000000 / 367760617761) := by
    rw [show ((367760617761 / 250000000000) : ℝ) = ((250000000000 / 367760617761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68351621 / 250000000) ≤ -Real.log (250000000000 / 328608608307) ∧
    -Real.log (250000000000 / 328608608307) ≤ (54681297 / 200000000) := by
  have h := checkLog_sound (w := (78608608307 / 578608608307)) (n := 12)
    (lo := (68351621 / 250000000)) (hi := (54681297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328608608307 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328608608307 / 250000000000) = 1/(250000000000 / 328608608307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68351621 / 250000000) (54681297 / 200000000) (Real.log (328608608307 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (328608608307 / 250000000000) = -Real.log (250000000000 / 328608608307) := by
    rw [show ((328608608307 / 250000000000) : ℝ) = ((250000000000 / 328608608307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (274030019 / 1000000000) ≤ -Real.log (50000000000 / 65762714219) ∧
    -Real.log (50000000000 / 65762714219) ≤ (13701501 / 50000000) := by
  have h := checkLog_sound (w := (15762714219 / 115762714219)) (n := 12)
    (lo := (274030019 / 1000000000)) (hi := (13701501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65762714219 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65762714219 / 50000000000) = 1/(50000000000 / 65762714219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (274030019 / 1000000000) (13701501 / 50000000) (Real.log (65762714219 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65762714219 / 50000000000) = -Real.log (50000000000 / 65762714219) := by
    rw [show ((65762714219 / 50000000000) : ℝ) = ((50000000000 / 65762714219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9357333 / 500000000) ≤ -Real.log (61341210319 / 62500000000) ∧
    -Real.log (61341210319 / 62500000000) ≤ (18714667 / 1000000000) := by
  have h := checkLog_sound (w := (1158789681 / 123841210319)) (n := 12)
    (lo := (9357333 / 500000000)) (hi := (18714667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61341210319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61341210319) = 1/(61341210319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18714667 / 1000000000) (-9357333 / 500000000) (Real.log (61341210319 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18629859 / 1000000000) ≤ -Real.log (245385650959 / 250000000000) ∧
    -Real.log (245385650959 / 250000000000) ≤ (931493 / 50000000) := by
  have h := checkLog_sound (w := (4614349041 / 495385650959)) (n := 12)
    (lo := (18629859 / 1000000000)) (hi := (931493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245385650959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245385650959) = 1/(245385650959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-931493 / 50000000) (-18629859 / 1000000000) (Real.log (245385650959 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell031
