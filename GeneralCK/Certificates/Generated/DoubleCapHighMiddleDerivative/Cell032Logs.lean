import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell032
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

theorem reflection_log_1_neg : (238493879 / 1000000000) ≤ -Real.log (5120 / 6499) ∧
    -Real.log (5120 / 6499) ≤ (5962347 / 25000000) := by
  have h := checkLog_sound (w := (1379 / 11619)) (n := 12)
    (lo := (238493879 / 1000000000)) (hi := (5962347 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6499 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6499 / 5120) = 1/(5120 / 6499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (238493879 / 1000000000) (5962347 / 25000000) (Real.log (6499 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6499 / 5120) = -Real.log (5120 / 6499) := by
    rw [show ((6499 / 5120) : ℝ) = ((5120 / 6499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (313801483 / 1000000000) ≤ -Real.log (3741 / 5120) ∧
    -Real.log (3741 / 5120) ≤ (78450371 / 250000000) := by
  have h := checkLog_sound (w := (1379 / 8861)) (n := 12)
    (lo := (313801483 / 1000000000)) (hi := (78450371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3741) = 1/(3741 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78450371 / 250000000) (-313801483 / 1000000000) (Real.log (3741 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (238032163 / 1000000000) ≤ -Real.log (160 / 203) ∧
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


theorem reflection_log_3 : Bounds (238032163 / 1000000000) (59508041 / 250000000) (Real.log (203 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (203 / 160) = -Real.log (160 / 203) := by
    rw [show ((203 / 160) : ℝ) = ((160 / 203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7824997 / 25000000) ≤ -Real.log (117 / 160) ∧
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


theorem reflection_log_4 : Bounds (-312999881 / 1000000000) (-7824997 / 25000000) (Real.log (117 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (174477539 / 1000000000) ≤ -Real.log (31250 / 37207) ∧
    -Real.log (31250 / 37207) ≤ (8723877 / 50000000) := by
  have h := checkLog_sound (w := (5957 / 68457)) (n := 12)
    (lo := (174477539 / 1000000000)) (hi := (8723877 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37207 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37207 / 31250) = 1/(31250 / 37207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (174477539 / 1000000000) (8723877 / 50000000) (Real.log (37207 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37207 / 31250) = -Real.log (31250 / 37207) := by
    rw [show ((37207 / 31250) : ℝ) = ((31250 / 37207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (105745849 / 500000000) ≤ -Real.log (25293 / 31250) ∧
    -Real.log (25293 / 31250) ≤ (211491699 / 1000000000) := by
  have h := checkLog_sound (w := (5957 / 56543)) (n := 12)
    (lo := (105745849 / 500000000)) (hi := (211491699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25293) = 1/(25293 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211491699 / 1000000000) (-105745849 / 500000000) (Real.log (25293 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (174829393 / 1000000000) ≤ -Real.log (1000000 / 1191043) ∧
    -Real.log (1000000 / 1191043) ≤ (87414697 / 500000000) := by
  have h := checkLog_sound (w := (191043 / 2191043)) (n := 12)
    (lo := (174829393 / 1000000000)) (hi := (87414697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191043 / 1000000) = 1/(1000000 / 1191043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (174829393 / 1000000000) (87414697 / 500000000) (Real.log (1191043 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1191043 / 1000000) = -Real.log (1000000 / 1191043) := by
    rw [show ((1191043 / 1000000) : ℝ) = ((1000000 / 1191043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (42401903 / 200000000) ≤ -Real.log (808957 / 1000000) ∧
    -Real.log (808957 / 1000000) ≤ (53002379 / 250000000) := by
  have h := checkLog_sound (w := (191043 / 1808957)) (n := 12)
    (lo := (42401903 / 200000000)) (hi := (53002379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808957) = 1/(808957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53002379 / 250000000) (-42401903 / 200000000) (Real.log (808957 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (25531359 / 200000000) ≤ -Real.log (1000000 / 1136163) ∧
    -Real.log (1000000 / 1136163) ≤ (31914199 / 250000000) := by
  have h := checkLog_sound (w := (136163 / 2136163)) (n := 12)
    (lo := (25531359 / 200000000)) (hi := (31914199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136163 / 1000000) = 1/(1000000 / 1136163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (25531359 / 200000000) (31914199 / 250000000) (Real.log (1136163 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1136163 / 1000000) = -Real.log (1000000 / 1136163) := by
    rw [show ((1136163 / 1000000) : ℝ) = ((1000000 / 1136163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (29274237 / 200000000) ≤ -Real.log (863837 / 1000000) ∧
    -Real.log (863837 / 1000000) ≤ (73185593 / 500000000) := by
  have h := checkLog_sound (w := (136163 / 1863837)) (n := 12)
    (lo := (29274237 / 200000000)) (hi := (73185593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863837) = 1/(863837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-73185593 / 500000000) (-29274237 / 200000000) (Real.log (863837 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127926087 / 1000000000) ≤ -Real.log (1000000 / 1136469) ∧
    -Real.log (1000000 / 1136469) ≤ (15990761 / 125000000) := by
  have h := checkLog_sound (w := (136469 / 2136469)) (n := 12)
    (lo := (127926087 / 1000000000)) (hi := (15990761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136469 / 1000000) = 1/(1000000 / 1136469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127926087 / 1000000000) (15990761 / 125000000) (Real.log (1136469 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1136469 / 1000000) = -Real.log (1000000 / 1136469) := by
    rw [show ((1136469 / 1000000) : ℝ) = ((1000000 / 1136469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (146725481 / 1000000000) ≤ -Real.log (863531 / 1000000) ∧
    -Real.log (863531 / 1000000) ≤ (73362741 / 500000000) := by
  have h := checkLog_sound (w := (136469 / 1863531)) (n := 12)
    (lo := (146725481 / 1000000000)) (hi := (73362741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863531) = 1/(863531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73362741 / 500000000) (-146725481 / 1000000000) (Real.log (863531 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (137758011 / 250000000) ≤ -Real.log (500000000000 / 867521367521) ∧
    -Real.log (500000000000 / 867521367521) ≤ (110206409 / 200000000) := by
  have h := checkLog_sound (w := (367521367521 / 1367521367521)) (n := 12)
    (lo := (137758011 / 250000000)) (hi := (110206409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867521367521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867521367521 / 500000000000) = 1/(500000000000 / 867521367521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (137758011 / 250000000) (110206409 / 200000000) (Real.log (867521367521 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (867521367521 / 500000000000) = -Real.log (500000000000 / 867521367521) := by
    rw [show ((867521367521 / 500000000000) : ℝ) = ((500000000000 / 867521367521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (552295363 / 1000000000) ≤ -Real.log (250000000000 / 434309008287) ∧
    -Real.log (250000000000 / 434309008287) ≤ (138073841 / 250000000) := by
  have h := checkLog_sound (w := (184309008287 / 684309008287)) (n := 12)
    (lo := (552295363 / 1000000000)) (hi := (138073841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434309008287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434309008287 / 250000000000) = 1/(250000000000 / 434309008287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (552295363 / 1000000000) (138073841 / 250000000) (Real.log (434309008287 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (434309008287 / 250000000000) = -Real.log (250000000000 / 434309008287) := by
    rw [show ((434309008287 / 250000000000) : ℝ) = ((250000000000 / 434309008287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (192984619 / 500000000) ≤ -Real.log (50000000000 / 73551970901) ∧
    -Real.log (50000000000 / 73551970901) ≤ (385969239 / 1000000000) := by
  have h := checkLog_sound (w := (23551970901 / 123551970901)) (n := 12)
    (lo := (192984619 / 500000000)) (hi := (385969239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73551970901 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73551970901 / 50000000000) = 1/(50000000000 / 73551970901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192984619 / 500000000) (385969239 / 1000000000) (Real.log (73551970901 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (73551970901 / 50000000000) = -Real.log (50000000000 / 73551970901) := by
    rw [show ((73551970901 / 50000000000) : ℝ) = ((50000000000 / 73551970901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (386838909 / 1000000000) ≤ -Real.log (500000000000 / 736159647547) ∧
    -Real.log (500000000000 / 736159647547) ≤ (38683891 / 100000000) := by
  have h := checkLog_sound (w := (236159647547 / 1236159647547)) (n := 12)
    (lo := (386838909 / 1000000000)) (hi := (38683891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736159647547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736159647547 / 500000000000) = 1/(500000000000 / 736159647547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (386838909 / 1000000000) (38683891 / 100000000) (Real.log (736159647547 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (736159647547 / 500000000000) = -Real.log (500000000000 / 736159647547) := by
    rw [show ((736159647547 / 500000000000) : ℝ) = ((500000000000 / 736159647547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (274027981 / 1000000000) ≤ -Real.log (500000000000 / 657625802089) ∧
    -Real.log (500000000000 / 657625802089) ≤ (137013991 / 500000000) := by
  have h := checkLog_sound (w := (157625802089 / 1157625802089)) (n := 12)
    (lo := (274027981 / 1000000000)) (hi := (137013991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657625802089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657625802089 / 500000000000) = 1/(500000000000 / 657625802089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (274027981 / 1000000000) (137013991 / 500000000) (Real.log (657625802089 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (657625802089 / 500000000000) = -Real.log (500000000000 / 657625802089) := by
    rw [show ((657625802089 / 500000000000) : ℝ) = ((500000000000 / 657625802089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17165723 / 62500000) ≤ -Real.log (500000000000 / 658036017237) ∧
    -Real.log (500000000000 / 658036017237) ≤ (274651569 / 1000000000) := by
  have h := checkLog_sound (w := (158036017237 / 1158036017237)) (n := 12)
    (lo := (17165723 / 62500000)) (hi := (274651569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658036017237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658036017237 / 500000000000) = 1/(500000000000 / 658036017237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17165723 / 62500000) (274651569 / 1000000000) (Real.log (658036017237 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (658036017237 / 500000000000) = -Real.log (500000000000 / 658036017237) := by
    rw [show ((658036017237 / 500000000000) : ℝ) = ((500000000000 / 658036017237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9399697 / 500000000) ≤ -Real.log (981376212039 / 1000000000000) ∧
    -Real.log (981376212039 / 1000000000000) ≤ (3759879 / 200000000) := by
  have h := checkLog_sound (w := (18623787961 / 1981376212039)) (n := 12)
    (lo := (9399697 / 500000000)) (hi := (3759879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981376212039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981376212039) = 1/(981376212039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3759879 / 200000000) (-9399697 / 500000000) (Real.log (981376212039 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18714389 / 1000000000) ≤ -Real.log (981459637431 / 1000000000000) ∧
    -Real.log (981459637431 / 1000000000000) ≤ (1871439 / 100000000) := by
  have h := checkLog_sound (w := (18540362569 / 1981459637431)) (n := 12)
    (lo := (18714389 / 1000000000)) (hi := (1871439 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981459637431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981459637431) = 1/(981459637431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1871439 / 100000000) (-18714389 / 1000000000) (Real.log (981459637431 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell032
