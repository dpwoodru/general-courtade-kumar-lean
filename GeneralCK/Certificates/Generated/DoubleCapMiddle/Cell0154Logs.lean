import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0154
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

theorem reflection_log_1_neg : (71749561 / 250000000) ≤ -Real.log (2560 / 3411) ∧
    -Real.log (2560 / 3411) ≤ (57399649 / 200000000) := by
  have h := checkLog_sound (w := (851 / 5971)) (n := 12)
    (lo := (71749561 / 250000000)) (hi := (57399649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3411 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3411 / 2560) = 1/(2560 / 3411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (71749561 / 250000000) (57399649 / 200000000) (Real.log (3411 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3411 / 2560) = -Real.log (2560 / 3411) := by
    rw [show ((3411 / 2560) : ℝ) = ((2560 / 3411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (202049427 / 500000000) ≤ -Real.log (1709 / 2560) ∧
    -Real.log (1709 / 2560) ≤ (80819771 / 200000000) := by
  have h := checkLog_sound (w := (851 / 4269)) (n := 12)
    (lo := (202049427 / 500000000)) (hi := (80819771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1709) = 1/(1709 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80819771 / 200000000) (-202049427 / 500000000) (Real.log (1709 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5722367 / 20000000) ≤ -Real.log (160 / 213) ∧
    -Real.log (160 / 213) ≤ (286118351 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 373)) (n := 12)
    (lo := (5722367 / 20000000)) (hi := (286118351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 160) = 1/(160 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5722367 / 20000000) (286118351 / 1000000000) (Real.log (213 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (213 / 160) = -Real.log (160 / 213) := by
    rw [show ((213 / 160) : ℝ) = ((160 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20117249 / 50000000) ≤ -Real.log (107 / 160) ∧
    -Real.log (107 / 160) ≤ (402344981 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 267)) (n := 12)
    (lo := (20117249 / 50000000)) (hi := (402344981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 107) = 1/(107 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-402344981 / 1000000000) (-20117249 / 50000000) (Real.log (107 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (20389251 / 40000000) ≤ -Real.log (1280 / 2131) ∧
    -Real.log (1280 / 2131) ≤ (127432819 / 250000000) := by
  have h := checkLog_sound (w := (851 / 3411)) (n := 12)
    (lo := (20389251 / 40000000)) (hi := (127432819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2131 / 1280) = 1/(1280 / 2131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (20389251 / 40000000) (127432819 / 250000000) (Real.log (2131 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2131 / 1280) = -Real.log (1280 / 2131) := by
    rw [show ((2131 / 1280) : ℝ) = ((1280 / 2131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1093158437 / 1000000000) ≤ -Real.log (429 / 1280) ∧
    -Real.log (429 / 1280) ≤ (1093158439 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 429) = 1/(429 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1093158439 / 1000000000) (-1093158437 / 1000000000) (Real.log (429 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (508322493 / 1000000000) ≤ -Real.log (80 / 133) ∧
    -Real.log (80 / 133) ≤ (254161247 / 500000000) := by
  have h := checkLog_sound (w := (53 / 213)) (n := 12)
    (lo := (508322493 / 1000000000)) (hi := (254161247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 80) = 1/(80 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (508322493 / 1000000000) (254161247 / 500000000) (Real.log (133 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (133 / 80) = -Real.log (80 / 133) := by
    rw [show ((133 / 80) : ℝ) = ((80 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (135773721 / 125000000) ≤ -Real.log (27 / 80) ∧
    -Real.log (27 / 80) ≤ (108618977 / 100000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 27) = 1/(27 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-108618977 / 100000000) (-135773721 / 125000000) (Real.log (27 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (391438527 / 1000000000) ≤ -Real.log (1000000 / 1479107) ∧
    -Real.log (1000000 / 1479107) ≤ (6116227 / 15625000) := by
  have h := checkLog_sound (w := (479107 / 2479107)) (n := 12)
    (lo := (391438527 / 1000000000)) (hi := (6116227 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479107 / 1000000) = 1/(1000000 / 1479107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (391438527 / 1000000000) (6116227 / 15625000) (Real.log (1479107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1479107 / 1000000) = -Real.log (1000000 / 1479107) := by
    rw [show ((1479107 / 1000000) : ℝ) = ((1000000 / 1479107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81526329 / 125000000) ≤ -Real.log (520893 / 1000000) ∧
    -Real.log (520893 / 1000000) ≤ (652210633 / 1000000000) := by
  have h := checkLog_sound (w := (479107 / 1520893)) (n := 12)
    (lo := (81526329 / 125000000)) (hi := (652210633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 520893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 520893) = 1/(520893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-652210633 / 1000000000) (-81526329 / 125000000) (Real.log (520893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (392650011 / 1000000000) ≤ -Real.log (10000 / 14809) ∧
    -Real.log (10000 / 14809) ≤ (98162503 / 250000000) := by
  have h := checkLog_sound (w := (4809 / 24809)) (n := 12)
    (lo := (392650011 / 1000000000)) (hi := (98162503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14809 / 10000) = 1/(10000 / 14809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (392650011 / 1000000000) (98162503 / 250000000) (Real.log (14809 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14809 / 10000) = -Real.log (10000 / 14809) := by
    rw [show ((14809 / 10000) : ℝ) = ((10000 / 14809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40978671 / 62500000) ≤ -Real.log (5191 / 10000) ∧
    -Real.log (5191 / 10000) ≤ (655658737 / 1000000000) := by
  have h := checkLog_sound (w := (4809 / 15191)) (n := 12)
    (lo := (40978671 / 62500000)) (hi := (655658737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 5191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 5191) = 1/(5191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-655658737 / 1000000000) (-40978671 / 62500000) (Real.log (5191 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77182011 / 250000000) ≤ -Real.log (250000 / 340423) ∧
    -Real.log (250000 / 340423) ≤ (61745609 / 200000000) := by
  have h := checkLog_sound (w := (90423 / 590423)) (n := 12)
    (lo := (77182011 / 250000000)) (hi := (61745609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340423 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340423 / 250000) = 1/(250000 / 340423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77182011 / 250000000) (61745609 / 200000000) (Real.log (340423 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (340423 / 250000) = -Real.log (250000 / 340423) := by
    rw [show ((340423 / 250000) : ℝ) = ((250000 / 340423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (448934353 / 1000000000) ≤ -Real.log (159577 / 250000) ∧
    -Real.log (159577 / 250000) ≤ (224467177 / 500000000) := by
  have h := checkLog_sound (w := (90423 / 409577)) (n := 12)
    (lo := (448934353 / 1000000000)) (hi := (224467177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159577) = 1/(159577 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-224467177 / 500000000) (-448934353 / 1000000000) (Real.log (159577 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38731927 / 125000000) ≤ -Real.log (250000 / 340807) ∧
    -Real.log (250000 / 340807) ≤ (309855417 / 1000000000) := by
  have h := checkLog_sound (w := (90807 / 590807)) (n := 12)
    (lo := (38731927 / 125000000)) (hi := (309855417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340807 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340807 / 250000) = 1/(250000 / 340807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38731927 / 125000000) (309855417 / 1000000000) (Real.log (340807 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (340807 / 250000) = -Real.log (250000 / 340807) := by
    rw [show ((340807 / 250000) : ℝ) = ((250000 / 340807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (90268723 / 200000000) ≤ -Real.log (159193 / 250000) ∧
    -Real.log (159193 / 250000) ≤ (1763061 / 3906250) := by
  have h := checkLog_sound (w := (90807 / 409193)) (n := 12)
    (lo := (90268723 / 200000000)) (hi := (1763061 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159193) = 1/(159193 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1763061 / 3906250) (-90268723 / 200000000) (Real.log (159193 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1043649159 / 1000000000) ≤ -Real.log (100000000000 / 283956013999) ∧
    -Real.log (100000000000 / 283956013999) ≤ (1043649161 / 1000000000) := by
  have h := checkLog_sound (w := (83956013999 / 483956013999)) (n := 12)
    (lo := (350501979 / 1000000000)) (hi := (17525099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283956013999 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283956013999 / 200000000000) = 1/(100000000000 / 283956013999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1043649159 / 1000000000) (1043649161 / 1000000000) (Real.log (283956013999 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (283956013999 / 100000000000) = -Real.log (100000000000 / 283956013999) := by
    rw [show ((283956013999 / 100000000000) : ℝ) = ((100000000000 / 283956013999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (524154373 / 500000000) ≤ -Real.log (7812500000 / 22287673377) ∧
    -Real.log (7812500000 / 22287673377) ≤ (262077187 / 250000000) := by
  have h := checkLog_sound (w := (6662673377 / 37912673377)) (n := 12)
    (lo := (177580783 / 500000000)) (hi := (355161567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22287673377 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(22287673377 / 15625000000) = 1/(7812500000 / 22287673377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (524154373 / 500000000) (262077187 / 250000000) (Real.log (22287673377 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22287673377 / 7812500000) = -Real.log (7812500000 / 22287673377) := by
    rw [show ((22287673377 / 7812500000) : ℝ) = ((7812500000 / 22287673377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (757662397 / 1000000000) ≤ -Real.log (500000000000 / 1066641809283) ∧
    -Real.log (500000000000 / 1066641809283) ≤ (757662399 / 1000000000) := by
  have h := checkLog_sound (w := (66641809283 / 2066641809283)) (n := 12)
    (lo := (64515217 / 1000000000)) (hi := (32257609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066641809283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066641809283 / 1000000000000) = 1/(500000000000 / 1066641809283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (757662397 / 1000000000) (757662399 / 1000000000) (Real.log (1066641809283 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1066641809283 / 500000000000) = -Real.log (500000000000 / 1066641809283) := by
    rw [show ((1066641809283 / 500000000000) : ℝ) = ((500000000000 / 1066641809283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (761199031 / 1000000000) ≤ -Real.log (500000000000 / 1070420809961) ∧
    -Real.log (500000000000 / 1070420809961) ≤ (761199033 / 1000000000) := by
  have h := checkLog_sound (w := (70420809961 / 2070420809961)) (n := 12)
    (lo := (68051851 / 1000000000)) (hi := (17012963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070420809961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070420809961 / 1000000000000) = 1/(500000000000 / 1070420809961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (761199031 / 1000000000) (761199033 / 1000000000) (Real.log (1070420809961 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1070420809961 / 500000000000) = -Real.log (500000000000 / 1070420809961) := by
    rw [show ((1070420809961 / 500000000000) : ℝ) = ((500000000000 / 1070420809961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0154
