import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0389
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

theorem reflection_log_1_neg : (202861121 / 1000000000) ≤ -Real.log (10240 / 12543) ∧
    -Real.log (10240 / 12543) ≤ (101430561 / 500000000) := by
  have h := checkLog_sound (w := (2303 / 22783)) (n := 12)
    (lo := (202861121 / 1000000000)) (hi := (101430561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12543 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12543 / 10240) = 1/(10240 / 12543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (202861121 / 1000000000) (101430561 / 500000000) (Real.log (12543 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12543 / 10240) = -Real.log (10240 / 12543) := by
    rw [show ((12543 / 10240) : ℝ) = ((10240 / 12543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (254766249 / 1000000000) ≤ -Real.log (7937 / 10240) ∧
    -Real.log (7937 / 10240) ≤ (203813 / 800000) := by
  have h := checkLog_sound (w := (2303 / 18177)) (n := 12)
    (lo := (254766249 / 1000000000)) (hi := (203813 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7937) = 1/(7937 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-203813 / 800000) (-254766249 / 1000000000) (Real.log (7937 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40524383 / 200000000) ≤ -Real.log (512 / 627) ∧
    -Real.log (512 / 627) ≤ (50655479 / 250000000) := by
  have h := checkLog_sound (w := (115 / 1139)) (n := 12)
    (lo := (40524383 / 200000000)) (hi := (50655479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627 / 512) = 1/(512 / 627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40524383 / 200000000) (50655479 / 250000000) (Real.log (627 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (627 / 512) = -Real.log (512 / 627) := by
    rw [show ((627 / 512) : ℝ) = ((512 / 627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31798543 / 125000000) ≤ -Real.log (397 / 512) ∧
    -Real.log (397 / 512) ≤ (50877669 / 200000000) := by
  have h := checkLog_sound (w := (115 / 909)) (n := 12)
    (lo := (31798543 / 125000000)) (hi := (50877669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 397) = 1/(397 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-50877669 / 200000000) (-31798543 / 125000000) (Real.log (397 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (371428849 / 1000000000) ≤ -Real.log (5120 / 7423) ∧
    -Real.log (5120 / 7423) ≤ (7428577 / 20000000) := by
  have h := checkLog_sound (w := (2303 / 12543)) (n := 12)
    (lo := (371428849 / 1000000000)) (hi := (7428577 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7423 / 5120) = 1/(5120 / 7423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (371428849 / 1000000000) (7428577 / 20000000) (Real.log (7423 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7423 / 5120) = -Real.log (5120 / 7423) := by
    rw [show ((7423 / 5120) : ℝ) = ((5120 / 7423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11949639 / 20000000) ≤ -Real.log (2817 / 5120) ∧
    -Real.log (2817 / 5120) ≤ (597481951 / 1000000000) := by
  have h := checkLog_sound (w := (2303 / 7937)) (n := 12)
    (lo := (11949639 / 20000000)) (hi := (597481951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2817) = 1/(2817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-597481951 / 1000000000) (-11949639 / 20000000) (Real.log (2817 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (185512309 / 500000000) ≤ -Real.log (256 / 371) ∧
    -Real.log (256 / 371) ≤ (371024619 / 1000000000) := by
  have h := checkLog_sound (w := (115 / 627)) (n := 12)
    (lo := (185512309 / 500000000)) (hi := (371024619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 256) = 1/(256 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (185512309 / 500000000) (371024619 / 1000000000) (Real.log (371 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (371 / 256) = -Real.log (256 / 371) := by
    rw [show ((371 / 256) : ℝ) = ((256 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298208777 / 500000000) ≤ -Real.log (141 / 256) ∧
    -Real.log (141 / 256) ≤ (119283511 / 200000000) := by
  have h := checkLog_sound (w := (115 / 397)) (n := 12)
    (lo := (298208777 / 500000000)) (hi := (119283511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 141) = 1/(141 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119283511 / 200000000) (-298208777 / 500000000) (Real.log (141 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (278061189 / 1000000000) ≤ -Real.log (1000000 / 1320567) ∧
    -Real.log (1000000 / 1320567) ≤ (27806119 / 100000000) := by
  have h := checkLog_sound (w := (320567 / 2320567)) (n := 12)
    (lo := (278061189 / 1000000000)) (hi := (27806119 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320567 / 1000000) = 1/(1000000 / 1320567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (278061189 / 1000000000) (27806119 / 100000000) (Real.log (1320567 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1320567 / 1000000) = -Real.log (1000000 / 1320567) := by
    rw [show ((1320567 / 1000000) : ℝ) = ((1000000 / 1320567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96624163 / 250000000) ≤ -Real.log (679433 / 1000000) ∧
    -Real.log (679433 / 1000000) ≤ (386496653 / 1000000000) := by
  have h := checkLog_sound (w := (320567 / 1679433)) (n := 12)
    (lo := (96624163 / 250000000)) (hi := (386496653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679433) = 1/(679433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-386496653 / 1000000000) (-96624163 / 250000000) (Real.log (679433 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (278384483 / 1000000000) ≤ -Real.log (500000 / 660497) ∧
    -Real.log (500000 / 660497) ≤ (69596121 / 250000000) := by
  have h := checkLog_sound (w := (160497 / 1160497)) (n := 12)
    (lo := (278384483 / 1000000000)) (hi := (69596121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660497 / 500000) = 1/(500000 / 660497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (278384483 / 1000000000) (69596121 / 250000000) (Real.log (660497 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (660497 / 500000) = -Real.log (500000 / 660497) := by
    rw [show ((660497 / 500000) : ℝ) = ((500000 / 660497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (193562657 / 500000000) ≤ -Real.log (339503 / 500000) ∧
    -Real.log (339503 / 500000) ≤ (77425063 / 200000000) := by
  have h := checkLog_sound (w := (160497 / 839503)) (n := 12)
    (lo := (193562657 / 500000000)) (hi := (77425063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 339503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 339503) = 1/(339503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-77425063 / 200000000) (-193562657 / 500000000) (Real.log (339503 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (209703233 / 1000000000) ≤ -Real.log (31250 / 38541) ∧
    -Real.log (31250 / 38541) ≤ (104851617 / 500000000) := by
  have h := checkLog_sound (w := (7291 / 69791)) (n := 12)
    (lo := (209703233 / 1000000000)) (hi := (104851617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38541 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38541 / 31250) = 1/(31250 / 38541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (209703233 / 1000000000) (104851617 / 500000000) (Real.log (38541 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (38541 / 31250) = -Real.log (31250 / 38541) := by
    rw [show ((38541 / 31250) : ℝ) = ((31250 / 38541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13283767 / 50000000) ≤ -Real.log (23959 / 31250) ∧
    -Real.log (23959 / 31250) ≤ (265675341 / 1000000000) := by
  have h := checkLog_sound (w := (7291 / 55209)) (n := 12)
    (lo := (13283767 / 50000000)) (hi := (265675341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23959) = 1/(23959 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-265675341 / 1000000000) (-13283767 / 50000000) (Real.log (23959 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (209969959 / 1000000000) ≤ -Real.log (1000000 / 1233641) ∧
    -Real.log (1000000 / 1233641) ≤ (5249249 / 25000000) := by
  have h := checkLog_sound (w := (233641 / 2233641)) (n := 12)
    (lo := (209969959 / 1000000000)) (hi := (5249249 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233641 / 1000000) = 1/(1000000 / 1233641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (209969959 / 1000000000) (5249249 / 25000000) (Real.log (1233641 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1233641 / 1000000) = -Real.log (1000000 / 1233641) := by
    rw [show ((1233641 / 1000000) : ℝ) = ((1000000 / 1233641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5322091 / 20000000) ≤ -Real.log (766359 / 1000000) ∧
    -Real.log (766359 / 1000000) ≤ (266104551 / 1000000000) := by
  have h := checkLog_sound (w := (233641 / 1766359)) (n := 12)
    (lo := (5322091 / 20000000)) (hi := (266104551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766359) = 1/(766359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-266104551 / 1000000000) (-5322091 / 20000000) (Real.log (766359 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (664557841 / 1000000000) ≤ -Real.log (500000000000 / 971815469663) ∧
    -Real.log (500000000000 / 971815469663) ≤ (332278921 / 500000000) := by
  have h := checkLog_sound (w := (471815469663 / 1471815469663)) (n := 12)
    (lo := (664557841 / 1000000000)) (hi := (332278921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971815469663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971815469663 / 500000000000) = 1/(500000000000 / 971815469663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (664557841 / 1000000000) (332278921 / 500000000) (Real.log (971815469663 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (971815469663 / 500000000000) = -Real.log (500000000000 / 971815469663) := by
    rw [show ((971815469663 / 500000000000) : ℝ) = ((500000000000 / 971815469663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (332754899 / 500000000) ≤ -Real.log (250000000000 / 486370518081) ∧
    -Real.log (250000000000 / 486370518081) ≤ (665509799 / 1000000000) := by
  have h := checkLog_sound (w := (236370518081 / 736370518081)) (n := 12)
    (lo := (332754899 / 500000000)) (hi := (665509799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486370518081 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486370518081 / 250000000000) = 1/(250000000000 / 486370518081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (332754899 / 500000000) (665509799 / 1000000000) (Real.log (486370518081 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (486370518081 / 250000000000) = -Real.log (250000000000 / 486370518081) := by
    rw [show ((486370518081 / 250000000000) : ℝ) = ((250000000000 / 486370518081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (475378573 / 1000000000) ≤ -Real.log (2500000000 / 4021557661) ∧
    -Real.log (2500000000 / 4021557661) ≤ (237689287 / 500000000) := by
  have h := checkLog_sound (w := (1521557661 / 6521557661)) (n := 12)
    (lo := (475378573 / 1000000000)) (hi := (237689287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4021557661 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4021557661 / 2500000000) = 1/(2500000000 / 4021557661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (475378573 / 1000000000) (237689287 / 500000000) (Real.log (4021557661 / 2500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4021557661 / 2500000000) = -Real.log (2500000000 / 4021557661) := by
    rw [show ((4021557661 / 2500000000) : ℝ) = ((2500000000 / 4021557661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (476074509 / 1000000000) ≤ -Real.log (125000000000 / 201217869171) ∧
    -Real.log (125000000000 / 201217869171) ≤ (47607451 / 100000000) := by
  have h := checkLog_sound (w := (76217869171 / 326217869171)) (n := 12)
    (lo := (476074509 / 1000000000)) (hi := (47607451 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201217869171 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201217869171 / 125000000000) = 1/(125000000000 / 201217869171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (476074509 / 1000000000) (47607451 / 100000000) (Real.log (201217869171 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (201217869171 / 125000000000) = -Real.log (125000000000 / 201217869171) := by
    rw [show ((201217869171 / 125000000000) : ℝ) = ((125000000000 / 201217869171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0389
