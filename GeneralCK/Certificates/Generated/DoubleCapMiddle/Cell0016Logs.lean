import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0016
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

theorem reflection_log_1_neg : (50193901 / 125000000) ≤ -Real.log (512 / 765) ∧
    -Real.log (512 / 765) ≤ (401551209 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1277)) (n := 12)
    (lo := (50193901 / 125000000)) (hi := (401551209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765 / 512) = 1/(512 / 765) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50193901 / 125000000) (401551209 / 1000000000) (Real.log (765 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (765 / 512) = -Real.log (512 / 765) := by
    rw [show ((765 / 512) : ℝ) = ((512 / 765) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (681496563 / 1000000000) ≤ -Real.log (259 / 512) ∧
    -Real.log (259 / 512) ≤ (170374141 / 250000000) := by
  have h := checkLog_sound (w := (253 / 771)) (n := 12)
    (lo := (681496563 / 1000000000)) (hi := (170374141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 259) = 1/(259 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170374141 / 250000000) (-681496563 / 1000000000) (Real.log (259 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (400766587 / 1000000000) ≤ -Real.log (1280 / 1911) ∧
    -Real.log (1280 / 1911) ≤ (100191647 / 250000000) := by
  have h := checkLog_sound (w := (631 / 3191)) (n := 12)
    (lo := (400766587 / 1000000000)) (hi := (100191647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1280) = 1/(1280 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (400766587 / 1000000000) (100191647 / 250000000) (Real.log (1911 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1911 / 1280) = -Real.log (1280 / 1911) := by
    rw [show ((1911 / 1280) : ℝ) = ((1280 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8489783 / 12500000) ≤ -Real.log (649 / 1280) ∧
    -Real.log (649 / 1280) ≤ (679182641 / 1000000000) := by
  have h := checkLog_sound (w := (631 / 1929)) (n := 12)
    (lo := (8489783 / 12500000)) (hi := (679182641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 649) = 1/(649 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-679182641 / 1000000000) (-8489783 / 12500000) (Real.log (649 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171817643 / 250000000) ≤ -Real.log (256 / 509) ∧
    -Real.log (256 / 509) ≤ (687270573 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 765)) (n := 12)
    (lo := (171817643 / 250000000)) (hi := (687270573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 256) = 1/(256 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171817643 / 250000000) (687270573 / 1000000000) (Real.log (509 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (509 / 256) = -Real.log (256 / 509) := by
    rw [show ((509 / 256) : ℝ) = ((256 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138955161 / 31250000) ≤ -Real.log (3 / 256) ∧
    -Real.log (3 / 256) ≤ (4446565159 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4 / 3) = 1/(3 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4446565159 / 1000000000) (-138955161 / 31250000) (Real.log (3 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343045547 / 500000000) ≤ -Real.log (640 / 1271) ∧
    -Real.log (640 / 1271) ≤ (137218219 / 200000000) := by
  have h := checkLog_sound (w := (631 / 1911)) (n := 12)
    (lo := (343045547 / 500000000)) (hi := (137218219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 640) = 1/(640 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343045547 / 500000000) (137218219 / 200000000) (Real.log (1271 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1271 / 640) = -Real.log (640 / 1271) := by
    rw [show ((1271 / 640) : ℝ) = ((640 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (852848719 / 200000000) ≤ -Real.log (9 / 640) ∧
    -Real.log (9 / 640) ≤ (2132121801 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10 / 9) = 1/(9 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2132121801 / 500000000) (-852848719 / 200000000) (Real.log (9 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (70622813 / 125000000) ≤ -Real.log (1000000 / 1759417) ∧
    -Real.log (1000000 / 1759417) ≤ (112996501 / 200000000) := by
  have h := checkLog_sound (w := (759417 / 2759417)) (n := 12)
    (lo := (70622813 / 125000000)) (hi := (112996501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1759417 / 1000000) = 1/(1000000 / 1759417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (70622813 / 125000000) (112996501 / 200000000) (Real.log (1759417 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1759417 / 1000000) = -Real.log (1000000 / 1759417) := by
    rw [show ((1759417 / 1000000) : ℝ) = ((1000000 / 1759417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1424690133 / 1000000000) ≤ -Real.log (240583 / 1000000) ∧
    -Real.log (240583 / 1000000) ≤ (178086267 / 125000000) := by
  have h := checkLog_sound (w := (9417 / 490583)) (n := 12)
    (lo := (38395773 / 1000000000)) (hi := (19197887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 240583) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 240583) = 1/(240583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178086267 / 125000000) (-1424690133 / 1000000000) (Real.log (240583 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (566662331 / 1000000000) ≤ -Real.log (8000 / 14099) ∧
    -Real.log (8000 / 14099) ≤ (141665583 / 250000000) := by
  have h := checkLog_sound (w := (6099 / 22099)) (n := 12)
    (lo := (566662331 / 1000000000)) (hi := (141665583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14099 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14099 / 8000) = 1/(8000 / 14099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (566662331 / 1000000000) (141665583 / 250000000) (Real.log (14099 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14099 / 8000) = -Real.log (8000 / 14099) := by
    rw [show ((14099 / 8000) : ℝ) = ((8000 / 14099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1437061477 / 1000000000) ≤ -Real.log (1901 / 8000) ∧
    -Real.log (1901 / 8000) ≤ (35926537 / 25000000) := by
  have h := checkLog_sound (w := (99 / 3901)) (n := 12)
    (lo := (50767117 / 1000000000)) (hi := (25383559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1901) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2000 / 1901) = 1/(1901 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35926537 / 25000000) (-1437061477 / 1000000000) (Real.log (1901 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (492367923 / 1000000000) ≤ -Real.log (500000 / 818093) ∧
    -Real.log (500000 / 818093) ≤ (123091981 / 250000000) := by
  have h := checkLog_sound (w := (318093 / 1318093)) (n := 12)
    (lo := (492367923 / 1000000000)) (hi := (123091981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818093 / 500000) = 1/(500000 / 818093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (492367923 / 1000000000) (123091981 / 250000000) (Real.log (818093 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (818093 / 500000) = -Real.log (500000 / 818093) := by
    rw [show ((818093 / 500000) : ℝ) = ((500000 / 818093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (101111253 / 100000000) ≤ -Real.log (181907 / 500000) ∧
    -Real.log (181907 / 500000) ≤ (252778133 / 250000000) := by
  have h := checkLog_sound (w := (68093 / 431907)) (n := 12)
    (lo := (6359307 / 20000000)) (hi := (317965351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 181907) = 1/(181907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-252778133 / 250000000) (-101111253 / 100000000) (Real.log (181907 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (494383997 / 1000000000) ≤ -Real.log (15625 / 25617) ∧
    -Real.log (15625 / 25617) ≤ (247191999 / 500000000) := by
  have h := checkLog_sound (w := (4996 / 20621)) (n := 12)
    (lo := (494383997 / 1000000000)) (hi := (247191999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25617 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25617 / 15625) = 1/(15625 / 25617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (494383997 / 1000000000) (247191999 / 500000000) (Real.log (25617 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25617 / 15625) = -Real.log (15625 / 25617) := by
    rw [show ((25617 / 15625) : ℝ) = ((15625 / 25617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (204046007 / 200000000) ≤ -Real.log (5633 / 15625) ∧
    -Real.log (5633 / 15625) ≤ (1020230037 / 1000000000) := by
  have h := checkLog_sound (w := (4359 / 26891)) (n := 12)
    (lo := (65416571 / 200000000)) (hi := (40885357 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11266) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 11266) = 1/(5633 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1020230037 / 1000000000) (-204046007 / 200000000) (Real.log (5633 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1989672637 / 1000000000) ≤ -Real.log (100000000000 / 731313933237) ∧
    -Real.log (100000000000 / 731313933237) ≤ (6217727 / 3125000) := by
  have h := checkLog_sound (w := (331313933237 / 1131313933237)) (n := 12)
    (lo := (603378277 / 1000000000)) (hi := (301689139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731313933237 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(731313933237 / 400000000000) = 1/(100000000000 / 731313933237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1989672637 / 1000000000) (6217727 / 3125000) (Real.log (731313933237 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (731313933237 / 100000000000) = -Real.log (100000000000 / 731313933237) := by
    rw [show ((731313933237 / 100000000000) : ℝ) = ((100000000000 / 731313933237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (62616369 / 31250000) ≤ -Real.log (100000000000 / 741662283009) ∧
    -Real.log (100000000000 / 741662283009) ≤ (2003723811 / 1000000000) := by
  have h := checkLog_sound (w := (341662283009 / 1141662283009)) (n := 12)
    (lo := (77178681 / 125000000)) (hi := (617429449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741662283009 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(741662283009 / 400000000000) = 1/(100000000000 / 741662283009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (62616369 / 31250000) (2003723811 / 1000000000) (Real.log (741662283009 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741662283009 / 100000000000) = -Real.log (100000000000 / 741662283009) := by
    rw [show ((741662283009 / 100000000000) : ℝ) = ((100000000000 / 741662283009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1503480453 / 1000000000) ≤ -Real.log (250000000000 / 1124328640459) ∧
    -Real.log (250000000000 / 1124328640459) ≤ (187935057 / 125000000) := by
  have h := checkLog_sound (w := (124328640459 / 2124328640459)) (n := 12)
    (lo := (117186093 / 1000000000)) (hi := (58593047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1124328640459 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1124328640459 / 1000000000000) = 1/(250000000000 / 1124328640459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1503480453 / 1000000000) (187935057 / 125000000) (Real.log (1124328640459 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1124328640459 / 250000000000) = -Real.log (250000000000 / 1124328640459) := by
    rw [show ((1124328640459 / 250000000000) : ℝ) = ((250000000000 / 1124328640459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (94663377 / 62500000) ≤ -Real.log (50000000000 / 227383277117) ∧
    -Real.log (50000000000 / 227383277117) ≤ (302922807 / 200000000) := by
  have h := checkLog_sound (w := (27383277117 / 427383277117)) (n := 12)
    (lo := (16039959 / 125000000)) (hi := (128319673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227383277117 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(227383277117 / 200000000000) = 1/(50000000000 / 227383277117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (94663377 / 62500000) (302922807 / 200000000) (Real.log (227383277117 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (227383277117 / 50000000000) = -Real.log (50000000000 / 227383277117) := by
    rw [show ((227383277117 / 50000000000) : ℝ) = ((50000000000 / 227383277117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0016
