import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0156
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

theorem reflection_log_1_neg : (285237681 / 1000000000) ≤ -Real.log (512 / 681) ∧
    -Real.log (512 / 681) ≤ (142618841 / 500000000) := by
  have h := checkLog_sound (w := (169 / 1193)) (n := 12)
    (lo := (285237681 / 1000000000)) (hi := (142618841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 512) = 1/(512 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (285237681 / 1000000000) (142618841 / 500000000) (Real.log (681 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (681 / 512) = -Real.log (512 / 681) := by
    rw [show ((681 / 512) : ℝ) = ((512 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (400594177 / 1000000000) ≤ -Real.log (343 / 512) ∧
    -Real.log (343 / 512) ≤ (200297089 / 500000000) := by
  have h := checkLog_sound (w := (169 / 855)) (n := 12)
    (lo := (400594177 / 1000000000)) (hi := (200297089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 343) = 1/(343 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200297089 / 500000000) (-400594177 / 1000000000) (Real.log (343 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56959411 / 200000000) ≤ -Real.log (5120 / 6807) ∧
    -Real.log (5120 / 6807) ≤ (2224977 / 7812500) := by
  have h := checkLog_sound (w := (1687 / 11927)) (n := 12)
    (lo := (56959411 / 200000000)) (hi := (2224977 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6807 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6807 / 5120) = 1/(5120 / 6807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56959411 / 200000000) (2224977 / 7812500) (Real.log (6807 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6807 / 5120) = -Real.log (5120 / 6807) := by
    rw [show ((6807 / 5120) : ℝ) = ((5120 / 6807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (99929981 / 250000000) ≤ -Real.log (3433 / 5120) ∧
    -Real.log (3433 / 5120) ≤ (15988797 / 40000000) := by
  have h := checkLog_sound (w := (1687 / 8553)) (n := 12)
    (lo := (99929981 / 250000000)) (hi := (15988797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3433) = 1/(3433 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15988797 / 40000000) (-99929981 / 250000000) (Real.log (3433 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (126727931 / 250000000) ≤ -Real.log (256 / 425) ∧
    -Real.log (256 / 425) ≤ (20276469 / 40000000) := by
  have h := checkLog_sound (w := (169 / 681)) (n := 12)
    (lo := (126727931 / 250000000)) (hi := (20276469 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425 / 256) = 1/(256 / 425) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (126727931 / 250000000) (20276469 / 40000000) (Real.log (425 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (425 / 256) = -Real.log (256 / 425) := by
    rw [show ((425 / 256) : ℝ) = ((256 / 425) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (43170773 / 40000000) ≤ -Real.log (87 / 256) ∧
    -Real.log (87 / 256) ≤ (1079269327 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 87) = 1/(87 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1079269327 / 1000000000) (-43170773 / 40000000) (Real.log (87 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (63275699 / 125000000) ≤ -Real.log (2560 / 4247) ∧
    -Real.log (2560 / 4247) ≤ (506205593 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 6807)) (n := 12)
    (lo := (63275699 / 125000000)) (hi := (506205593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4247 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4247 / 2560) = 1/(2560 / 4247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (63275699 / 125000000) (506205593 / 1000000000) (Real.log (4247 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4247 / 2560) = -Real.log (2560 / 4247) := by
    rw [show ((4247 / 2560) : ℝ) = ((2560 / 4247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1075826981 / 1000000000) ≤ -Real.log (873 / 2560) ∧
    -Real.log (873 / 2560) ≤ (1075826983 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 873) = 1/(873 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1075826983 / 1000000000) (-1075826981 / 1000000000) (Real.log (873 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38962227 / 100000000) ≤ -Real.log (1000000 / 1476423) ∧
    -Real.log (1000000 / 1476423) ≤ (389622271 / 1000000000) := by
  have h := checkLog_sound (w := (476423 / 2476423)) (n := 12)
    (lo := (38962227 / 100000000)) (hi := (389622271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1476423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1476423 / 1000000) = 1/(1000000 / 1476423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38962227 / 100000000) (389622271 / 1000000000) (Real.log (1476423 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1476423 / 1000000) = -Real.log (1000000 / 1476423) := by
    rw [show ((1476423 / 1000000) : ℝ) = ((1000000 / 1476423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (161767793 / 250000000) ≤ -Real.log (523577 / 1000000) ∧
    -Real.log (523577 / 1000000) ≤ (647071173 / 1000000000) := by
  have h := checkLog_sound (w := (476423 / 1523577)) (n := 12)
    (lo := (161767793 / 250000000)) (hi := (647071173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 523577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 523577) = 1/(523577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-647071173 / 1000000000) (-161767793 / 250000000) (Real.log (523577 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (195114479 / 500000000) ≤ -Real.log (1000000 / 1477319) ∧
    -Real.log (1000000 / 1477319) ≤ (390228959 / 1000000000) := by
  have h := checkLog_sound (w := (477319 / 2477319)) (n := 12)
    (lo := (195114479 / 500000000)) (hi := (390228959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1477319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1477319 / 1000000) = 1/(1000000 / 1477319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (195114479 / 500000000) (390228959 / 1000000000) (Real.log (1477319 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1477319 / 1000000) = -Real.log (1000000 / 1477319) := by
    rw [show ((1477319 / 1000000) : ℝ) = ((1000000 / 1477319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (648783943 / 1000000000) ≤ -Real.log (522681 / 1000000) ∧
    -Real.log (522681 / 1000000) ≤ (81097993 / 125000000) := by
  have h := checkLog_sound (w := (477319 / 1522681)) (n := 12)
    (lo := (648783943 / 1000000000)) (hi := (81097993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 522681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 522681) = 1/(522681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-81097993 / 125000000) (-648783943 / 1000000000) (Real.log (522681 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (307039747 / 1000000000) ≤ -Real.log (200000 / 271879) ∧
    -Real.log (200000 / 271879) ≤ (76759937 / 250000000) := by
  have h := checkLog_sound (w := (71879 / 471879)) (n := 12)
    (lo := (307039747 / 1000000000)) (hi := (76759937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271879 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271879 / 200000) = 1/(200000 / 271879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (307039747 / 1000000000) (76759937 / 250000000) (Real.log (271879 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (271879 / 200000) = -Real.log (200000 / 271879) := by
    rw [show ((271879 / 200000) : ℝ) = ((200000 / 271879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (111335559 / 250000000) ≤ -Real.log (128121 / 200000) ∧
    -Real.log (128121 / 200000) ≤ (445342237 / 1000000000) := by
  have h := checkLog_sound (w := (71879 / 328121)) (n := 12)
    (lo := (111335559 / 250000000)) (hi := (445342237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 128121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 128121) = 1/(128121 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-445342237 / 1000000000) (-111335559 / 250000000) (Real.log (128121 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12304123 / 40000000) ≤ -Real.log (1000000 / 1360161) ∧
    -Real.log (1000000 / 1360161) ≤ (76900769 / 250000000) := by
  have h := checkLog_sound (w := (360161 / 2360161)) (n := 12)
    (lo := (12304123 / 40000000)) (hi := (76900769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1360161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1360161 / 1000000) = 1/(1000000 / 1360161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12304123 / 40000000) (76900769 / 250000000) (Real.log (1360161 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1360161 / 1000000) = -Real.log (1000000 / 1360161) := by
    rw [show ((1360161 / 1000000) : ℝ) = ((1000000 / 1360161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55817337 / 125000000) ≤ -Real.log (639839 / 1000000) ∧
    -Real.log (639839 / 1000000) ≤ (446538697 / 1000000000) := by
  have h := checkLog_sound (w := (360161 / 1639839)) (n := 12)
    (lo := (55817337 / 125000000)) (hi := (446538697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 639839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 639839) = 1/(639839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-446538697 / 1000000000) (-55817337 / 125000000) (Real.log (639839 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (518346721 / 500000000) ≤ -Real.log (62500000000 / 176242343533) ∧
    -Real.log (62500000000 / 176242343533) ≤ (259173361 / 250000000) := by
  have h := checkLog_sound (w := (51242343533 / 301242343533)) (n := 12)
    (lo := (171773131 / 500000000)) (hi := (343546263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176242343533 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(176242343533 / 125000000000) = 1/(62500000000 / 176242343533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (518346721 / 500000000) (259173361 / 250000000) (Real.log (176242343533 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (176242343533 / 62500000000) = -Real.log (62500000000 / 176242343533) := by
    rw [show ((176242343533 / 62500000000) : ℝ) = ((62500000000 / 176242343533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1039012901 / 1000000000) ≤ -Real.log (500000000000 / 1413212839189) ∧
    -Real.log (500000000000 / 1413212839189) ≤ (1039012903 / 1000000000) := by
  have h := checkLog_sound (w := (413212839189 / 2413212839189)) (n := 12)
    (lo := (345865721 / 1000000000)) (hi := (172932861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413212839189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1413212839189 / 1000000000000) = 1/(500000000000 / 1413212839189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1039012901 / 1000000000) (1039012903 / 1000000000) (Real.log (1413212839189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1413212839189 / 500000000000) = -Real.log (500000000000 / 1413212839189) := by
    rw [show ((1413212839189 / 500000000000) : ℝ) = ((500000000000 / 1413212839189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (752381983 / 1000000000) ≤ -Real.log (250000000000 / 530512172087) ∧
    -Real.log (250000000000 / 530512172087) ≤ (150476397 / 200000000) := by
  have h := checkLog_sound (w := (30512172087 / 1030512172087)) (n := 12)
    (lo := (59234803 / 1000000000)) (hi := (14808701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((530512172087 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(530512172087 / 500000000000) = 1/(250000000000 / 530512172087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (752381983 / 1000000000) (150476397 / 200000000) (Real.log (530512172087 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (530512172087 / 250000000000) = -Real.log (250000000000 / 530512172087) := by
    rw [show ((530512172087 / 250000000000) : ℝ) = ((250000000000 / 530512172087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (754141771 / 1000000000) ≤ -Real.log (1953125000 / 4151926427) ∧
    -Real.log (1953125000 / 4151926427) ≤ (754141773 / 1000000000) := by
  have h := checkLog_sound (w := (245676427 / 8058176427)) (n := 12)
    (lo := (60994591 / 1000000000)) (hi := (1906081 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4151926427 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4151926427 / 3906250000) = 1/(1953125000 / 4151926427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (754141771 / 1000000000) (754141773 / 1000000000) (Real.log (4151926427 / 1953125000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4151926427 / 1953125000) = -Real.log (1953125000 / 4151926427) := by
    rw [show ((4151926427 / 1953125000) : ℝ) = ((1953125000 / 4151926427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0156
