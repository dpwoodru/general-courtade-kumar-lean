import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0360
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

theorem reflection_log_1_neg : (52443329 / 250000000) ≤ -Real.log (1024 / 1263) ∧
    -Real.log (1024 / 1263) ≤ (209773317 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2287)) (n := 12)
    (lo := (52443329 / 250000000)) (hi := (209773317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263 / 1024) = 1/(1024 / 1263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (52443329 / 250000000) (209773317 / 1000000000) (Real.log (1263 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1263 / 1024) = -Real.log (1024 / 1263) := by
    rw [show ((1263 / 1024) : ℝ) = ((1024 / 1263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (265788087 / 1000000000) ≤ -Real.log (785 / 1024) ∧
    -Real.log (785 / 1024) ≤ (33223511 / 125000000) := by
  have h := checkLog_sound (w := (239 / 1809)) (n := 12)
    (lo := (265788087 / 1000000000)) (hi := (33223511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 785) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 785) = 1/(785 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33223511 / 125000000) (-265788087 / 1000000000) (Real.log (785 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104767879 / 500000000) ≤ -Real.log (10240 / 12627) ∧
    -Real.log (10240 / 12627) ≤ (209535759 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 22867)) (n := 12)
    (lo := (104767879 / 500000000)) (hi := (209535759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12627 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12627 / 10240) = 1/(10240 / 12627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104767879 / 500000000) (209535759 / 1000000000) (Real.log (12627 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12627 / 10240) = -Real.log (10240 / 12627) := by
    rw [show ((12627 / 10240) : ℝ) = ((10240 / 12627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (53081199 / 200000000) ≤ -Real.log (7853 / 10240) ∧
    -Real.log (7853 / 10240) ≤ (66351499 / 250000000) := by
  have h := checkLog_sound (w := (2387 / 18093)) (n := 12)
    (lo := (53081199 / 200000000)) (hi := (66351499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7853) = 1/(7853 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-66351499 / 250000000) (-53081199 / 200000000) (Real.log (7853 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (191540513 / 500000000) ≤ -Real.log (512 / 751) ∧
    -Real.log (512 / 751) ≤ (383081027 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1263)) (n := 12)
    (lo := (191540513 / 500000000)) (hi := (383081027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751 / 512) = 1/(512 / 751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (191540513 / 500000000) (383081027 / 1000000000) (Real.log (751 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (751 / 512) = -Real.log (512 / 751) := by
    rw [show ((751 / 512) : ℝ) = ((512 / 751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (628852829 / 1000000000) ≤ -Real.log (273 / 512) ∧
    -Real.log (273 / 512) ≤ (62885283 / 100000000) := by
  have h := checkLog_sound (w := (239 / 785)) (n := 12)
    (lo := (628852829 / 1000000000)) (hi := (62885283 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 273) = 1/(273 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62885283 / 100000000) (-628852829 / 1000000000) (Real.log (273 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (382681479 / 1000000000) ≤ -Real.log (5120 / 7507) ∧
    -Real.log (5120 / 7507) ≤ (9567037 / 25000000) := by
  have h := checkLog_sound (w := (2387 / 12627)) (n := 12)
    (lo := (382681479 / 1000000000)) (hi := (9567037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7507 / 5120) = 1/(5120 / 7507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (382681479 / 1000000000) (9567037 / 25000000) (Real.log (7507 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7507 / 5120) = -Real.log (5120 / 7507) := by
    rw [show ((7507 / 5120) : ℝ) = ((5120 / 7507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (156938633 / 250000000) ≤ -Real.log (2733 / 5120) ∧
    -Real.log (2733 / 5120) ≤ (627754533 / 1000000000) := by
  have h := checkLog_sound (w := (2387 / 7853)) (n := 12)
    (lo := (156938633 / 250000000)) (hi := (627754533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2733) = 1/(2733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-627754533 / 1000000000) (-156938633 / 250000000) (Real.log (2733 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (287395281 / 1000000000) ≤ -Real.log (1000000 / 1332951) ∧
    -Real.log (1000000 / 1332951) ≤ (143697641 / 500000000) := by
  have h := checkLog_sound (w := (332951 / 2332951)) (n := 12)
    (lo := (287395281 / 1000000000)) (hi := (143697641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332951 / 1000000) = 1/(1000000 / 1332951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (287395281 / 1000000000) (143697641 / 500000000) (Real.log (1332951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1332951 / 1000000) = -Real.log (1000000 / 1332951) := by
    rw [show ((1332951 / 1000000) : ℝ) = ((1000000 / 1332951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101222943 / 250000000) ≤ -Real.log (667049 / 1000000) ∧
    -Real.log (667049 / 1000000) ≤ (404891773 / 1000000000) := by
  have h := checkLog_sound (w := (332951 / 1667049)) (n := 12)
    (lo := (101222943 / 250000000)) (hi := (404891773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667049) = 1/(667049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-404891773 / 1000000000) (-101222943 / 250000000) (Real.log (667049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (287717071 / 1000000000) ≤ -Real.log (50000 / 66669) ∧
    -Real.log (50000 / 66669) ≤ (17982317 / 62500000) := by
  have h := checkLog_sound (w := (16669 / 116669)) (n := 12)
    (lo := (287717071 / 1000000000)) (hi := (17982317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66669 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66669 / 50000) = 1/(50000 / 66669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (287717071 / 1000000000) (17982317 / 62500000) (Real.log (66669 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (66669 / 50000) = -Real.log (50000 / 66669) := by
    rw [show ((66669 / 50000) : ℝ) = ((50000 / 66669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (40553511 / 100000000) ≤ -Real.log (33331 / 50000) ∧
    -Real.log (33331 / 50000) ≤ (405535111 / 1000000000) := by
  have h := checkLog_sound (w := (16669 / 83331)) (n := 12)
    (lo := (40553511 / 100000000)) (hi := (405535111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33331) = 1/(33331 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-405535111 / 1000000000) (-40553511 / 100000000) (Real.log (33331 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (43486897 / 200000000) ≤ -Real.log (250000 / 310721) ∧
    -Real.log (250000 / 310721) ≤ (108717243 / 500000000) := by
  have h := checkLog_sound (w := (60721 / 560721)) (n := 12)
    (lo := (43486897 / 200000000)) (hi := (108717243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310721 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310721 / 250000) = 1/(250000 / 310721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (43486897 / 200000000) (108717243 / 500000000) (Real.log (310721 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (310721 / 250000) = -Real.log (250000 / 310721) := by
    rw [show ((310721 / 250000) : ℝ) = ((250000 / 310721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (695597 / 2500000) ≤ -Real.log (189279 / 250000) ∧
    -Real.log (189279 / 250000) ≤ (278238801 / 1000000000) := by
  have h := checkLog_sound (w := (60721 / 439279)) (n := 12)
    (lo := (695597 / 2500000)) (hi := (278238801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189279) = 1/(189279 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-278238801 / 1000000000) (-695597 / 2500000) (Real.log (189279 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21770157 / 100000000) ≤ -Real.log (62500 / 77701) ∧
    -Real.log (62500 / 77701) ≤ (217701571 / 1000000000) := by
  have h := checkLog_sound (w := (15201 / 140201)) (n := 12)
    (lo := (21770157 / 100000000)) (hi := (217701571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77701 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77701 / 62500) = 1/(62500 / 77701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21770157 / 100000000) (217701571 / 1000000000) (Real.log (77701 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (77701 / 62500) = -Real.log (62500 / 77701) := by
    rw [show ((77701 / 62500) : ℝ) = ((62500 / 77701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (278677403 / 1000000000) ≤ -Real.log (47299 / 62500) ∧
    -Real.log (47299 / 62500) ≤ (69669351 / 250000000) := by
  have h := checkLog_sound (w := (15201 / 109799)) (n := 12)
    (lo := (278677403 / 1000000000)) (hi := (69669351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47299) = 1/(47299 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-69669351 / 250000000) (-278677403 / 1000000000) (Real.log (47299 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (692287053 / 1000000000) ≤ -Real.log (50000000000 / 99914024307) ∧
    -Real.log (50000000000 / 99914024307) ≤ (346143527 / 500000000) := by
  have h := checkLog_sound (w := (49914024307 / 149914024307)) (n := 12)
    (lo := (692287053 / 1000000000)) (hi := (346143527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99914024307 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99914024307 / 50000000000) = 1/(50000000000 / 99914024307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (692287053 / 1000000000) (346143527 / 500000000) (Real.log (99914024307 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99914024307 / 50000000000) = -Real.log (50000000000 / 99914024307) := by
    rw [show ((99914024307 / 50000000000) : ℝ) = ((50000000000 / 99914024307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (693252181 / 1000000000) ≤ -Real.log (500000000000 / 1000105007351) ∧
    -Real.log (500000000000 / 1000105007351) ≤ (693252183 / 1000000000) := by
  have h := checkLog_sound (w := (105007351 / 2000105007351)) (n := 12)
    (lo := (105001 / 1000000000)) (hi := (52501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000105007351 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000105007351 / 1000000000000) = 1/(500000000000 / 1000105007351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (693252181 / 1000000000) (693252183 / 1000000000) (Real.log (1000105007351 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1000105007351 / 500000000000) = -Real.log (500000000000 / 1000105007351) := by
    rw [show ((1000105007351 / 500000000000) : ℝ) = ((500000000000 / 1000105007351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (247836643 / 500000000) ≤ -Real.log (100000000000 / 164160313611) ∧
    -Real.log (100000000000 / 164160313611) ≤ (495673287 / 1000000000) := by
  have h := checkLog_sound (w := (64160313611 / 264160313611)) (n := 12)
    (lo := (247836643 / 500000000)) (hi := (495673287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164160313611 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164160313611 / 100000000000) = 1/(100000000000 / 164160313611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (247836643 / 500000000) (495673287 / 1000000000) (Real.log (164160313611 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (164160313611 / 100000000000) = -Real.log (100000000000 / 164160313611) := by
    rw [show ((164160313611 / 100000000000) : ℝ) = ((100000000000 / 164160313611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (496378973 / 1000000000) ≤ -Real.log (500000000000 / 821381001713) ∧
    -Real.log (500000000000 / 821381001713) ≤ (248189487 / 500000000) := by
  have h := checkLog_sound (w := (321381001713 / 1321381001713)) (n := 12)
    (lo := (496378973 / 1000000000)) (hi := (248189487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821381001713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821381001713 / 500000000000) = 1/(500000000000 / 821381001713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (496378973 / 1000000000) (248189487 / 500000000) (Real.log (821381001713 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (821381001713 / 500000000000) = -Real.log (500000000000 / 821381001713) := by
    rw [show ((821381001713 / 500000000000) : ℝ) = ((500000000000 / 821381001713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0360
