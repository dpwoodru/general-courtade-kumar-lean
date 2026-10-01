import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0335
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

theorem reflection_log_1_neg : (215693997 / 1000000000) ≤ -Real.log (2048 / 2541) ∧
    -Real.log (2048 / 2541) ≤ (107846999 / 500000000) := by
  have h := checkLog_sound (w := (493 / 4589)) (n := 12)
    (lo := (215693997 / 1000000000)) (hi := (107846999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2048) = 1/(2048 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (215693997 / 1000000000) (107846999 / 500000000) (Real.log (2541 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2541 / 2048) = -Real.log (2048 / 2541) := by
    rw [show ((2541 / 2048) : ℝ) = ((2048 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (275388161 / 1000000000) ≤ -Real.log (1555 / 2048) ∧
    -Real.log (1555 / 2048) ≤ (137694081 / 500000000) := by
  have h := checkLog_sound (w := (493 / 3603)) (n := 12)
    (lo := (275388161 / 1000000000)) (hi := (137694081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1555) = 1/(1555 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137694081 / 500000000) (-275388161 / 1000000000) (Real.log (1555 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (215457841 / 1000000000) ≤ -Real.log (5120 / 6351) ∧
    -Real.log (5120 / 6351) ≤ (107728921 / 500000000) := by
  have h := checkLog_sound (w := (1231 / 11471)) (n := 12)
    (lo := (215457841 / 1000000000)) (hi := (107728921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6351 / 5120) = 1/(5120 / 6351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (215457841 / 1000000000) (107728921 / 500000000) (Real.log (6351 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6351 / 5120) = -Real.log (5120 / 6351) := by
    rw [show ((6351 / 5120) : ℝ) = ((5120 / 6351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (275002383 / 1000000000) ≤ -Real.log (3889 / 5120) ∧
    -Real.log (3889 / 5120) ≤ (17187649 / 62500000) := by
  have h := checkLog_sound (w := (1231 / 9009)) (n := 12)
    (lo := (275002383 / 1000000000)) (hi := (17187649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3889) = 1/(3889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17187649 / 62500000) (-275002383 / 1000000000) (Real.log (3889 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (393018173 / 1000000000) ≤ -Real.log (1024 / 1517) ∧
    -Real.log (1024 / 1517) ≤ (196509087 / 500000000) := by
  have h := checkLog_sound (w := (493 / 2541)) (n := 12)
    (lo := (393018173 / 1000000000)) (hi := (196509087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517 / 1024) = 1/(1024 / 1517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (393018173 / 1000000000) (196509087 / 500000000) (Real.log (1517 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1517 / 1024) = -Real.log (1024 / 1517) := by
    rw [show ((1517 / 1024) : ℝ) = ((1024 / 1517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (82088723 / 125000000) ≤ -Real.log (531 / 1024) ∧
    -Real.log (531 / 1024) ≤ (131341957 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1555)) (n := 12)
    (lo := (82088723 / 125000000)) (hi := (131341957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 531) = 1/(531 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-131341957 / 200000000) (-82088723 / 125000000) (Real.log (531 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (196311289 / 500000000) ≤ -Real.log (2560 / 3791) ∧
    -Real.log (2560 / 3791) ≤ (392622579 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 6351)) (n := 12)
    (lo := (196311289 / 500000000)) (hi := (392622579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3791 / 2560) = 1/(2560 / 3791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (196311289 / 500000000) (392622579 / 1000000000) (Real.log (3791 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3791 / 2560) = -Real.log (2560 / 3791) := by
    rw [show ((3791 / 2560) : ℝ) = ((2560 / 3791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (327790239 / 500000000) ≤ -Real.log (1329 / 2560) ∧
    -Real.log (1329 / 2560) ≤ (655580479 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 3889)) (n := 12)
    (lo := (327790239 / 500000000)) (hi := (655580479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1329) = 1/(1329 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-655580479 / 1000000000) (-327790239 / 500000000) (Real.log (1329 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (576939 / 1953125) ≤ -Real.log (500000 / 671827) ∧
    -Real.log (500000 / 671827) ≤ (295392769 / 1000000000) := by
  have h := checkLog_sound (w := (171827 / 1171827)) (n := 12)
    (lo := (576939 / 1953125)) (hi := (295392769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671827 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671827 / 500000) = 1/(500000 / 671827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (576939 / 1953125) (295392769 / 1000000000) (Real.log (671827 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (671827 / 500000) = -Real.log (500000 / 671827) := by
    rw [show ((671827 / 500000) : ℝ) = ((500000 / 671827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42106719 / 100000000) ≤ -Real.log (328173 / 500000) ∧
    -Real.log (328173 / 500000) ≤ (421067191 / 1000000000) := by
  have h := checkLog_sound (w := (171827 / 828173)) (n := 12)
    (lo := (42106719 / 100000000)) (hi := (421067191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328173) = 1/(328173 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-421067191 / 1000000000) (-42106719 / 100000000) (Real.log (328173 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14785637 / 50000000) ≤ -Real.log (250000 / 336021) ∧
    -Real.log (250000 / 336021) ≤ (295712741 / 1000000000) := by
  have h := checkLog_sound (w := (86021 / 586021)) (n := 12)
    (lo := (14785637 / 50000000)) (hi := (295712741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336021 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336021 / 250000) = 1/(250000 / 336021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14785637 / 50000000) (295712741 / 1000000000) (Real.log (336021 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (336021 / 250000) = -Real.log (250000 / 336021) := by
    rw [show ((336021 / 250000) : ℝ) = ((250000 / 336021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (421722547 / 1000000000) ≤ -Real.log (163979 / 250000) ∧
    -Real.log (163979 / 250000) ≤ (105430637 / 250000000) := by
  have h := checkLog_sound (w := (86021 / 413979)) (n := 12)
    (lo := (421722547 / 1000000000)) (hi := (105430637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163979) = 1/(163979 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105430637 / 250000000) (-421722547 / 1000000000) (Real.log (163979 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224110283 / 1000000000) ≤ -Real.log (1000000 / 1251209) ∧
    -Real.log (1000000 / 1251209) ≤ (56027571 / 250000000) := by
  have h := checkLog_sound (w := (251209 / 2251209)) (n := 12)
    (lo := (224110283 / 1000000000)) (hi := (56027571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251209 / 1000000) = 1/(1000000 / 1251209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224110283 / 1000000000) (56027571 / 250000000) (Real.log (1251209 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1251209 / 1000000) = -Real.log (1000000 / 1251209) := by
    rw [show ((1251209 / 1000000) : ℝ) = ((1000000 / 1251209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (289295373 / 1000000000) ≤ -Real.log (748791 / 1000000) ∧
    -Real.log (748791 / 1000000) ≤ (144647687 / 500000000) := by
  have h := checkLog_sound (w := (251209 / 1748791)) (n := 12)
    (lo := (289295373 / 1000000000)) (hi := (144647687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748791) = 1/(748791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144647687 / 500000000) (-289295373 / 1000000000) (Real.log (748791 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (56094697 / 250000000) ≤ -Real.log (200000 / 250309) ∧
    -Real.log (200000 / 250309) ≤ (224378789 / 1000000000) := by
  have h := checkLog_sound (w := (50309 / 450309)) (n := 12)
    (lo := (56094697 / 250000000)) (hi := (224378789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250309 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250309 / 200000) = 1/(200000 / 250309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56094697 / 250000000) (224378789 / 1000000000) (Real.log (250309 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (250309 / 200000) = -Real.log (200000 / 250309) := by
    rw [show ((250309 / 200000) : ℝ) = ((200000 / 250309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (289744197 / 1000000000) ≤ -Real.log (149691 / 200000) ∧
    -Real.log (149691 / 200000) ≤ (144872099 / 500000000) := by
  have h := checkLog_sound (w := (50309 / 349691)) (n := 12)
    (lo := (289744197 / 1000000000)) (hi := (144872099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149691) = 1/(149691 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-144872099 / 500000000) (-289744197 / 1000000000) (Real.log (149691 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (716459957 / 1000000000) ≤ -Real.log (31250000000 / 63974165303) ∧
    -Real.log (31250000000 / 63974165303) ≤ (716459959 / 1000000000) := by
  have h := checkLog_sound (w := (1474165303 / 126474165303)) (n := 12)
    (lo := (23312777 / 1000000000)) (hi := (11656389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63974165303 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63974165303 / 62500000000) = 1/(31250000000 / 63974165303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (716459957 / 1000000000) (716459959 / 1000000000) (Real.log (63974165303 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (63974165303 / 31250000000) = -Real.log (31250000000 / 63974165303) := by
    rw [show ((63974165303 / 31250000000) : ℝ) = ((31250000000 / 63974165303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358717643 / 500000000) ≤ -Real.log (500000000000 / 1024585465213) ∧
    -Real.log (500000000000 / 1024585465213) ≤ (89679411 / 125000000) := by
  have h := checkLog_sound (w := (24585465213 / 2024585465213)) (n := 12)
    (lo := (12144053 / 500000000)) (hi := (24288107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024585465213 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024585465213 / 1000000000000) = 1/(500000000000 / 1024585465213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358717643 / 500000000) (89679411 / 125000000) (Real.log (1024585465213 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1024585465213 / 500000000000) = -Real.log (500000000000 / 1024585465213) := by
    rw [show ((1024585465213 / 500000000000) : ℝ) = ((500000000000 / 1024585465213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (64175707 / 125000000) ≤ -Real.log (250000000000 / 417743068493) ∧
    -Real.log (250000000000 / 417743068493) ≤ (513405657 / 1000000000) := by
  have h := checkLog_sound (w := (167743068493 / 667743068493)) (n := 12)
    (lo := (64175707 / 125000000)) (hi := (513405657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417743068493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417743068493 / 250000000000) = 1/(250000000000 / 417743068493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (64175707 / 125000000) (513405657 / 1000000000) (Real.log (417743068493 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (417743068493 / 250000000000) = -Real.log (250000000000 / 417743068493) := by
    rw [show ((417743068493 / 250000000000) : ℝ) = ((250000000000 / 417743068493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (102824597 / 200000000) ≤ -Real.log (250000000000 / 418042834907) ∧
    -Real.log (250000000000 / 418042834907) ≤ (257061493 / 500000000) := by
  have h := checkLog_sound (w := (168042834907 / 668042834907)) (n := 12)
    (lo := (102824597 / 200000000)) (hi := (257061493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418042834907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418042834907 / 250000000000) = 1/(250000000000 / 418042834907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (102824597 / 200000000) (257061493 / 500000000) (Real.log (418042834907 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (418042834907 / 250000000000) = -Real.log (250000000000 / 418042834907) := by
    rw [show ((418042834907 / 250000000000) : ℝ) = ((250000000000 / 418042834907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0335
