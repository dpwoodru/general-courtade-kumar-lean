import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0053
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

theorem reflection_log_1_neg : (93025551 / 250000000) ≤ -Real.log (1280 / 1857) ∧
    -Real.log (1280 / 1857) ≤ (74420441 / 200000000) := by
  have h := checkLog_sound (w := (577 / 3137)) (n := 12)
    (lo := (93025551 / 250000000)) (hi := (74420441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1280) = 1/(1280 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (93025551 / 250000000) (74420441 / 200000000) (Real.log (1857 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1857 / 1280) = -Real.log (1280 / 1857) := by
    rw [show ((1857 / 1280) : ℝ) = ((1280 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (119851693 / 200000000) ≤ -Real.log (703 / 1280) ∧
    -Real.log (703 / 1280) ≤ (299629233 / 500000000) := by
  have h := checkLog_sound (w := (577 / 1983)) (n := 12)
    (lo := (119851693 / 200000000)) (hi := (299629233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 703) = 1/(703 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299629233 / 500000000) (-119851693 / 200000000) (Real.log (703 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (371294123 / 1000000000) ≤ -Real.log (2560 / 3711) ∧
    -Real.log (2560 / 3711) ≤ (92823531 / 250000000) := by
  have h := checkLog_sound (w := (1151 / 6271)) (n := 12)
    (lo := (371294123 / 1000000000)) (hi := (92823531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3711 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3711 / 2560) = 1/(2560 / 3711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (371294123 / 1000000000) (92823531 / 250000000) (Real.log (3711 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3711 / 2560) = -Real.log (2560 / 3711) := by
    rw [show ((3711 / 2560) : ℝ) = ((2560 / 3711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (23885081 / 40000000) ≤ -Real.log (1409 / 2560) ∧
    -Real.log (1409 / 2560) ≤ (298563513 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3969)) (n := 12)
    (lo := (23885081 / 40000000)) (hi := (298563513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1409) = 1/(1409 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-298563513 / 500000000) (-23885081 / 40000000) (Real.log (1409 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (160668979 / 250000000) ≤ -Real.log (640 / 1217) ∧
    -Real.log (640 / 1217) ≤ (642675917 / 1000000000) := by
  have h := checkLog_sound (w := (577 / 1857)) (n := 12)
    (lo := (160668979 / 250000000)) (hi := (642675917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217 / 640) = 1/(640 / 1217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (160668979 / 250000000) (642675917 / 1000000000) (Real.log (1217 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1217 / 640) = -Real.log (640 / 1217) := by
    rw [show ((1217 / 640) : ℝ) = ((640 / 1217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (289791681 / 125000000) ≤ -Real.log (63 / 640) ∧
    -Real.log (63 / 640) ≤ (579583363 / 250000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 63) = 1/(63 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-579583363 / 250000000) (-289791681 / 125000000) (Real.log (63 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (641442617 / 1000000000) ≤ -Real.log (1280 / 2431) ∧
    -Real.log (1280 / 2431) ≤ (320721309 / 500000000) := by
  have h := checkLog_sound (w := (1151 / 3711)) (n := 12)
    (lo := (641442617 / 1000000000)) (hi := (320721309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2431 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2431 / 1280) = 1/(1280 / 2431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (641442617 / 1000000000) (320721309 / 500000000) (Real.log (2431 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2431 / 1280) = -Real.log (1280 / 2431) := by
    rw [show ((2431 / 1280) : ℝ) = ((1280 / 2431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45896059 / 20000000) ≤ -Real.log (129 / 1280) ∧
    -Real.log (129 / 1280) ≤ (1147401477 / 500000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 129) = 1/(129 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1147401477 / 500000000) (-45896059 / 20000000) (Real.log (129 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32118843 / 62500000) ≤ -Real.log (1000000 / 1671801) ∧
    -Real.log (1000000 / 1671801) ≤ (513901489 / 1000000000) := by
  have h := checkLog_sound (w := (671801 / 2671801)) (n := 12)
    (lo := (32118843 / 62500000)) (hi := (513901489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671801 / 1000000) = 1/(1000000 / 1671801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32118843 / 62500000) (513901489 / 1000000000) (Real.log (1671801 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1671801 / 1000000) = -Real.log (1000000 / 1671801) := by
    rw [show ((1671801 / 1000000) : ℝ) = ((1000000 / 1671801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (557067573 / 500000000) ≤ -Real.log (328199 / 1000000) ∧
    -Real.log (328199 / 1000000) ≤ (278533787 / 250000000) := by
  have h := checkLog_sound (w := (171801 / 828199)) (n := 12)
    (lo := (210493983 / 500000000)) (hi := (420987967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 328199) = 1/(328199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-278533787 / 250000000) (-557067573 / 500000000) (Real.log (328199 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (515167583 / 1000000000) ≤ -Real.log (1000000 / 1673919) ∧
    -Real.log (1000000 / 1673919) ≤ (16098987 / 31250000) := by
  have h := checkLog_sound (w := (673919 / 2673919)) (n := 12)
    (lo := (515167583 / 1000000000)) (hi := (16098987 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1673919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1673919 / 1000000) = 1/(1000000 / 1673919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (515167583 / 1000000000) (16098987 / 31250000) (Real.log (1673919 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1673919 / 1000000) = -Real.log (1000000 / 1673919) := by
    rw [show ((1673919 / 1000000) : ℝ) = ((1000000 / 1673919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1120609461 / 1000000000) ≤ -Real.log (326081 / 1000000) ∧
    -Real.log (326081 / 1000000) ≤ (1120609463 / 1000000000) := by
  have h := checkLog_sound (w := (173919 / 826081)) (n := 12)
    (lo := (427462281 / 1000000000)) (hi := (213731141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 326081) = 1/(326081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1120609463 / 1000000000) (-1120609461 / 1000000000) (Real.log (326081 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (433050443 / 1000000000) ≤ -Real.log (500000 / 770977) ∧
    -Real.log (500000 / 770977) ≤ (108262611 / 250000000) := by
  have h := checkLog_sound (w := (270977 / 1270977)) (n := 12)
    (lo := (433050443 / 1000000000)) (hi := (108262611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770977 / 500000) = 1/(500000 / 770977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (433050443 / 1000000000) (108262611 / 250000000) (Real.log (770977 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (770977 / 500000) = -Real.log (500000 / 770977) := by
    rw [show ((770977 / 500000) : ℝ) = ((500000 / 770977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (390392831 / 500000000) ≤ -Real.log (229023 / 500000) ∧
    -Real.log (229023 / 500000) ≤ (1524972 / 1953125) := by
  have h := checkLog_sound (w := (20977 / 479023)) (n := 12)
    (lo := (43819241 / 500000000)) (hi := (87638483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 229023) = 1/(229023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1524972 / 1953125) (-390392831 / 500000000) (Real.log (229023 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (434463883 / 1000000000) ≤ -Real.log (200000 / 308827) ∧
    -Real.log (200000 / 308827) ≤ (108615971 / 250000000) := by
  have h := checkLog_sound (w := (108827 / 508827)) (n := 12)
    (lo := (434463883 / 1000000000)) (hi := (108615971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308827 / 200000) = 1/(200000 / 308827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (434463883 / 1000000000) (108615971 / 250000000) (Real.log (308827 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308827 / 200000) = -Real.log (200000 / 308827) := by
    rw [show ((308827 / 200000) : ℝ) = ((200000 / 308827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (157111713 / 200000000) ≤ -Real.log (91173 / 200000) ∧
    -Real.log (91173 / 200000) ≤ (785558567 / 1000000000) := by
  have h := checkLog_sound (w := (8827 / 191173)) (n := 12)
    (lo := (18482277 / 200000000)) (hi := (46205693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 91173) = 1/(91173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-785558567 / 1000000000) (-157111713 / 200000000) (Real.log (91173 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (814018317 / 500000000) ≤ -Real.log (500000000000 / 2546931891931) ∧
    -Real.log (500000000000 / 2546931891931) ≤ (1628036637 / 1000000000) := by
  have h := checkLog_sound (w := (546931891931 / 4546931891931)) (n := 12)
    (lo := (120871137 / 500000000)) (hi := (9669691 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2546931891931 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2546931891931 / 2000000000000) = 1/(500000000000 / 2546931891931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (814018317 / 500000000) (1628036637 / 1000000000) (Real.log (2546931891931 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2546931891931 / 500000000000) = -Real.log (500000000000 / 2546931891931) := by
    rw [show ((2546931891931 / 500000000000) : ℝ) = ((500000000000 / 2546931891931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (408944261 / 250000000) ≤ -Real.log (125000000000 / 641680671367) ∧
    -Real.log (125000000000 / 641680671367) ≤ (1635777047 / 1000000000) := by
  have h := checkLog_sound (w := (141680671367 / 1141680671367)) (n := 12)
    (lo := (62370671 / 250000000)) (hi := (49896537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641680671367 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(641680671367 / 500000000000) = 1/(125000000000 / 641680671367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (408944261 / 250000000) (1635777047 / 1000000000) (Real.log (641680671367 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (641680671367 / 125000000000) = -Real.log (125000000000 / 641680671367) := by
    rw [show ((641680671367 / 125000000000) : ℝ) = ((125000000000 / 641680671367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (242767221 / 200000000) ≤ -Real.log (62500000000 / 210398355187) ∧
    -Real.log (62500000000 / 210398355187) ≤ (1213836107 / 1000000000) := by
  have h := checkLog_sound (w := (85398355187 / 335398355187)) (n := 12)
    (lo := (20827557 / 40000000)) (hi := (260344463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210398355187 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210398355187 / 125000000000) = 1/(62500000000 / 210398355187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (242767221 / 200000000) (1213836107 / 1000000000) (Real.log (210398355187 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (210398355187 / 62500000000) = -Real.log (62500000000 / 210398355187) := by
    rw [show ((210398355187 / 62500000000) : ℝ) = ((62500000000 / 210398355187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (76251403 / 62500000) ≤ -Real.log (250000000000 / 846815943317) ∧
    -Real.log (250000000000 / 846815943317) ≤ (24400449 / 20000000) := by
  have h := checkLog_sound (w := (346815943317 / 1346815943317)) (n := 12)
    (lo := (131718817 / 250000000)) (hi := (526875269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846815943317 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(846815943317 / 500000000000) = 1/(250000000000 / 846815943317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (76251403 / 62500000) (24400449 / 20000000) (Real.log (846815943317 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (846815943317 / 250000000000) = -Real.log (250000000000 / 846815943317) := by
    rw [show ((846815943317 / 250000000000) : ℝ) = ((250000000000 / 846815943317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0053
