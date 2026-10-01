import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6528_neg : (9462267 / 100000000) ≤ -Real.log (250000 / 274811) ∧
    -Real.log (250000 / 274811) ≤ (94622671 / 1000000000) := by
  have h := checkLog_sound (w := (24811 / 524811)) (n := 12)
    (lo := (9462267 / 100000000)) (hi := (94622671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274811 / 250000) = 1/(250000 / 274811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6528 : Bounds (9462267 / 100000000) (94622671 / 1000000000) (Real.log (274811 / 250000)) := by
  have h := reflection_log_6528_neg
  have he : Real.log (274811 / 250000) = -Real.log (250000 / 274811) := by
    rw [show ((274811 / 250000) : ℝ) = ((250000 / 274811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6529_neg : (26130217 / 250000000) ≤ -Real.log (225189 / 250000) ∧
    -Real.log (225189 / 250000) ≤ (104520869 / 1000000000) := by
  have h := checkLog_sound (w := (24811 / 475189)) (n := 12)
    (lo := (26130217 / 250000000)) (hi := (104520869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225189) = 1/(225189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6529 : Bounds (-104520869 / 1000000000) (-26130217 / 250000000) (Real.log (225189 / 250000)) := by
  have h := reflection_log_6529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6530_neg : (9898197 / 1000000000) ≤ -Real.log (61884414279 / 62500000000) ∧
    -Real.log (61884414279 / 62500000000) ≤ (4949099 / 500000000) := by
  have h := checkLog_sound (w := (615585721 / 124384414279)) (n := 12)
    (lo := (9898197 / 1000000000)) (hi := (4949099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61884414279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61884414279) = 1/(61884414279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6530 : Bounds (-4949099 / 500000000) (-9898197 / 1000000000) (Real.log (61884414279 / 62500000000)) := by
  have h := reflection_log_6530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6531_neg : (4924373 / 500000000) ≤ -Real.log (990199593991 / 1000000000000) ∧
    -Real.log (990199593991 / 1000000000000) ≤ (9848747 / 1000000000) := by
  have h := checkLog_sound (w := (9800406009 / 1990199593991)) (n := 12)
    (lo := (4924373 / 500000000)) (hi := (9848747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990199593991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990199593991) = 1/(990199593991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6531 : Bounds (-9848747 / 1000000000) (-4924373 / 500000000) (Real.log (990199593991 / 1000000000000)) := by
  have h := reflection_log_6531_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6532_neg : (198644637 / 1000000000) ≤ -Real.log (250000000000 / 304937108977) ∧
    -Real.log (250000000000 / 304937108977) ≤ (99322319 / 500000000) := by
  have h := checkLog_sound (w := (54937108977 / 554937108977)) (n := 12)
    (lo := (198644637 / 1000000000)) (hi := (99322319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304937108977 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304937108977 / 250000000000) = 1/(250000000000 / 304937108977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6532 : Bounds (198644637 / 1000000000) (99322319 / 500000000) (Real.log (304937108977 / 250000000000)) := by
  have h := reflection_log_6532_neg
  have he : Real.log (304937108977 / 250000000000) = -Real.log (250000000000 / 304937108977) := by
    rw [show ((304937108977 / 250000000000) : ℝ) = ((250000000000 / 304937108977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6533_neg : (199143539 / 1000000000) ≤ -Real.log (3125000000 / 3813616007) ∧
    -Real.log (3125000000 / 3813616007) ≤ (9957177 / 50000000) := by
  have h := checkLog_sound (w := (688616007 / 6938616007)) (n := 12)
    (lo := (199143539 / 1000000000)) (hi := (9957177 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813616007 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813616007 / 3125000000) = 1/(3125000000 / 3813616007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6533 : Bounds (199143539 / 1000000000) (9957177 / 50000000) (Real.log (3813616007 / 3125000000)) := by
  have h := reflection_log_6533_neg
  have he : Real.log (3813616007 / 3125000000) = -Real.log (3125000000 / 3813616007) := by
    rw [show ((3813616007 / 3125000000) : ℝ) = ((3125000000 / 3813616007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6534_neg : (199401429 / 500000000) ≤ -Real.log (250000000000 / 372509960159) ∧
    -Real.log (250000000000 / 372509960159) ≤ (398802859 / 1000000000) := by
  have h := checkLog_sound (w := (122509960159 / 622509960159)) (n := 12)
    (lo := (199401429 / 500000000)) (hi := (398802859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372509960159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372509960159 / 250000000000) = 1/(250000000000 / 372509960159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6534 : Bounds (199401429 / 500000000) (398802859 / 1000000000) (Real.log (372509960159 / 250000000000)) := by
  have h := reflection_log_6534_neg
  have he : Real.log (372509960159 / 250000000000) = -Real.log (250000000000 / 372509960159) := by
    rw [show ((372509960159 / 250000000000) : ℝ) = ((250000000000 / 372509960159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6535_neg : (9975273 / 25000000) ≤ -Real.log (500000000000 / 745174947081) ∧
    -Real.log (500000000000 / 745174947081) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (245174947081 / 1245174947081)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745174947081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745174947081 / 500000000000) = 1/(500000000000 / 745174947081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6535 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (745174947081 / 500000000000)) := by
  have h := reflection_log_6535_neg
  have he : Real.log (745174947081 / 500000000000) = -Real.log (500000000000 / 745174947081) := by
    rw [show ((745174947081 / 500000000000) : ℝ) = ((500000000000 / 745174947081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6536_neg : (89909213 / 500000000) ≤ -Real.log (1000 / 1197) ∧
    -Real.log (1000 / 1197) ≤ (179818427 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2197)) (n := 12)
    (lo := (89909213 / 500000000)) (hi := (179818427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197 / 1000) = 1/(1000 / 1197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6536 : Bounds (89909213 / 500000000) (179818427 / 1000000000) (Real.log (1197 / 1000)) := by
  have h := reflection_log_6536_neg
  have he : Real.log (1197 / 1000) = -Real.log (1000 / 1197) := by
    rw [show ((1197 / 1000) : ℝ) = ((1000 / 1197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6537_neg : (43880113 / 200000000) ≤ -Real.log (803 / 1000) ∧
    -Real.log (803 / 1000) ≤ (109700283 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1803)) (n := 12)
    (lo := (43880113 / 200000000)) (hi := (109700283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 803) = 1/(803 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6537 : Bounds (-109700283 / 500000000) (-43880113 / 200000000) (Real.log (803 / 1000)) := by
  have h := reflection_log_6537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6538_neg : (9849 / 50000000) ≤ -Real.log (1000000 / 1000197) ∧
    -Real.log (1000000 / 1000197) ≤ (196981 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2000197)) (n := 12)
    (lo := (9849 / 50000000)) (hi := (196981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000197 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000197 / 1000000) = 1/(1000000 / 1000197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6538 : Bounds (9849 / 50000000) (196981 / 1000000000) (Real.log (1000197 / 1000000)) := by
  have h := reflection_log_6538_neg
  have he : Real.log (1000197 / 1000000) = -Real.log (1000000 / 1000197) := by
    rw [show ((1000197 / 1000000) : ℝ) = ((1000000 / 1000197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6539_neg : (197019 / 1000000000) ≤ -Real.log (999803 / 1000000) ∧
    -Real.log (999803 / 1000000) ≤ (9851 / 50000000) := by
  have h := checkLog_sound (w := (197 / 1999803)) (n := 12)
    (lo := (197019 / 1000000000)) (hi := (9851 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999803) = 1/(999803 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6539 : Bounds (-9851 / 50000000) (-197019 / 1000000000) (Real.log (999803 / 1000000)) := by
  have h := reflection_log_6539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6540_neg : (1888887 / 20000000) ≤ -Real.log (125000 / 137381) ∧
    -Real.log (125000 / 137381) ≤ (94444351 / 1000000000) := by
  have h := checkLog_sound (w := (12381 / 262381)) (n := 12)
    (lo := (1888887 / 20000000)) (hi := (94444351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137381 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137381 / 125000) = 1/(125000 / 137381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6540 : Bounds (1888887 / 20000000) (94444351 / 1000000000) (Real.log (137381 / 125000)) := by
  have h := reflection_log_6540_neg
  have he : Real.log (137381 / 125000) = -Real.log (125000 / 137381) := by
    rw [show ((137381 / 125000) : ℝ) = ((125000 / 137381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6541_neg : (1629739 / 15625000) ≤ -Real.log (112619 / 125000) ∧
    -Real.log (112619 / 125000) ≤ (104303297 / 1000000000) := by
  have h := checkLog_sound (w := (12381 / 237619)) (n := 12)
    (lo := (1629739 / 15625000)) (hi := (104303297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112619) = 1/(112619 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6541 : Bounds (-104303297 / 1000000000) (-1629739 / 15625000) (Real.log (112619 / 125000)) := by
  have h := reflection_log_6541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6542_neg : (47334987 / 500000000) ≤ -Real.log (31250 / 34353) ∧
    -Real.log (31250 / 34353) ≤ (3786799 / 40000000) := by
  have h := checkLog_sound (w := (3103 / 65603)) (n := 12)
    (lo := (47334987 / 500000000)) (hi := (3786799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34353 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34353 / 31250) = 1/(31250 / 34353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6542 : Bounds (47334987 / 500000000) (3786799 / 40000000) (Real.log (34353 / 31250)) := by
  have h := reflection_log_6542_neg
  have he : Real.log (34353 / 31250) = -Real.log (31250 / 34353) := by
    rw [show ((34353 / 31250) : ℝ) = ((31250 / 34353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6543_neg : (104578599 / 1000000000) ≤ -Real.log (28147 / 31250) ∧
    -Real.log (28147 / 31250) ≤ (522893 / 5000000) := by
  have h := checkLog_sound (w := (3103 / 59397)) (n := 12)
    (lo := (104578599 / 1000000000)) (hi := (522893 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28147) = 1/(28147 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6543 : Bounds (-522893 / 5000000) (-104578599 / 1000000000) (Real.log (28147 / 31250)) := by
  have h := reflection_log_6543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6544_neg : (619289 / 62500000) ≤ -Real.log (966933891 / 976562500) ∧
    -Real.log (966933891 / 976562500) ≤ (79269 / 8000000) := by
  have h := checkLog_sound (w := (9628609 / 1943496391)) (n := 12)
    (lo := (619289 / 62500000)) (hi := (79269 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 966933891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 966933891) = 1/(966933891 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6544 : Bounds (-79269 / 8000000) (-619289 / 62500000) (Real.log (966933891 / 976562500)) := by
  have h := reflection_log_6544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6545_neg : (4929473 / 500000000) ≤ -Real.log (15471710839 / 15625000000) ∧
    -Real.log (15471710839 / 15625000000) ≤ (9858947 / 1000000000) := by
  have h := checkLog_sound (w := (153289161 / 31096710839)) (n := 12)
    (lo := (4929473 / 500000000)) (hi := (9858947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15471710839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15471710839) = 1/(15471710839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6545 : Bounds (-9858947 / 1000000000) (-4929473 / 500000000) (Real.log (15471710839 / 15625000000)) := by
  have h := reflection_log_6545_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6546_neg : (198747647 / 1000000000) ≤ -Real.log (50000000000 / 60993704437) ∧
    -Real.log (50000000000 / 60993704437) ≤ (388179 / 1953125) := by
  have h := checkLog_sound (w := (10993704437 / 110993704437)) (n := 12)
    (lo := (198747647 / 1000000000)) (hi := (388179 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60993704437 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60993704437 / 50000000000) = 1/(50000000000 / 60993704437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6546 : Bounds (198747647 / 1000000000) (388179 / 1953125) (Real.log (60993704437 / 50000000000)) := by
  have h := reflection_log_6546_neg
  have he : Real.log (60993704437 / 50000000000) = -Real.log (50000000000 / 60993704437) := by
    rw [show ((60993704437 / 50000000000) : ℝ) = ((50000000000 / 60993704437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6547_neg : (99624287 / 500000000) ≤ -Real.log (100000000000 / 122048530927) ∧
    -Real.log (100000000000 / 122048530927) ≤ (7969943 / 40000000) := by
  have h := checkLog_sound (w := (22048530927 / 222048530927)) (n := 12)
    (lo := (99624287 / 500000000)) (hi := (7969943 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122048530927 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122048530927 / 100000000000) = 1/(100000000000 / 122048530927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6547 : Bounds (99624287 / 500000000) (7969943 / 40000000) (Real.log (122048530927 / 100000000000)) := by
  have h := reflection_log_6547_neg
  have he : Real.log (122048530927 / 100000000000) = -Real.log (100000000000 / 122048530927) := by
    rw [show ((122048530927 / 100000000000) : ℝ) = ((100000000000 / 122048530927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6548_neg : (9975273 / 25000000) ≤ -Real.log (12500000000 / 18629373677) ∧
    -Real.log (12500000000 / 18629373677) ≤ (399010921 / 1000000000) := by
  have h := checkLog_sound (w := (6129373677 / 31129373677)) (n := 12)
    (lo := (9975273 / 25000000)) (hi := (399010921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18629373677 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18629373677 / 12500000000) = 1/(12500000000 / 18629373677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6548 : Bounds (9975273 / 25000000) (399010921 / 1000000000) (Real.log (18629373677 / 12500000000)) := by
  have h := reflection_log_6548_neg
  have he : Real.log (18629373677 / 12500000000) = -Real.log (12500000000 / 18629373677) := by
    rw [show ((18629373677 / 12500000000) : ℝ) = ((12500000000 / 18629373677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6549_neg : (399218991 / 1000000000) ≤ -Real.log (250000000000 / 372665006227) ∧
    -Real.log (250000000000 / 372665006227) ≤ (24951187 / 62500000) := by
  have h := checkLog_sound (w := (122665006227 / 622665006227)) (n := 12)
    (lo := (399218991 / 1000000000)) (hi := (24951187 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372665006227 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372665006227 / 250000000000) = 1/(250000000000 / 372665006227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6549 : Bounds (399218991 / 1000000000) (24951187 / 62500000) (Real.log (372665006227 / 250000000000)) := by
  have h := reflection_log_6549_neg
  have he : Real.log (372665006227 / 250000000000) = -Real.log (250000000000 / 372665006227) := by
    rw [show ((372665006227 / 250000000000) : ℝ) = ((250000000000 / 372665006227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6550_neg : (35980393 / 200000000) ≤ -Real.log (10000 / 11971) ∧
    -Real.log (10000 / 11971) ≤ (89950983 / 500000000) := by
  have h := checkLog_sound (w := (1971 / 21971)) (n := 12)
    (lo := (35980393 / 200000000)) (hi := (89950983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11971 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11971 / 10000) = 1/(10000 / 11971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6550 : Bounds (35980393 / 200000000) (89950983 / 500000000) (Real.log (11971 / 10000)) := by
  have h := reflection_log_6550_neg
  have he : Real.log (11971 / 10000) = -Real.log (10000 / 11971) := by
    rw [show ((11971 / 10000) : ℝ) = ((10000 / 11971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6551_neg : (43905021 / 200000000) ≤ -Real.log (8029 / 10000) ∧
    -Real.log (8029 / 10000) ≤ (109762553 / 500000000) := by
  have h := checkLog_sound (w := (1971 / 18029)) (n := 12)
    (lo := (43905021 / 200000000)) (hi := (109762553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8029) = 1/(8029 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6551 : Bounds (-109762553 / 500000000) (-43905021 / 200000000) (Real.log (8029 / 10000)) := by
  have h := reflection_log_6551_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6552_neg : (4927 / 25000000) ≤ -Real.log (10000000 / 10001971) ∧
    -Real.log (10000000 / 10001971) ≤ (197081 / 1000000000) := by
  have h := checkLog_sound (w := (1971 / 20001971)) (n := 12)
    (lo := (4927 / 25000000)) (hi := (197081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001971 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001971 / 10000000) = 1/(10000000 / 10001971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6552 : Bounds (4927 / 25000000) (197081 / 1000000000) (Real.log (10001971 / 10000000)) := by
  have h := reflection_log_6552_neg
  have he : Real.log (10001971 / 10000000) = -Real.log (10000000 / 10001971) := by
    rw [show ((10001971 / 10000000) : ℝ) = ((10000000 / 10001971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6553_neg : (197119 / 1000000000) ≤ -Real.log (9998029 / 10000000) ∧
    -Real.log (9998029 / 10000000) ≤ (77 / 390625) := by
  have h := checkLog_sound (w := (1971 / 19998029)) (n := 12)
    (lo := (197119 / 1000000000)) (hi := (77 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998029) = 1/(9998029 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6553 : Bounds (-77 / 390625) (-197119 / 1000000000) (Real.log (9998029 / 10000000)) := by
  have h := reflection_log_6553_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6554_neg : (94490753 / 1000000000) ≤ -Real.log (1000000 / 1099099) ∧
    -Real.log (1000000 / 1099099) ≤ (47245377 / 500000000) := by
  have h := checkLog_sound (w := (99099 / 2099099)) (n := 12)
    (lo := (94490753 / 1000000000)) (hi := (47245377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099099 / 1000000) = 1/(1000000 / 1099099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6554 : Bounds (94490753 / 1000000000) (47245377 / 500000000) (Real.log (1099099 / 1000000)) := by
  have h := reflection_log_6554_neg
  have he : Real.log (1099099 / 1000000) = -Real.log (1000000 / 1099099) := by
    rw [show ((1099099 / 1000000) : ℝ) = ((1000000 / 1099099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6555_neg : (20871981 / 200000000) ≤ -Real.log (900901 / 1000000) ∧
    -Real.log (900901 / 1000000) ≤ (52179953 / 500000000) := by
  have h := checkLog_sound (w := (99099 / 1900901)) (n := 12)
    (lo := (20871981 / 200000000)) (hi := (52179953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900901) = 1/(900901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6555 : Bounds (-52179953 / 500000000) (-20871981 / 200000000) (Real.log (900901 / 1000000)) := by
  have h := reflection_log_6555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6556_neg : (94716367 / 1000000000) ≤ -Real.log (1000000 / 1099347) ∧
    -Real.log (1000000 / 1099347) ≤ (5919773 / 62500000) := by
  have h := checkLog_sound (w := (99347 / 2099347)) (n := 12)
    (lo := (94716367 / 1000000000)) (hi := (5919773 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099347 / 1000000) = 1/(1000000 / 1099347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6556 : Bounds (94716367 / 1000000000) (5919773 / 62500000) (Real.log (1099347 / 1000000)) := by
  have h := reflection_log_6556_neg
  have he : Real.log (1099347 / 1000000) = -Real.log (1000000 / 1099347) := by
    rw [show ((1099347 / 1000000) : ℝ) = ((1000000 / 1099347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6557_neg : (104635223 / 1000000000) ≤ -Real.log (900653 / 1000000) ∧
    -Real.log (900653 / 1000000) ≤ (13079403 / 125000000) := by
  have h := checkLog_sound (w := (99347 / 1900653)) (n := 12)
    (lo := (104635223 / 1000000000)) (hi := (13079403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900653) = 1/(900653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6557 : Bounds (-13079403 / 125000000) (-104635223 / 1000000000) (Real.log (900653 / 1000000)) := by
  have h := reflection_log_6557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6558_neg : (1239857 / 125000000) ≤ -Real.log (990130173591 / 1000000000000) ∧
    -Real.log (990130173591 / 1000000000000) ≤ (9918857 / 1000000000) := by
  have h := checkLog_sound (w := (9869826409 / 1990130173591)) (n := 12)
    (lo := (1239857 / 125000000)) (hi := (9918857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990130173591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990130173591) = 1/(990130173591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6558 : Bounds (-9918857 / 1000000000) (-1239857 / 125000000) (Real.log (990130173591 / 1000000000000)) := by
  have h := reflection_log_6558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6559_neg : (308411 / 31250000) ≤ -Real.log (990179388199 / 1000000000000) ∧
    -Real.log (990179388199 / 1000000000000) ≤ (9869153 / 1000000000) := by
  have h := checkLog_sound (w := (9820611801 / 1990179388199)) (n := 12)
    (lo := (308411 / 31250000)) (hi := (9869153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990179388199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990179388199) = 1/(990179388199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6559 : Bounds (-9869153 / 1000000000) (-308411 / 31250000) (Real.log (990179388199 / 1000000000000)) := by
  have h := reflection_log_6559_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6560_neg : (99425329 / 500000000) ≤ -Real.log (5000000000 / 6099998779) ∧
    -Real.log (5000000000 / 6099998779) ≤ (198850659 / 1000000000) := by
  have h := checkLog_sound (w := (1099998779 / 11099998779)) (n := 12)
    (lo := (99425329 / 500000000)) (hi := (198850659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6099998779 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6099998779 / 5000000000) = 1/(5000000000 / 6099998779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6560 : Bounds (99425329 / 500000000) (198850659 / 1000000000) (Real.log (6099998779 / 5000000000)) := by
  have h := reflection_log_6560_neg
  have he : Real.log (6099998779 / 5000000000) = -Real.log (5000000000 / 6099998779) := by
    rw [show ((6099998779 / 5000000000) : ℝ) = ((5000000000 / 6099998779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6561_neg : (19935159 / 100000000) ≤ -Real.log (500000000000 / 610305522771) ∧
    -Real.log (500000000000 / 610305522771) ≤ (199351591 / 1000000000) := by
  have h := checkLog_sound (w := (110305522771 / 1110305522771)) (n := 12)
    (lo := (19935159 / 100000000)) (hi := (199351591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610305522771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610305522771 / 500000000000) = 1/(500000000000 / 610305522771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6561 : Bounds (19935159 / 100000000) (199351591 / 1000000000) (Real.log (610305522771 / 500000000000)) := by
  have h := reflection_log_6561_neg
  have he : Real.log (610305522771 / 500000000000) = -Real.log (500000000000 / 610305522771) := by
    rw [show ((610305522771 / 500000000000) : ℝ) = ((500000000000 / 610305522771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6562_neg : (399218991 / 1000000000) ≤ -Real.log (500000000000 / 745330012453) ∧
    -Real.log (500000000000 / 745330012453) ≤ (24951187 / 62500000) := by
  have h := checkLog_sound (w := (245330012453 / 1245330012453)) (n := 12)
    (lo := (399218991 / 1000000000)) (hi := (24951187 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745330012453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745330012453 / 500000000000) = 1/(500000000000 / 745330012453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6562 : Bounds (399218991 / 1000000000) (24951187 / 62500000) (Real.log (745330012453 / 500000000000)) := by
  have h := reflection_log_6562_neg
  have he : Real.log (745330012453 / 500000000000) = -Real.log (500000000000 / 745330012453) := by
    rw [show ((745330012453 / 500000000000) : ℝ) = ((500000000000 / 745330012453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6563_neg : (399427071 / 1000000000) ≤ -Real.log (500000000000 / 745485116453) ∧
    -Real.log (500000000000 / 745485116453) ≤ (780131 / 1953125) := by
  have h := checkLog_sound (w := (245485116453 / 1245485116453)) (n := 12)
    (lo := (399427071 / 1000000000)) (hi := (780131 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745485116453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745485116453 / 500000000000) = 1/(500000000000 / 745485116453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6563 : Bounds (399427071 / 1000000000) (780131 / 1953125) (Real.log (745485116453 / 500000000000)) := by
  have h := reflection_log_6563_neg
  have he : Real.log (745485116453 / 500000000000) = -Real.log (500000000000 / 745485116453) := by
    rw [show ((745485116453 / 500000000000) : ℝ) = ((500000000000 / 745485116453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6564_neg : (22498187 / 125000000) ≤ -Real.log (2500 / 2993) ∧
    -Real.log (2500 / 2993) ≤ (179985497 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 5493)) (n := 12)
    (lo := (22498187 / 125000000)) (hi := (179985497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2993 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2993 / 2500) = 1/(2500 / 2993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6564 : Bounds (22498187 / 125000000) (179985497 / 1000000000) (Real.log (2993 / 2500)) := by
  have h := reflection_log_6564_neg
  have he : Real.log (2993 / 2500) = -Real.log (2500 / 2993) := by
    rw [show ((2993 / 2500) : ℝ) = ((2500 / 2993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6565_neg : (109824831 / 500000000) ≤ -Real.log (2007 / 2500) ∧
    -Real.log (2007 / 2500) ≤ (219649663 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 4507)) (n := 12)
    (lo := (109824831 / 500000000)) (hi := (219649663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2007) = 1/(2007 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6565 : Bounds (-219649663 / 1000000000) (-109824831 / 500000000) (Real.log (2007 / 2500)) := by
  have h := reflection_log_6565_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6566_neg : (9859 / 50000000) ≤ -Real.log (2500000 / 2500493) ∧
    -Real.log (2500000 / 2500493) ≤ (197181 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 5000493)) (n := 12)
    (lo := (9859 / 50000000)) (hi := (197181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500493 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500493 / 2500000) = 1/(2500000 / 2500493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6566 : Bounds (9859 / 50000000) (197181 / 1000000000) (Real.log (2500493 / 2500000)) := by
  have h := reflection_log_6566_neg
  have he : Real.log (2500493 / 2500000) = -Real.log (2500000 / 2500493) := by
    rw [show ((2500493 / 2500000) : ℝ) = ((2500000 / 2500493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6567_neg : (197219 / 1000000000) ≤ -Real.log (2499507 / 2500000) ∧
    -Real.log (2499507 / 2500000) ≤ (9861 / 50000000) := by
  have h := checkLog_sound (w := (493 / 4999507)) (n := 12)
    (lo := (197219 / 1000000000)) (hi := (9861 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499507) = 1/(2499507 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6567 : Bounds (-9861 / 50000000) (-197219 / 1000000000) (Real.log (2499507 / 2500000)) := by
  have h := reflection_log_6567_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6568_neg : (94537153 / 1000000000) ≤ -Real.log (20000 / 21983) ∧
    -Real.log (20000 / 21983) ≤ (47268577 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 41983)) (n := 12)
    (lo := (94537153 / 1000000000)) (hi := (47268577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21983 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21983 / 20000) = 1/(20000 / 21983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6568 : Bounds (94537153 / 1000000000) (47268577 / 500000000) (Real.log (21983 / 20000)) := by
  have h := reflection_log_6568_neg
  have he : Real.log (21983 / 20000) = -Real.log (20000 / 21983) := by
    rw [show ((21983 / 20000) : ℝ) = ((20000 / 21983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6569_neg : (26104129 / 250000000) ≤ -Real.log (18017 / 20000) ∧
    -Real.log (18017 / 20000) ≤ (104416517 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 38017)) (n := 12)
    (lo := (26104129 / 250000000)) (hi := (104416517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18017) = 1/(18017 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6569 : Bounds (-104416517 / 1000000000) (-26104129 / 250000000) (Real.log (18017 / 20000)) := by
  have h := reflection_log_6569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6570_neg : (94762757 / 1000000000) ≤ -Real.log (500000 / 549699) ∧
    -Real.log (500000 / 549699) ≤ (47381379 / 500000000) := by
  have h := checkLog_sound (w := (49699 / 1049699)) (n := 12)
    (lo := (94762757 / 1000000000)) (hi := (47381379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549699 / 500000) = 1/(500000 / 549699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6570 : Bounds (94762757 / 1000000000) (47381379 / 500000000) (Real.log (549699 / 500000)) := by
  have h := reflection_log_6570_neg
  have he : Real.log (549699 / 500000) = -Real.log (500000 / 549699) := by
    rw [show ((549699 / 500000) : ℝ) = ((500000 / 549699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6571_neg : (2093837 / 20000000) ≤ -Real.log (450301 / 500000) ∧
    -Real.log (450301 / 500000) ≤ (104691851 / 1000000000) := by
  have h := checkLog_sound (w := (49699 / 950301)) (n := 12)
    (lo := (2093837 / 20000000)) (hi := (104691851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450301) = 1/(450301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6571 : Bounds (-104691851 / 1000000000) (-2093837 / 20000000) (Real.log (450301 / 500000)) := by
  have h := reflection_log_6571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6572_neg : (9929093 / 1000000000) ≤ -Real.log (247530009399 / 250000000000) ∧
    -Real.log (247530009399 / 250000000000) ≤ (4964547 / 500000000) := by
  have h := checkLog_sound (w := (2469990601 / 497530009399)) (n := 12)
    (lo := (9929093 / 1000000000)) (hi := (4964547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247530009399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247530009399) = 1/(247530009399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6572 : Bounds (-4964547 / 500000000) (-9929093 / 1000000000) (Real.log (247530009399 / 250000000000)) := by
  have h := reflection_log_6572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6573_neg : (9879363 / 1000000000) ≤ -Real.log (396067711 / 400000000) ∧
    -Real.log (396067711 / 400000000) ≤ (2469841 / 250000000) := by
  have h := checkLog_sound (w := (3932289 / 796067711)) (n := 12)
    (lo := (9879363 / 1000000000)) (hi := (2469841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396067711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396067711) = 1/(396067711 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6573 : Bounds (-2469841 / 250000000) (-9879363 / 1000000000) (Real.log (396067711 / 400000000)) := by
  have h := reflection_log_6573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6574_neg : (19895367 / 100000000) ≤ -Real.log (500000000000 / 610062718543) ∧
    -Real.log (500000000000 / 610062718543) ≤ (198953671 / 1000000000) := by
  have h := checkLog_sound (w := (110062718543 / 1110062718543)) (n := 12)
    (lo := (19895367 / 100000000)) (hi := (198953671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610062718543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610062718543 / 500000000000) = 1/(500000000000 / 610062718543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6574 : Bounds (19895367 / 100000000) (198953671 / 1000000000) (Real.log (610062718543 / 500000000000)) := by
  have h := reflection_log_6574_neg
  have he : Real.log (610062718543 / 500000000000) = -Real.log (500000000000 / 610062718543) := by
    rw [show ((610062718543 / 500000000000) : ℝ) = ((500000000000 / 610062718543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6575_neg : (199454607 / 1000000000) ≤ -Real.log (125000000000 / 152592099507) ∧
    -Real.log (125000000000 / 152592099507) ≤ (12465913 / 62500000) := by
  have h := checkLog_sound (w := (27592099507 / 277592099507)) (n := 12)
    (lo := (199454607 / 1000000000)) (hi := (12465913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152592099507 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152592099507 / 125000000000) = 1/(125000000000 / 152592099507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6575 : Bounds (199454607 / 1000000000) (12465913 / 62500000) (Real.log (152592099507 / 125000000000)) := by
  have h := reflection_log_6575_neg
  have he : Real.log (152592099507 / 125000000000) = -Real.log (125000000000 / 152592099507) := by
    rw [show ((152592099507 / 125000000000) : ℝ) = ((125000000000 / 152592099507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6576_neg : (399427071 / 1000000000) ≤ -Real.log (125000000000 / 186371279113) ∧
    -Real.log (125000000000 / 186371279113) ≤ (780131 / 1953125) := by
  have h := checkLog_sound (w := (61371279113 / 311371279113)) (n := 12)
    (lo := (399427071 / 1000000000)) (hi := (780131 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186371279113 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186371279113 / 125000000000) = 1/(125000000000 / 186371279113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6576 : Bounds (399427071 / 1000000000) (780131 / 1953125) (Real.log (186371279113 / 125000000000)) := by
  have h := reflection_log_6576_neg
  have he : Real.log (186371279113 / 125000000000) = -Real.log (125000000000 / 186371279113) := by
    rw [show ((186371279113 / 125000000000) : ℝ) = ((125000000000 / 186371279113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6577_neg : (399635159 / 1000000000) ≤ -Real.log (250000000000 / 372820129547) ∧
    -Real.log (250000000000 / 372820129547) ≤ (9990879 / 25000000) := by
  have h := checkLog_sound (w := (122820129547 / 622820129547)) (n := 12)
    (lo := (399635159 / 1000000000)) (hi := (9990879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372820129547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372820129547 / 250000000000) = 1/(250000000000 / 372820129547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6577 : Bounds (399635159 / 1000000000) (9990879 / 25000000) (Real.log (372820129547 / 250000000000)) := by
  have h := reflection_log_6577_neg
  have he : Real.log (372820129547 / 250000000000) = -Real.log (250000000000 / 372820129547) := by
    rw [show ((372820129547 / 250000000000) : ℝ) = ((250000000000 / 372820129547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6578_neg : (180069021 / 1000000000) ≤ -Real.log (10000 / 11973) ∧
    -Real.log (10000 / 11973) ≤ (90034511 / 500000000) := by
  have h := checkLog_sound (w := (1973 / 21973)) (n := 12)
    (lo := (180069021 / 1000000000)) (hi := (90034511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11973 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11973 / 10000) = 1/(10000 / 11973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6578 : Bounds (180069021 / 1000000000) (90034511 / 500000000) (Real.log (11973 / 10000)) := by
  have h := reflection_log_6578_neg
  have he : Real.log (11973 / 10000) = -Real.log (10000 / 11973) := by
    rw [show ((11973 / 10000) : ℝ) = ((10000 / 11973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6579_neg : (219774233 / 1000000000) ≤ -Real.log (8027 / 10000) ∧
    -Real.log (8027 / 10000) ≤ (109887117 / 500000000) := by
  have h := checkLog_sound (w := (1973 / 18027)) (n := 12)
    (lo := (219774233 / 1000000000)) (hi := (109887117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8027) = 1/(8027 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6579 : Bounds (-109887117 / 500000000) (-219774233 / 1000000000) (Real.log (8027 / 10000)) := by
  have h := reflection_log_6579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6580_neg : (1233 / 6250000) ≤ -Real.log (10000000 / 10001973) ∧
    -Real.log (10000000 / 10001973) ≤ (197281 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 20001973)) (n := 12)
    (lo := (1233 / 6250000)) (hi := (197281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001973 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001973 / 10000000) = 1/(10000000 / 10001973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6580 : Bounds (1233 / 6250000) (197281 / 1000000000) (Real.log (10001973 / 10000000)) := by
  have h := reflection_log_6580_neg
  have he : Real.log (10001973 / 10000000) = -Real.log (10000000 / 10001973) := by
    rw [show ((10001973 / 10000000) : ℝ) = ((10000000 / 10001973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6581_neg : (197319 / 1000000000) ≤ -Real.log (9998027 / 10000000) ∧
    -Real.log (9998027 / 10000000) ≤ (4933 / 25000000) := by
  have h := checkLog_sound (w := (1973 / 19998027)) (n := 12)
    (lo := (197319 / 1000000000)) (hi := (4933 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998027) = 1/(9998027 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6581 : Bounds (-4933 / 25000000) (-197319 / 1000000000) (Real.log (9998027 / 10000000)) := by
  have h := reflection_log_6581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6582_neg : (369467 / 3906250) ≤ -Real.log (1000000 / 1099201) ∧
    -Real.log (1000000 / 1099201) ≤ (94583553 / 1000000000) := by
  have h := checkLog_sound (w := (99201 / 2099201)) (n := 12)
    (lo := (369467 / 3906250)) (hi := (94583553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099201 / 1000000) = 1/(1000000 / 1099201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6582 : Bounds (369467 / 3906250) (94583553 / 1000000000) (Real.log (1099201 / 1000000)) := by
  have h := reflection_log_6582_neg
  have he : Real.log (1099201 / 1000000) = -Real.log (1000000 / 1099201) := by
    rw [show ((1099201 / 1000000) : ℝ) = ((1000000 / 1099201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6583_neg : (104473131 / 1000000000) ≤ -Real.log (900799 / 1000000) ∧
    -Real.log (900799 / 1000000) ≤ (26118283 / 250000000) := by
  have h := checkLog_sound (w := (99201 / 1900799)) (n := 12)
    (lo := (104473131 / 1000000000)) (hi := (26118283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900799) = 1/(900799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6583 : Bounds (-26118283 / 250000000) (-104473131 / 1000000000) (Real.log (900799 / 1000000)) := by
  have h := reflection_log_6583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6584_neg : (18961829 / 200000000) ≤ -Real.log (1000000 / 1099449) ∧
    -Real.log (1000000 / 1099449) ≤ (47404573 / 500000000) := by
  have h := checkLog_sound (w := (99449 / 2099449)) (n := 12)
    (lo := (18961829 / 200000000)) (hi := (47404573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099449 / 1000000) = 1/(1000000 / 1099449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6584 : Bounds (18961829 / 200000000) (47404573 / 500000000) (Real.log (1099449 / 1000000)) := by
  have h := reflection_log_6584_neg
  have he : Real.log (1099449 / 1000000) = -Real.log (1000000 / 1099449) := by
    rw [show ((1099449 / 1000000) : ℝ) = ((1000000 / 1099449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6585_neg : (327339 / 3125000) ≤ -Real.log (900551 / 1000000) ∧
    -Real.log (900551 / 1000000) ≤ (104748481 / 1000000000) := by
  have h := checkLog_sound (w := (99449 / 1900551)) (n := 12)
    (lo := (327339 / 3125000)) (hi := (104748481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900551) = 1/(900551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6585 : Bounds (-104748481 / 1000000000) (-327339 / 3125000) (Real.log (900551 / 1000000)) := by
  have h := reflection_log_6585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6586_neg : (1987867 / 200000000) ≤ -Real.log (990109896399 / 1000000000000) ∧
    -Real.log (990109896399 / 1000000000000) ≤ (1242417 / 125000000) := by
  have h := checkLog_sound (w := (9890103601 / 1990109896399)) (n := 12)
    (lo := (1987867 / 200000000)) (hi := (1242417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990109896399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990109896399) = 1/(990109896399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6586 : Bounds (-1242417 / 125000000) (-1987867 / 200000000) (Real.log (990109896399 / 1000000000000)) := by
  have h := reflection_log_6586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6587_neg : (9889579 / 1000000000) ≤ -Real.log (990159161599 / 1000000000000) ∧
    -Real.log (990159161599 / 1000000000000) ≤ (494479 / 50000000) := by
  have h := checkLog_sound (w := (9840838401 / 1990159161599)) (n := 12)
    (lo := (9889579 / 1000000000)) (hi := (494479 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990159161599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990159161599) = 1/(990159161599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6587 : Bounds (-494479 / 50000000) (-9889579 / 1000000000) (Real.log (990159161599 / 1000000000000)) := by
  have h := reflection_log_6587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6588_neg : (199056683 / 1000000000) ≤ -Real.log (250000000000 / 305062783151) ∧
    -Real.log (250000000000 / 305062783151) ≤ (49764171 / 250000000) := by
  have h := checkLog_sound (w := (55062783151 / 555062783151)) (n := 12)
    (lo := (199056683 / 1000000000)) (hi := (49764171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305062783151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305062783151 / 250000000000) = 1/(250000000000 / 305062783151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6588 : Bounds (199056683 / 1000000000) (49764171 / 250000000) (Real.log (305062783151 / 250000000000)) := by
  have h := reflection_log_6588_neg
  have he : Real.log (305062783151 / 250000000000) = -Real.log (250000000000 / 305062783151) := by
    rw [show ((305062783151 / 250000000000) : ℝ) = ((250000000000 / 305062783151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6589_neg : (1596461 / 8000000) ≤ -Real.log (100000000000 / 122086256081) ∧
    -Real.log (100000000000 / 122086256081) ≤ (99778813 / 500000000) := by
  have h := checkLog_sound (w := (22086256081 / 222086256081)) (n := 12)
    (lo := (1596461 / 8000000)) (hi := (99778813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122086256081 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122086256081 / 100000000000) = 1/(100000000000 / 122086256081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6589 : Bounds (1596461 / 8000000) (99778813 / 500000000) (Real.log (122086256081 / 100000000000)) := by
  have h := reflection_log_6589_neg
  have he : Real.log (122086256081 / 100000000000) = -Real.log (100000000000 / 122086256081) := by
    rw [show ((122086256081 / 100000000000) : ℝ) = ((100000000000 / 122086256081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6590_neg : (399635159 / 1000000000) ≤ -Real.log (500000000000 / 745640259093) ∧
    -Real.log (500000000000 / 745640259093) ≤ (9990879 / 25000000) := by
  have h := checkLog_sound (w := (245640259093 / 1245640259093)) (n := 12)
    (lo := (399635159 / 1000000000)) (hi := (9990879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745640259093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745640259093 / 500000000000) = 1/(500000000000 / 745640259093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6590 : Bounds (399635159 / 1000000000) (9990879 / 25000000) (Real.log (745640259093 / 500000000000)) := by
  have h := reflection_log_6590_neg
  have he : Real.log (745640259093 / 500000000000) = -Real.log (500000000000 / 745640259093) := by
    rw [show ((745640259093 / 500000000000) : ℝ) = ((500000000000 / 745640259093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6591_neg : (79968651 / 200000000) ≤ -Real.log (500000000000 / 745795440389) ∧
    -Real.log (500000000000 / 745795440389) ≤ (49980407 / 125000000) := by
  have h := checkLog_sound (w := (245795440389 / 1245795440389)) (n := 12)
    (lo := (79968651 / 200000000)) (hi := (49980407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745795440389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745795440389 / 500000000000) = 1/(500000000000 / 745795440389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6591 : Bounds (79968651 / 200000000) (49980407 / 125000000) (Real.log (745795440389 / 500000000000)) := by
  have h := reflection_log_6591_neg
  have he : Real.log (745795440389 / 500000000000) = -Real.log (500000000000 / 745795440389) := by
    rw [show ((745795440389 / 500000000000) : ℝ) = ((500000000000 / 745795440389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
