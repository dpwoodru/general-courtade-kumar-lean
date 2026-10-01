import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0197
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

theorem reflection_log_1_neg : (598664783 / 1000000000) ≤ -Real.log (3200 / 5823) ∧
    -Real.log (3200 / 5823) ≤ (37416549 / 62500000) := by
  have h := checkLog_sound (w := (2623 / 9023)) (n := 12)
    (lo := (598664783 / 1000000000)) (hi := (37416549 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 3200) = 1/(3200 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (598664783 / 1000000000) (37416549 / 62500000) (Real.log (5823 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5823 / 3200) = -Real.log (3200 / 5823) := by
    rw [show ((5823 / 3200) : ℝ) = ((3200 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1713063821 / 1000000000) ≤ -Real.log (577 / 3200) ∧
    -Real.log (577 / 3200) ≤ (107066489 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 577) = 1/(577 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-107066489 / 62500000) (-1713063821 / 1000000000) (Real.log (577 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (597031989 / 1000000000) ≤ -Real.log (6400 / 11627) ∧
    -Real.log (6400 / 11627) ≤ (59703199 / 100000000) := by
  have h := checkLog_sound (w := (5227 / 18027)) (n := 12)
    (lo := (597031989 / 1000000000)) (hi := (59703199 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 6400) = 1/(6400 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (597031989 / 1000000000) (59703199 / 100000000) (Real.log (11627 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11627 / 6400) = -Real.log (6400 / 11627) := by
    rw [show ((11627 / 6400) : ℝ) = ((6400 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1696733419 / 1000000000) ≤ -Real.log (1173 / 6400) ∧
    -Real.log (1173 / 6400) ≤ (848366711 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1173) = 1/(1173 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-848366711 / 500000000) (-1696733419 / 1000000000) (Real.log (1173 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (494315071 / 1000000000) ≤ -Real.log (1600 / 2623) ∧
    -Real.log (1600 / 2623) ≤ (7723673 / 15625000) := by
  have h := checkLog_sound (w := (1023 / 4223)) (n := 12)
    (lo := (494315071 / 1000000000)) (hi := (7723673 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2623 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2623 / 1600) = 1/(1600 / 2623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (494315071 / 1000000000) (7723673 / 15625000) (Real.log (2623 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2623 / 1600) = -Real.log (1600 / 2623) := by
    rw [show ((2623 / 1600) : ℝ) = ((1600 / 2623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1019916641 / 1000000000) ≤ -Real.log (577 / 1600) ∧
    -Real.log (577 / 1600) ≤ (1019916643 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1377)) (n := 12)
    (lo := (326769461 / 1000000000)) (hi := (163384731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 577) = 1/(577 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1019916643 / 1000000000) (-1019916641 / 1000000000) (Real.log (577 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (490686689 / 1000000000) ≤ -Real.log (3200 / 5227) ∧
    -Real.log (3200 / 5227) ≤ (49068669 / 100000000) := by
  have h := checkLog_sound (w := (2027 / 8427)) (n := 12)
    (lo := (490686689 / 1000000000)) (hi := (49068669 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5227 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5227 / 3200) = 1/(3200 / 5227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (490686689 / 1000000000) (49068669 / 100000000) (Real.log (5227 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5227 / 3200) = -Real.log (3200 / 5227) := by
    rw [show ((5227 / 3200) : ℝ) = ((3200 / 5227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1003586239 / 1000000000) ≤ -Real.log (1173 / 3200) ∧
    -Real.log (1173 / 3200) ≤ (1003586241 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2773)) (n := 12)
    (lo := (310439059 / 1000000000)) (hi := (15521953 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1173) = 1/(1173 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1003586241 / 1000000000) (-1003586239 / 1000000000) (Real.log (1173 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62687489 / 100000000) ≤ -Real.log (125000 / 233969) ∧
    -Real.log (125000 / 233969) ≤ (626874891 / 1000000000) := by
  have h := checkLog_sound (w := (108969 / 358969)) (n := 12)
    (lo := (62687489 / 100000000)) (hi := (626874891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233969 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233969 / 125000) = 1/(125000 / 233969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62687489 / 100000000) (626874891 / 1000000000) (Real.log (233969 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233969 / 125000) = -Real.log (125000 / 233969) := by
    rw [show ((233969 / 125000) : ℝ) = ((125000 / 233969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (513447347 / 250000000) ≤ -Real.log (16031 / 125000) ∧
    -Real.log (16031 / 125000) ≤ (2053789391 / 1000000000) := by
  have h := checkLog_sound (w := (15219 / 47281)) (n := 12)
    (lo := (166873757 / 250000000)) (hi := (667495029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16031) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 16031) = 1/(16031 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2053789391 / 1000000000) (-513447347 / 250000000) (Real.log (16031 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (78470371 / 125000000) ≤ -Real.log (200000 / 374683) ∧
    -Real.log (200000 / 374683) ≤ (627762969 / 1000000000) := by
  have h := checkLog_sound (w := (174683 / 574683)) (n := 12)
    (lo := (78470371 / 125000000)) (hi := (627762969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374683 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374683 / 200000) = 1/(200000 / 374683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (78470371 / 125000000) (627762969 / 1000000000) (Real.log (374683 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374683 / 200000) = -Real.log (200000 / 374683) := by
    rw [show ((374683 / 200000) : ℝ) = ((200000 / 374683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1033420629 / 500000000) ≤ -Real.log (25317 / 200000) ∧
    -Real.log (25317 / 200000) ≤ (2066841261 / 1000000000) := by
  have h := checkLog_sound (w := (24683 / 75317)) (n := 12)
    (lo := (340273449 / 500000000)) (hi := (680546899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25317) = 1/(25317 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2066841261 / 1000000000) (-1033420629 / 500000000) (Real.log (25317 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (621540539 / 1000000000) ≤ -Real.log (500000 / 930897) ∧
    -Real.log (500000 / 930897) ≤ (31077027 / 50000000) := by
  have h := checkLog_sound (w := (430897 / 1430897)) (n := 12)
    (lo := (621540539 / 1000000000)) (hi := (31077027 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930897 / 500000) = 1/(500000 / 930897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (621540539 / 1000000000) (31077027 / 50000000) (Real.log (930897 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (930897 / 500000) = -Real.log (500000 / 930897) := by
    rw [show ((930897 / 500000) : ℝ) = ((500000 / 930897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61844061 / 31250000) ≤ -Real.log (69103 / 500000) ∧
    -Real.log (69103 / 500000) ≤ (395801991 / 200000000) := by
  have h := checkLog_sound (w := (55897 / 194103)) (n := 12)
    (lo := (74089449 / 125000000)) (hi := (592715593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69103) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 69103) = 1/(69103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-395801991 / 200000000) (-61844061 / 31250000) (Real.log (69103 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (155659987 / 250000000) ≤ -Real.log (500000 / 931921) ∧
    -Real.log (500000 / 931921) ≤ (622639949 / 1000000000) := by
  have h := checkLog_sound (w := (431921 / 1431921)) (n := 12)
    (lo := (155659987 / 250000000)) (hi := (622639949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((931921 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(931921 / 500000) = 1/(500000 / 931921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (155659987 / 250000000) (622639949 / 1000000000) (Real.log (931921 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (931921 / 500000) = -Real.log (500000 / 931921) := by
    rw [show ((931921 / 500000) : ℝ) = ((500000 / 931921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1993939301 / 1000000000) ≤ -Real.log (68079 / 500000) ∧
    -Real.log (68079 / 500000) ≤ (249242413 / 125000000) := by
  have h := checkLog_sound (w := (56921 / 193079)) (n := 12)
    (lo := (607644941 / 1000000000)) (hi := (303822471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68079) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 68079) = 1/(68079 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-249242413 / 125000000) (-1993939301 / 1000000000) (Real.log (68079 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1340332139 / 500000000) ≤ -Real.log (50000000000 / 729739255193) ∧
    -Real.log (50000000000 / 729739255193) ≤ (1340332141 / 500000000) := by
  have h := checkLog_sound (w := (329739255193 / 1129739255193)) (n := 12)
    (lo := (300611369 / 500000000)) (hi := (601222739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729739255193 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(729739255193 / 400000000000) = 1/(50000000000 / 729739255193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1340332139 / 500000000) (1340332141 / 500000000) (Real.log (729739255193 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (729739255193 / 50000000000) = -Real.log (50000000000 / 729739255193) := by
    rw [show ((729739255193 / 50000000000) : ℝ) = ((50000000000 / 729739255193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1347302113 / 500000000) ≤ -Real.log (125000000000 / 1849957538413) ∧
    -Real.log (125000000000 / 1849957538413) ≤ (269460423 / 100000000) := by
  have h := checkLog_sound (w := (849957538413 / 2849957538413)) (n := 12)
    (lo := (307581343 / 500000000)) (hi := (615162687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1849957538413 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1849957538413 / 1000000000000) = 1/(125000000000 / 1849957538413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1347302113 / 500000000) (269460423 / 100000000) (Real.log (1849957538413 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1849957538413 / 125000000000) = -Real.log (125000000000 / 1849957538413) := by
    rw [show ((1849957538413 / 125000000000) : ℝ) = ((125000000000 / 1849957538413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (260055049 / 100000000) ≤ -Real.log (125000000000 / 1683893969871) ∧
    -Real.log (125000000000 / 1683893969871) ≤ (1300275247 / 500000000) := by
  have h := checkLog_sound (w := (683893969871 / 2683893969871)) (n := 12)
    (lo := (10422179 / 20000000)) (hi := (521108951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683893969871 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1683893969871 / 1000000000000) = 1/(125000000000 / 1683893969871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (260055049 / 100000000) (1300275247 / 500000000) (Real.log (1683893969871 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1683893969871 / 125000000000) = -Real.log (125000000000 / 1683893969871) := by
    rw [show ((1683893969871 / 125000000000) : ℝ) = ((125000000000 / 1683893969871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2616579249 / 1000000000) ≤ -Real.log (62500000000 / 855551087707) ∧
    -Real.log (62500000000 / 855551087707) ≤ (2616579253 / 1000000000) := by
  have h := checkLog_sound (w := (355551087707 / 1355551087707)) (n := 12)
    (lo := (537137709 / 1000000000)) (hi := (53713771 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855551087707 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(855551087707 / 500000000000) = 1/(62500000000 / 855551087707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2616579249 / 1000000000) (2616579253 / 1000000000) (Real.log (855551087707 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (855551087707 / 62500000000) = -Real.log (62500000000 / 855551087707) := by
    rw [show ((855551087707 / 62500000000) : ℝ) = ((62500000000 / 855551087707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0197
