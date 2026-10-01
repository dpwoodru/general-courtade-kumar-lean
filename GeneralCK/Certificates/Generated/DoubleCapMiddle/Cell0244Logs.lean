import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0244
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

theorem reflection_log_1_neg : (245699737 / 1000000000) ≤ -Real.log (2560 / 3273) ∧
    -Real.log (2560 / 3273) ≤ (122849869 / 500000000) := by
  have h := checkLog_sound (w := (713 / 5833)) (n := 12)
    (lo := (245699737 / 1000000000)) (hi := (122849869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3273 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3273 / 2560) = 1/(2560 / 3273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (245699737 / 1000000000) (122849869 / 500000000) (Real.log (3273 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3273 / 2560) = -Real.log (2560 / 3273) := by
    rw [show ((3273 / 2560) : ℝ) = ((2560 / 3273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (326444557 / 1000000000) ≤ -Real.log (1847 / 2560) ∧
    -Real.log (1847 / 2560) ≤ (163222279 / 500000000) := by
  have h := checkLog_sound (w := (713 / 4407)) (n := 12)
    (lo := (326444557 / 1000000000)) (hi := (163222279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1847) = 1/(1847 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-163222279 / 500000000) (-326444557 / 1000000000) (Real.log (1847 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (30655167 / 125000000) ≤ -Real.log (5120 / 6543) ∧
    -Real.log (5120 / 6543) ≤ (245241337 / 1000000000) := by
  have h := checkLog_sound (w := (1423 / 11663)) (n := 12)
    (lo := (30655167 / 125000000)) (hi := (245241337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6543 / 5120) = 1/(5120 / 6543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (30655167 / 125000000) (245241337 / 1000000000) (Real.log (6543 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6543 / 5120) = -Real.log (5120 / 6543) := by
    rw [show ((6543 / 5120) : ℝ) = ((5120 / 6543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (325632759 / 1000000000) ≤ -Real.log (3697 / 5120) ∧
    -Real.log (3697 / 5120) ≤ (8140819 / 25000000) := by
  have h := checkLog_sound (w := (1423 / 8817)) (n := 12)
    (lo := (325632759 / 1000000000)) (hi := (8140819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3697) = 1/(3697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8140819 / 25000000) (-325632759 / 1000000000) (Real.log (3697 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (442780963 / 1000000000) ≤ -Real.log (1280 / 1993) ∧
    -Real.log (1280 / 1993) ≤ (110695241 / 250000000) := by
  have h := checkLog_sound (w := (713 / 3273)) (n := 12)
    (lo := (442780963 / 1000000000)) (hi := (110695241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1280) = 1/(1280 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (442780963 / 1000000000) (110695241 / 250000000) (Real.log (1993 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1993 / 1280) = -Real.log (1280 / 1993) := by
    rw [show ((1993 / 1280) : ℝ) = ((1280 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203564013 / 250000000) ≤ -Real.log (567 / 1280) ∧
    -Real.log (567 / 1280) ≤ (407128027 / 500000000) := by
  have h := checkLog_sound (w := (73 / 1207)) (n := 12)
    (lo := (15138609 / 125000000)) (hi := (121108873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 567) = 1/(567 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-407128027 / 500000000) (-203564013 / 250000000) (Real.log (567 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (88405609 / 200000000) ≤ -Real.log (2560 / 3983) ∧
    -Real.log (2560 / 3983) ≤ (221014023 / 500000000) := by
  have h := checkLog_sound (w := (1423 / 6543)) (n := 12)
    (lo := (88405609 / 200000000)) (hi := (221014023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3983 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3983 / 2560) = 1/(2560 / 3983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (88405609 / 200000000) (221014023 / 500000000) (Real.log (3983 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3983 / 2560) = -Real.log (2560 / 3983) := by
    rw [show ((3983 / 2560) : ℝ) = ((2560 / 3983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (811614043 / 1000000000) ≤ -Real.log (1137 / 2560) ∧
    -Real.log (1137 / 2560) ≤ (162322809 / 200000000) := by
  have h := checkLog_sound (w := (143 / 2417)) (n := 12)
    (lo := (118466863 / 1000000000)) (hi := (7404179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1137) = 1/(1137 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-162322809 / 200000000) (-811614043 / 1000000000) (Real.log (1137 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (335682639 / 1000000000) ≤ -Real.log (200000 / 279779) ∧
    -Real.log (200000 / 279779) ≤ (4196033 / 12500000) := by
  have h := checkLog_sound (w := (79779 / 479779)) (n := 12)
    (lo := (335682639 / 1000000000)) (hi := (4196033 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279779 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279779 / 200000) = 1/(200000 / 279779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (335682639 / 1000000000) (4196033 / 12500000) (Real.log (279779 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (279779 / 200000) = -Real.log (200000 / 279779) := by
    rw [show ((279779 / 200000) : ℝ) = ((200000 / 279779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10179713 / 20000000) ≤ -Real.log (120221 / 200000) ∧
    -Real.log (120221 / 200000) ≤ (508985651 / 1000000000) := by
  have h := checkLog_sound (w := (79779 / 320221)) (n := 12)
    (lo := (10179713 / 20000000)) (hi := (508985651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120221) = 1/(120221 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-508985651 / 1000000000) (-10179713 / 20000000) (Real.log (120221 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336305079 / 1000000000) ≤ -Real.log (500000 / 699883) ∧
    -Real.log (500000 / 699883) ≤ (8407627 / 25000000) := by
  have h := checkLog_sound (w := (199883 / 1199883)) (n := 12)
    (lo := (336305079 / 1000000000)) (hi := (8407627 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699883 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699883 / 500000) = 1/(500000 / 699883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336305079 / 1000000000) (8407627 / 25000000) (Real.log (699883 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (699883 / 500000) = -Real.log (500000 / 699883) := by
    rw [show ((699883 / 500000) : ℝ) = ((500000 / 699883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (510435699 / 1000000000) ≤ -Real.log (300117 / 500000) ∧
    -Real.log (300117 / 500000) ≤ (5104357 / 10000000) := by
  have h := checkLog_sound (w := (199883 / 800117)) (n := 12)
    (lo := (510435699 / 1000000000)) (hi := (5104357 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 300117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 300117) = 1/(300117 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5104357 / 10000000) (-510435699 / 1000000000) (Real.log (300117 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129270791 / 500000000) ≤ -Real.log (3125 / 4047) ∧
    -Real.log (3125 / 4047) ≤ (258541583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3586)) (n := 12)
    (lo := (129270791 / 500000000)) (hi := (258541583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4047 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4047 / 3125) = 1/(3125 / 4047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129270791 / 500000000) (258541583 / 1000000000) (Real.log (4047 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4047 / 3125) = -Real.log (3125 / 4047) := by
    rw [show ((4047 / 3125) : ℝ) = ((3125 / 4047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69922843 / 200000000) ≤ -Real.log (2203 / 3125) ∧
    -Real.log (2203 / 3125) ≤ (43701777 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2664)) (n := 12)
    (lo := (69922843 / 200000000)) (hi := (43701777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2203) = 1/(2203 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-43701777 / 125000000) (-69922843 / 200000000) (Real.log (2203 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10363371 / 40000000) ≤ -Real.log (1000000 / 1295743) ∧
    -Real.log (1000000 / 1295743) ≤ (64771069 / 250000000) := by
  have h := checkLog_sound (w := (295743 / 2295743)) (n := 12)
    (lo := (10363371 / 40000000)) (hi := (64771069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295743 / 1000000) = 1/(1000000 / 1295743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10363371 / 40000000) (64771069 / 250000000) (Real.log (1295743 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1295743 / 1000000) = -Real.log (1000000 / 1295743) := by
    rw [show ((1295743 / 1000000) : ℝ) = ((1000000 / 1295743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (87652983 / 250000000) ≤ -Real.log (704257 / 1000000) ∧
    -Real.log (704257 / 1000000) ≤ (350611933 / 1000000000) := by
  have h := checkLog_sound (w := (295743 / 1704257)) (n := 12)
    (lo := (87652983 / 250000000)) (hi := (350611933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704257) = 1/(704257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-350611933 / 1000000000) (-87652983 / 250000000) (Real.log (704257 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (844668289 / 1000000000) ≤ -Real.log (125000000000 / 290900716181) ∧
    -Real.log (125000000000 / 290900716181) ≤ (844668291 / 1000000000) := by
  have h := checkLog_sound (w := (40900716181 / 540900716181)) (n := 12)
    (lo := (151521109 / 1000000000)) (hi := (15152111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290900716181 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(290900716181 / 250000000000) = 1/(125000000000 / 290900716181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (844668289 / 1000000000) (844668291 / 1000000000) (Real.log (290900716181 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (290900716181 / 125000000000) = -Real.log (125000000000 / 290900716181) := by
    rw [show ((290900716181 / 125000000000) : ℝ) = ((125000000000 / 290900716181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (846740779 / 1000000000) ≤ -Real.log (125000000000 / 291504230017) ∧
    -Real.log (125000000000 / 291504230017) ≤ (846740781 / 1000000000) := by
  have h := checkLog_sound (w := (41504230017 / 541504230017)) (n := 12)
    (lo := (153593599 / 1000000000)) (hi := (23999 / 156250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291504230017 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(291504230017 / 250000000000) = 1/(125000000000 / 291504230017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (846740779 / 1000000000) (846740781 / 1000000000) (Real.log (291504230017 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (291504230017 / 125000000000) = -Real.log (125000000000 / 291504230017) := by
    rw [show ((291504230017 / 125000000000) : ℝ) = ((125000000000 / 291504230017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (304077899 / 500000000) ≤ -Real.log (500000000000 / 918520199727) ∧
    -Real.log (500000000000 / 918520199727) ≤ (608155799 / 1000000000) := by
  have h := checkLog_sound (w := (418520199727 / 1418520199727)) (n := 12)
    (lo := (304077899 / 500000000)) (hi := (608155799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918520199727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918520199727 / 500000000000) = 1/(500000000000 / 918520199727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (304077899 / 500000000) (608155799 / 1000000000) (Real.log (918520199727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (918520199727 / 500000000000) = -Real.log (500000000000 / 918520199727) := by
    rw [show ((918520199727 / 500000000000) : ℝ) = ((500000000000 / 918520199727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (38106013 / 62500000) ≤ -Real.log (125000000000 / 229984047017) ∧
    -Real.log (125000000000 / 229984047017) ≤ (609696209 / 1000000000) := by
  have h := checkLog_sound (w := (104984047017 / 354984047017)) (n := 12)
    (lo := (38106013 / 62500000)) (hi := (609696209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229984047017 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229984047017 / 125000000000) = 1/(125000000000 / 229984047017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (38106013 / 62500000) (609696209 / 1000000000) (Real.log (229984047017 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (229984047017 / 125000000000) = -Real.log (125000000000 / 229984047017) := by
    rw [show ((229984047017 / 125000000000) : ℝ) = ((125000000000 / 229984047017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0244
