import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0232
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

theorem reflection_log_1_neg : (251184211 / 1000000000) ≤ -Real.log (2560 / 3291) ∧
    -Real.log (2560 / 3291) ≤ (62796053 / 250000000) := by
  have h := checkLog_sound (w := (731 / 5851)) (n := 12)
    (lo := (251184211 / 1000000000)) (hi := (62796053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3291 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3291 / 2560) = 1/(2560 / 3291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (251184211 / 1000000000) (62796053 / 250000000) (Real.log (3291 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3291 / 2560) = -Real.log (2560 / 3291) := by
    rw [show ((3291 / 2560) : ℝ) = ((2560 / 3291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (336237889 / 1000000000) ≤ -Real.log (1829 / 2560) ∧
    -Real.log (1829 / 2560) ≤ (33623789 / 100000000) := by
  have h := checkLog_sound (w := (731 / 4389)) (n := 12)
    (lo := (336237889 / 1000000000)) (hi := (33623789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1829) = 1/(1829 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33623789 / 100000000) (-336237889 / 1000000000) (Real.log (1829 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (250728319 / 1000000000) ≤ -Real.log (5120 / 6579) ∧
    -Real.log (5120 / 6579) ≤ (391763 / 1562500) := by
  have h := checkLog_sound (w := (1459 / 11699)) (n := 12)
    (lo := (250728319 / 1000000000)) (hi := (391763 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6579 / 5120) = 1/(5120 / 6579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (250728319 / 1000000000) (391763 / 1562500) (Real.log (6579 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6579 / 5120) = -Real.log (5120 / 6579) := by
    rw [show ((6579 / 5120) : ℝ) = ((5120 / 6579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41927263 / 125000000) ≤ -Real.log (3661 / 5120) ∧
    -Real.log (3661 / 5120) ≤ (67083621 / 200000000) := by
  have h := checkLog_sound (w := (1459 / 8781)) (n := 12)
    (lo := (41927263 / 125000000)) (hi := (67083621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3661) = 1/(3661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-67083621 / 200000000) (-41927263 / 125000000) (Real.log (3661 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3529469 / 7812500) ≤ -Real.log (1280 / 2011) ∧
    -Real.log (1280 / 2011) ≤ (451772033 / 1000000000) := by
  have h := checkLog_sound (w := (731 / 3291)) (n := 12)
    (lo := (3529469 / 7812500)) (hi := (451772033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2011 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2011 / 1280) = 1/(1280 / 2011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3529469 / 7812500) (451772033 / 1000000000) (Real.log (2011 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2011 / 1280) = -Real.log (1280 / 2011) := by
    rw [show ((2011 / 1280) : ℝ) = ((1280 / 2011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (423258457 / 500000000) ≤ -Real.log (549 / 1280) ∧
    -Real.log (549 / 1280) ≤ (211629229 / 250000000) := by
  have h := checkLog_sound (w := (91 / 1189)) (n := 12)
    (lo := (76684867 / 500000000)) (hi := (30673947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 549) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 549) = 1/(549 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211629229 / 250000000) (-423258457 / 500000000) (Real.log (549 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7047279 / 15625000) ≤ -Real.log (2560 / 4019) ∧
    -Real.log (2560 / 4019) ≤ (451025857 / 1000000000) := by
  have h := checkLog_sound (w := (1459 / 6579)) (n := 12)
    (lo := (7047279 / 15625000)) (hi := (451025857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4019 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4019 / 2560) = 1/(2560 / 4019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7047279 / 15625000) (451025857 / 1000000000) (Real.log (4019 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4019 / 2560) = -Real.log (2560 / 4019) := by
    rw [show ((4019 / 2560) : ℝ) = ((2560 / 4019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2109471 / 2500000) ≤ -Real.log (1101 / 2560) ∧
    -Real.log (1101 / 2560) ≤ (421894201 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2381)) (n := 12)
    (lo := (7532061 / 50000000)) (hi := (150641221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1101) = 1/(1101 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-421894201 / 500000000) (-2109471 / 2500000) (Real.log (1101 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85781619 / 250000000) ≤ -Real.log (1000000 / 1409347) ∧
    -Real.log (1000000 / 1409347) ≤ (343126477 / 1000000000) := by
  have h := checkLog_sound (w := (409347 / 2409347)) (n := 12)
    (lo := (85781619 / 250000000)) (hi := (343126477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409347 / 1000000) = 1/(1000000 / 1409347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85781619 / 250000000) (343126477 / 1000000000) (Real.log (1409347 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1409347 / 1000000) = -Real.log (1000000 / 1409347) := by
    rw [show ((1409347 / 1000000) : ℝ) = ((1000000 / 1409347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (263263287 / 500000000) ≤ -Real.log (590653 / 1000000) ∧
    -Real.log (590653 / 1000000) ≤ (21061063 / 40000000) := by
  have h := checkLog_sound (w := (409347 / 1590653)) (n := 12)
    (lo := (263263287 / 500000000)) (hi := (21061063 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590653) = 1/(590653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21061063 / 40000000) (-263263287 / 500000000) (Real.log (590653 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (343746429 / 1000000000) ≤ -Real.log (1000000 / 1410221) ∧
    -Real.log (1000000 / 1410221) ≤ (34374643 / 100000000) := by
  have h := checkLog_sound (w := (410221 / 2410221)) (n := 12)
    (lo := (343746429 / 1000000000)) (hi := (34374643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1410221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1410221 / 1000000) = 1/(1000000 / 1410221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (343746429 / 1000000000) (34374643 / 100000000) (Real.log (1410221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1410221 / 1000000) = -Real.log (1000000 / 1410221) := by
    rw [show ((1410221 / 1000000) : ℝ) = ((1000000 / 1410221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (132001847 / 250000000) ≤ -Real.log (589779 / 1000000) ∧
    -Real.log (589779 / 1000000) ≤ (528007389 / 1000000000) := by
  have h := checkLog_sound (w := (410221 / 1589779)) (n := 12)
    (lo := (132001847 / 250000000)) (hi := (528007389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 589779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 589779) = 1/(589779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-528007389 / 1000000000) (-132001847 / 250000000) (Real.log (589779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (132529929 / 500000000) ≤ -Real.log (1000000 / 1303509) ∧
    -Real.log (1000000 / 1303509) ≤ (265059859 / 1000000000) := by
  have h := checkLog_sound (w := (303509 / 2303509)) (n := 12)
    (lo := (132529929 / 500000000)) (hi := (265059859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303509 / 1000000) = 1/(1000000 / 1303509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (132529929 / 500000000) (265059859 / 1000000000) (Real.log (1303509 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1303509 / 1000000) = -Real.log (1000000 / 1303509) := by
    rw [show ((1303509 / 1000000) : ℝ) = ((1000000 / 1303509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (361700407 / 1000000000) ≤ -Real.log (696491 / 1000000) ∧
    -Real.log (696491 / 1000000) ≤ (45212551 / 125000000) := by
  have h := checkLog_sound (w := (303509 / 1696491)) (n := 12)
    (lo := (361700407 / 1000000000)) (hi := (45212551 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 696491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 696491) = 1/(696491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45212551 / 125000000) (-361700407 / 1000000000) (Real.log (696491 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6640129 / 25000000) ≤ -Real.log (50000 / 65211) ∧
    -Real.log (50000 / 65211) ≤ (265605161 / 1000000000) := by
  have h := checkLog_sound (w := (15211 / 115211)) (n := 12)
    (lo := (6640129 / 25000000)) (hi := (265605161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65211 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65211 / 50000) = 1/(50000 / 65211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6640129 / 25000000) (265605161 / 1000000000) (Real.log (65211 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (65211 / 50000) = -Real.log (50000 / 65211) := by
    rw [show ((65211 / 50000) : ℝ) = ((50000 / 65211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2267011 / 6250000) ≤ -Real.log (34789 / 50000) ∧
    -Real.log (34789 / 50000) ≤ (362721761 / 1000000000) := by
  have h := checkLog_sound (w := (15211 / 84789)) (n := 12)
    (lo := (2267011 / 6250000)) (hi := (362721761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34789) = 1/(34789 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-362721761 / 1000000000) (-2267011 / 6250000) (Real.log (34789 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (17393061 / 20000000) ≤ -Real.log (31250000000 / 74565089401) ∧
    -Real.log (31250000000 / 74565089401) ≤ (217413263 / 250000000) := by
  have h := checkLog_sound (w := (12065089401 / 137065089401)) (n := 12)
    (lo := (17650587 / 100000000)) (hi := (176505871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74565089401 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(74565089401 / 62500000000) = 1/(31250000000 / 74565089401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17393061 / 20000000) (217413263 / 250000000) (Real.log (74565089401 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (74565089401 / 31250000000) = -Real.log (31250000000 / 74565089401) := by
    rw [show ((74565089401 / 31250000000) : ℝ) = ((31250000000 / 74565089401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (871753817 / 1000000000) ≤ -Real.log (125000000000 / 298887591793) ∧
    -Real.log (125000000000 / 298887591793) ≤ (871753819 / 1000000000) := by
  have h := checkLog_sound (w := (48887591793 / 548887591793)) (n := 12)
    (lo := (178606637 / 1000000000)) (hi := (89303319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298887591793 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(298887591793 / 250000000000) = 1/(125000000000 / 298887591793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (871753817 / 1000000000) (871753819 / 1000000000) (Real.log (298887591793 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (298887591793 / 125000000000) = -Real.log (125000000000 / 298887591793) := by
    rw [show ((298887591793 / 125000000000) : ℝ) = ((125000000000 / 298887591793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (313380133 / 500000000) ≤ -Real.log (100000000000 / 187153746423) ∧
    -Real.log (100000000000 / 187153746423) ≤ (626760267 / 1000000000) := by
  have h := checkLog_sound (w := (87153746423 / 287153746423)) (n := 12)
    (lo := (313380133 / 500000000)) (hi := (626760267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187153746423 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187153746423 / 100000000000) = 1/(100000000000 / 187153746423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (313380133 / 500000000) (626760267 / 1000000000) (Real.log (187153746423 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (187153746423 / 100000000000) = -Real.log (100000000000 / 187153746423) := by
    rw [show ((187153746423 / 100000000000) : ℝ) = ((100000000000 / 187153746423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (628326921 / 1000000000) ≤ -Real.log (250000000000 / 468617953951) ∧
    -Real.log (250000000000 / 468617953951) ≤ (314163461 / 500000000) := by
  have h := checkLog_sound (w := (218617953951 / 718617953951)) (n := 12)
    (lo := (628326921 / 1000000000)) (hi := (314163461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((468617953951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(468617953951 / 250000000000) = 1/(250000000000 / 468617953951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (628326921 / 1000000000) (314163461 / 500000000) (Real.log (468617953951 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (468617953951 / 250000000000) = -Real.log (250000000000 / 468617953951) := by
    rw [show ((468617953951 / 250000000000) : ℝ) = ((250000000000 / 468617953951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0232
