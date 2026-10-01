import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell098
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (10740209 / 40000000) ≤ -Real.log (5120 / 6697) ∧
    -Real.log (5120 / 6697) ≤ (134252613 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 11817)) (n := 12)
    (lo := (10740209 / 40000000)) (hi := (134252613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6697 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6697 / 5120) = 1/(5120 / 6697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10740209 / 40000000) (134252613 / 500000000) (Real.log (6697 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6697 / 5120) = -Real.log (5120 / 6697) := by
    rw [show ((6697 / 5120) : ℝ) = ((5120 / 6697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (368180613 / 1000000000) ≤ -Real.log (3543 / 5120) ∧
    -Real.log (3543 / 5120) ≤ (184090307 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 8663)) (n := 12)
    (lo := (368180613 / 1000000000)) (hi := (184090307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3543) = 1/(3543 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-184090307 / 500000000) (-368180613 / 1000000000) (Real.log (3543 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (268057163 / 1000000000) ≤ -Real.log (2560 / 3347) ∧
    -Real.log (2560 / 3347) ≤ (67014291 / 250000000) := by
  have h := checkLog_sound (w := (787 / 5907)) (n := 12)
    (lo := (268057163 / 1000000000)) (hi := (67014291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3347 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3347 / 2560) = 1/(2560 / 3347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (268057163 / 1000000000) (67014291 / 250000000) (Real.log (3347 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3347 / 2560) = -Real.log (2560 / 3347) := by
    rw [show ((3347 / 2560) : ℝ) = ((2560 / 3347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (367334231 / 1000000000) ≤ -Real.log (1773 / 2560) ∧
    -Real.log (1773 / 2560) ≤ (45916779 / 125000000) := by
  have h := checkLog_sound (w := (787 / 4333)) (n := 12)
    (lo := (367334231 / 1000000000)) (hi := (45916779 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1773) = 1/(1773 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45916779 / 125000000) (-367334231 / 1000000000) (Real.log (1773 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616977 / 3125000) ≤ -Real.log (1000000 / 1218271) ∧
    -Real.log (1000000 / 1218271) ≤ (197432641 / 1000000000) := by
  have h := checkLog_sound (w := (218271 / 2218271)) (n := 12)
    (lo := (616977 / 3125000)) (hi := (197432641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218271 / 1000000) = 1/(1000000 / 1218271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616977 / 3125000) (197432641 / 1000000000) (Real.log (1218271 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1218271 / 1000000) = -Real.log (1000000 / 1218271) := by
    rw [show ((1218271 / 1000000) : ℝ) = ((1000000 / 1218271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (49249429 / 200000000) ≤ -Real.log (781729 / 1000000) ∧
    -Real.log (781729 / 1000000) ≤ (123123573 / 500000000) := by
  have h := checkLog_sound (w := (218271 / 1781729)) (n := 12)
    (lo := (49249429 / 200000000)) (hi := (123123573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781729) = 1/(781729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-123123573 / 500000000) (-49249429 / 200000000) (Real.log (781729 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197777331 / 1000000000) ≤ -Real.log (1000000 / 1218691) ∧
    -Real.log (1000000 / 1218691) ≤ (49444333 / 250000000) := by
  have h := checkLog_sound (w := (218691 / 2218691)) (n := 12)
    (lo := (197777331 / 1000000000)) (hi := (49444333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218691 / 1000000) = 1/(1000000 / 1218691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197777331 / 1000000000) (49444333 / 250000000) (Real.log (1218691 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1218691 / 1000000) = -Real.log (1000000 / 1218691) := by
    rw [show ((1218691 / 1000000) : ℝ) = ((1000000 / 1218691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3084807 / 12500000) ≤ -Real.log (781309 / 1000000) ∧
    -Real.log (781309 / 1000000) ≤ (246784561 / 1000000000) := by
  have h := checkLog_sound (w := (218691 / 1781309)) (n := 12)
    (lo := (3084807 / 12500000)) (hi := (246784561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781309) = 1/(781309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-246784561 / 1000000000) (-3084807 / 12500000) (Real.log (781309 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145316919 / 1000000000) ≤ -Real.log (500000 / 578203) ∧
    -Real.log (500000 / 578203) ≤ (3632923 / 25000000) := by
  have h := checkLog_sound (w := (78203 / 1078203)) (n := 12)
    (lo := (145316919 / 1000000000)) (hi := (3632923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578203 / 500000) = 1/(500000 / 578203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145316919 / 1000000000) (3632923 / 25000000) (Real.log (578203 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (578203 / 500000) = -Real.log (500000 / 578203) := by
    rw [show ((578203 / 500000) : ℝ) = ((500000 / 578203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (85041971 / 500000000) ≤ -Real.log (421797 / 500000) ∧
    -Real.log (421797 / 500000) ≤ (170083943 / 1000000000) := by
  have h := checkLog_sound (w := (78203 / 921797)) (n := 12)
    (lo := (85041971 / 500000000)) (hi := (170083943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421797) = 1/(421797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170083943 / 1000000000) (-85041971 / 500000000) (Real.log (421797 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145584091 / 1000000000) ≤ -Real.log (200000 / 231343) ∧
    -Real.log (200000 / 231343) ≤ (36396023 / 250000000) := by
  have h := checkLog_sound (w := (31343 / 431343)) (n := 12)
    (lo := (145584091 / 1000000000)) (hi := (36396023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231343 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231343 / 200000) = 1/(200000 / 231343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145584091 / 1000000000) (36396023 / 250000000) (Real.log (231343 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (231343 / 200000) = -Real.log (200000 / 231343) := by
    rw [show ((231343 / 200000) : ℝ) = ((200000 / 231343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170450299 / 1000000000) ≤ -Real.log (168657 / 200000) ∧
    -Real.log (168657 / 200000) ≤ (1704503 / 10000000) := by
  have h := checkLog_sound (w := (31343 / 368657)) (n := 12)
    (lo := (170450299 / 1000000000)) (hi := (1704503 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168657) = 1/(168657 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1704503 / 10000000) (-170450299 / 1000000000) (Real.log (168657 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (127078279 / 200000000) ≤ -Real.log (125000000000 / 235970107163) ∧
    -Real.log (125000000000 / 235970107163) ≤ (158847849 / 250000000) := by
  have h := checkLog_sound (w := (110970107163 / 360970107163)) (n := 12)
    (lo := (127078279 / 200000000)) (hi := (158847849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235970107163 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235970107163 / 125000000000) = 1/(125000000000 / 235970107163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (127078279 / 200000000) (158847849 / 250000000) (Real.log (235970107163 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (235970107163 / 125000000000) = -Real.log (125000000000 / 235970107163) := by
    rw [show ((235970107163 / 125000000000) : ℝ) = ((125000000000 / 235970107163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (636685839 / 1000000000) ≤ -Real.log (12500000000 / 23627575501) ∧
    -Real.log (12500000000 / 23627575501) ≤ (7958573 / 12500000) := by
  have h := checkLog_sound (w := (11127575501 / 36127575501)) (n := 12)
    (lo := (636685839 / 1000000000)) (hi := (7958573 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23627575501 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23627575501 / 12500000000) = 1/(12500000000 / 23627575501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (636685839 / 1000000000) (7958573 / 12500000) (Real.log (23627575501 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (23627575501 / 12500000000) = -Real.log (12500000000 / 23627575501) := by
    rw [show ((23627575501 / 12500000000) : ℝ) = ((12500000000 / 23627575501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (221839893 / 500000000) ≤ -Real.log (500000000000 / 779215687277) ∧
    -Real.log (500000000000 / 779215687277) ≤ (443679787 / 1000000000) := by
  have h := checkLog_sound (w := (279215687277 / 1279215687277)) (n := 12)
    (lo := (221839893 / 500000000)) (hi := (443679787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779215687277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779215687277 / 500000000000) = 1/(500000000000 / 779215687277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (221839893 / 500000000) (443679787 / 1000000000) (Real.log (779215687277 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (779215687277 / 500000000000) = -Real.log (500000000000 / 779215687277) := by
    rw [show ((779215687277 / 500000000000) : ℝ) = ((500000000000 / 779215687277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (111140473 / 250000000) ≤ -Real.log (5000000000 / 7799033417) ∧
    -Real.log (5000000000 / 7799033417) ≤ (444561893 / 1000000000) := by
  have h := checkLog_sound (w := (2799033417 / 12799033417)) (n := 12)
    (lo := (111140473 / 250000000)) (hi := (444561893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7799033417 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7799033417 / 5000000000) = 1/(5000000000 / 7799033417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (111140473 / 250000000) (444561893 / 1000000000) (Real.log (7799033417 / 5000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (7799033417 / 5000000000) = -Real.log (5000000000 / 7799033417) := by
    rw [show ((7799033417 / 5000000000) : ℝ) = ((5000000000 / 7799033417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (157700431 / 500000000) ≤ -Real.log (250000000000 / 342702176639) ∧
    -Real.log (250000000000 / 342702176639) ≤ (315400863 / 1000000000) := by
  have h := checkLog_sound (w := (92702176639 / 592702176639)) (n := 12)
    (lo := (157700431 / 500000000)) (hi := (315400863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342702176639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342702176639 / 250000000000) = 1/(250000000000 / 342702176639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (157700431 / 500000000) (315400863 / 1000000000) (Real.log (342702176639 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (342702176639 / 250000000000) = -Real.log (250000000000 / 342702176639) := by
    rw [show ((342702176639 / 250000000000) : ℝ) = ((250000000000 / 342702176639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (31603439 / 100000000) ≤ -Real.log (500000000000 / 685838714077) ∧
    -Real.log (500000000000 / 685838714077) ≤ (316034391 / 1000000000) := by
  have h := checkLog_sound (w := (185838714077 / 1185838714077)) (n := 12)
    (lo := (31603439 / 100000000)) (hi := (316034391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685838714077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685838714077 / 500000000000) = 1/(500000000000 / 685838714077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (31603439 / 100000000) (316034391 / 1000000000) (Real.log (685838714077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (685838714077 / 500000000000) = -Real.log (500000000000 / 685838714077) := by
    rw [show ((685838714077 / 500000000000) : ℝ) = ((500000000000 / 685838714077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (777069 / 31250000) ≤ -Real.log (39017616351 / 40000000000) ∧
    -Real.log (39017616351 / 40000000000) ≤ (24866209 / 1000000000) := by
  have h := checkLog_sound (w := (982383649 / 79017616351)) (n := 12)
    (lo := (777069 / 31250000)) (hi := (24866209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39017616351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39017616351) = 1/(39017616351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24866209 / 1000000000) (-777069 / 31250000) (Real.log (39017616351 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24767023 / 1000000000) ≤ -Real.log (243884290791 / 250000000000) ∧
    -Real.log (243884290791 / 250000000000) ≤ (1547939 / 62500000) := by
  have h := checkLog_sound (w := (6115709209 / 493884290791)) (n := 12)
    (lo := (24767023 / 1000000000)) (hi := (1547939 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243884290791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243884290791) = 1/(243884290791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1547939 / 62500000) (-24767023 / 1000000000) (Real.log (243884290791 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell098
