import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0248
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

theorem reflection_log_1_neg : (121932437 / 500000000) ≤ -Real.log (2560 / 3267) ∧
    -Real.log (2560 / 3267) ≤ (1950919 / 8000000) := by
  have h := checkLog_sound (w := (707 / 5827)) (n := 12)
    (lo := (121932437 / 500000000)) (hi := (1950919 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3267 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3267 / 2560) = 1/(2560 / 3267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121932437 / 500000000) (1950919 / 8000000) (Real.log (3267 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3267 / 2560) = -Real.log (2560 / 3267) := by
    rw [show ((3267 / 2560) : ℝ) = ((2560 / 3267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (323201311 / 1000000000) ≤ -Real.log (1853 / 2560) ∧
    -Real.log (1853 / 2560) ≤ (10100041 / 31250000) := by
  have h := checkLog_sound (w := (707 / 4413)) (n := 12)
    (lo := (323201311 / 1000000000)) (hi := (10100041 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1853) = 1/(1853 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10100041 / 31250000) (-323201311 / 1000000000) (Real.log (1853 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (243405631 / 1000000000) ≤ -Real.log (5120 / 6531) ∧
    -Real.log (5120 / 6531) ≤ (3803213 / 15625000) := by
  have h := checkLog_sound (w := (1411 / 11651)) (n := 12)
    (lo := (243405631 / 1000000000)) (hi := (3803213 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6531 / 5120) = 1/(5120 / 6531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (243405631 / 1000000000) (3803213 / 15625000) (Real.log (6531 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6531 / 5120) = -Real.log (5120 / 6531) := by
    rw [show ((6531 / 5120) : ℝ) = ((5120 / 6531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16119607 / 50000000) ≤ -Real.log (3709 / 5120) ∧
    -Real.log (3709 / 5120) ≤ (322392141 / 1000000000) := by
  have h := checkLog_sound (w := (1411 / 8829)) (n := 12)
    (lo := (16119607 / 50000000)) (hi := (322392141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3709) = 1/(3709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-322392141 / 1000000000) (-16119607 / 50000000) (Real.log (3709 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87953177 / 200000000) ≤ -Real.log (1280 / 1987) ∧
    -Real.log (1280 / 1987) ≤ (219882943 / 500000000) := by
  have h := checkLog_sound (w := (707 / 3267)) (n := 12)
    (lo := (87953177 / 200000000)) (hi := (219882943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1280) = 1/(1280 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87953177 / 200000000) (219882943 / 500000000) (Real.log (1987 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1987 / 1280) = -Real.log (1280 / 1987) := by
    rw [show ((1987 / 1280) : ℝ) = ((1280 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (803729639 / 1000000000) ≤ -Real.log (573 / 1280) ∧
    -Real.log (573 / 1280) ≤ (803729641 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 573) = 1/(573 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-803729641 / 1000000000) (-803729639 / 1000000000) (Real.log (573 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (439010693 / 1000000000) ≤ -Real.log (2560 / 3971) ∧
    -Real.log (2560 / 3971) ≤ (219505347 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 6531)) (n := 12)
    (lo := (439010693 / 1000000000)) (hi := (219505347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3971 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3971 / 2560) = 1/(2560 / 3971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (439010693 / 1000000000) (219505347 / 500000000) (Real.log (3971 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3971 / 2560) = -Real.log (2560 / 3971) := by
    rw [show ((3971 / 2560) : ℝ) = ((2560 / 3971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (801115259 / 1000000000) ≤ -Real.log (1149 / 2560) ∧
    -Real.log (1149 / 2560) ≤ (801115261 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 2429)) (n := 12)
    (lo := (107968079 / 1000000000)) (hi := (1349601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1149) = 1/(1149 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-801115261 / 1000000000) (-801115259 / 1000000000) (Real.log (1149 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (333194011 / 1000000000) ≤ -Real.log (500000 / 697709) ∧
    -Real.log (500000 / 697709) ≤ (83298503 / 250000000) := by
  have h := checkLog_sound (w := (197709 / 1197709)) (n := 12)
    (lo := (333194011 / 1000000000)) (hi := (83298503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697709 / 500000) = 1/(500000 / 697709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (333194011 / 1000000000) (83298503 / 250000000) (Real.log (697709 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (697709 / 500000) = -Real.log (500000 / 697709) := by
    rw [show ((697709 / 500000) : ℝ) = ((500000 / 697709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31451123 / 62500000) ≤ -Real.log (302291 / 500000) ∧
    -Real.log (302291 / 500000) ≤ (503217969 / 1000000000) := by
  have h := checkLog_sound (w := (197709 / 802291)) (n := 12)
    (lo := (31451123 / 62500000)) (hi := (503217969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 302291) = 1/(302291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-503217969 / 1000000000) (-31451123 / 62500000) (Real.log (302291 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166908643 / 500000000) ≤ -Real.log (15625 / 21817) ∧
    -Real.log (15625 / 21817) ≤ (333817287 / 1000000000) := by
  have h := checkLog_sound (w := (3096 / 18721)) (n := 12)
    (lo := (166908643 / 500000000)) (hi := (333817287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21817 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21817 / 15625) = 1/(15625 / 21817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166908643 / 500000000) (333817287 / 1000000000) (Real.log (21817 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21817 / 15625) = -Real.log (15625 / 21817) := by
    rw [show ((21817 / 15625) : ℝ) = ((15625 / 21817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100931603 / 200000000) ≤ -Real.log (9433 / 15625) ∧
    -Real.log (9433 / 15625) ≤ (15770563 / 31250000) := by
  have h := checkLog_sound (w := (3096 / 12529)) (n := 12)
    (lo := (100931603 / 200000000)) (hi := (15770563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 9433) = 1/(9433 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15770563 / 31250000) (-100931603 / 200000000) (Real.log (9433 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256374051 / 1000000000) ≤ -Real.log (250000 / 323059) ∧
    -Real.log (250000 / 323059) ≤ (64093513 / 250000000) := by
  have h := checkLog_sound (w := (73059 / 573059)) (n := 12)
    (lo := (256374051 / 1000000000)) (hi := (64093513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323059 / 250000) = 1/(250000 / 323059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256374051 / 1000000000) (64093513 / 250000000) (Real.log (323059 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (323059 / 250000) = -Real.log (250000 / 323059) := by
    rw [show ((323059 / 250000) : ℝ) = ((250000 / 323059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172822287 / 500000000) ≤ -Real.log (176941 / 250000) ∧
    -Real.log (176941 / 250000) ≤ (13825783 / 40000000) := by
  have h := checkLog_sound (w := (73059 / 426941)) (n := 12)
    (lo := (172822287 / 500000000)) (hi := (13825783 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 176941) = 1/(176941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13825783 / 40000000) (-172822287 / 500000000) (Real.log (176941 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (128458187 / 500000000) ≤ -Real.log (1000000 / 1292937) ∧
    -Real.log (1000000 / 1292937) ≤ (2055331 / 8000000) := by
  have h := checkLog_sound (w := (292937 / 2292937)) (n := 12)
    (lo := (128458187 / 500000000)) (hi := (2055331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292937 / 1000000) = 1/(1000000 / 1292937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (128458187 / 500000000) (2055331 / 8000000) (Real.log (1292937 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1292937 / 1000000) = -Real.log (1000000 / 1292937) := by
    rw [show ((1292937 / 1000000) : ℝ) = ((1000000 / 1292937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (86658877 / 250000000) ≤ -Real.log (707063 / 1000000) ∧
    -Real.log (707063 / 1000000) ≤ (346635509 / 1000000000) := by
  have h := checkLog_sound (w := (292937 / 1707063)) (n := 12)
    (lo := (86658877 / 250000000)) (hi := (346635509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707063) = 1/(707063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-346635509 / 1000000000) (-86658877 / 250000000) (Real.log (707063 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (41820599 / 50000000) ≤ -Real.log (500000000000 / 1154035350043) ∧
    -Real.log (500000000000 / 1154035350043) ≤ (418205991 / 500000000) := by
  have h := checkLog_sound (w := (154035350043 / 2154035350043)) (n := 12)
    (lo := (179081 / 1250000)) (hi := (143264801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154035350043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1154035350043 / 1000000000000) = 1/(500000000000 / 1154035350043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (41820599 / 50000000) (418205991 / 500000000) (Real.log (1154035350043 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1154035350043 / 500000000000) = -Real.log (500000000000 / 1154035350043) := by
    rw [show ((1154035350043 / 500000000000) : ℝ) = ((500000000000 / 1154035350043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (419237651 / 500000000) ≤ -Real.log (250000000000 / 578209477367) ∧
    -Real.log (250000000000 / 578209477367) ≤ (104809413 / 125000000) := by
  have h := checkLog_sound (w := (78209477367 / 1078209477367)) (n := 12)
    (lo := (72664061 / 500000000)) (hi := (145328123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578209477367 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(578209477367 / 500000000000) = 1/(250000000000 / 578209477367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (419237651 / 500000000) (104809413 / 125000000) (Real.log (578209477367 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (578209477367 / 250000000000) = -Real.log (250000000000 / 578209477367) := by
    rw [show ((578209477367 / 250000000000) : ℝ) = ((250000000000 / 578209477367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4816149 / 8000000) ≤ -Real.log (15625000000 / 28528135791) ∧
    -Real.log (15625000000 / 28528135791) ≤ (301009313 / 500000000) := by
  have h := checkLog_sound (w := (12903135791 / 44153135791)) (n := 12)
    (lo := (4816149 / 8000000)) (hi := (301009313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28528135791 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28528135791 / 15625000000) = 1/(15625000000 / 28528135791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4816149 / 8000000) (301009313 / 500000000) (Real.log (28528135791 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28528135791 / 15625000000) = -Real.log (15625000000 / 28528135791) := by
    rw [show ((28528135791 / 15625000000) : ℝ) = ((15625000000 / 28528135791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (301775941 / 500000000) ≤ -Real.log (500000000000 / 914301130169) ∧
    -Real.log (500000000000 / 914301130169) ≤ (603551883 / 1000000000) := by
  have h := checkLog_sound (w := (414301130169 / 1414301130169)) (n := 12)
    (lo := (301775941 / 500000000)) (hi := (603551883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914301130169 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914301130169 / 500000000000) = 1/(500000000000 / 914301130169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (301775941 / 500000000) (603551883 / 1000000000) (Real.log (914301130169 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (914301130169 / 500000000000) = -Real.log (500000000000 / 914301130169) := by
    rw [show ((914301130169 / 500000000000) : ℝ) = ((500000000000 / 914301130169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0248
