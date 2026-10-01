import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216
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

theorem reflection_log_1_neg : (134534189 / 250000000) ≤ -Real.log (3200 / 5481) ∧
    -Real.log (3200 / 5481) ≤ (538136757 / 1000000000) := by
  have h := checkLog_sound (w := (2281 / 8681)) (n := 12)
    (lo := (134534189 / 250000000)) (hi := (538136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5481 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5481 / 3200) = 1/(3200 / 5481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134534189 / 250000000) (538136757 / 1000000000) (Real.log (5481 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5481 / 3200) = -Real.log (3200 / 5481) := by
    rw [show ((5481 / 3200) : ℝ) = ((3200 / 5481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249523993 / 200000000) ≤ -Real.log (919 / 3200) ∧
    -Real.log (919 / 3200) ≤ (1247619967 / 1000000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 919) = 1/(919 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1247619967 / 1000000000) (-249523993 / 200000000) (Real.log (919 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (534664213 / 1000000000) ≤ -Real.log (1600 / 2731) ∧
    -Real.log (1600 / 2731) ≤ (267332107 / 500000000) := by
  have h := checkLog_sound (w := (1131 / 4331)) (n := 12)
    (lo := (534664213 / 1000000000)) (hi := (267332107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2731 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2731 / 1600) = 1/(1600 / 2731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (534664213 / 1000000000) (267332107 / 500000000) (Real.log (2731 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2731 / 1600) = -Real.log (1600 / 2731) := by
    rw [show ((2731 / 1600) : ℝ) = ((1600 / 2731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1227156139 / 1000000000) ≤ -Real.log (469 / 1600) ∧
    -Real.log (469 / 1600) ≤ (1227156141 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 469) = 1/(469 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1227156141 / 1000000000) (-1227156139 / 1000000000) (Real.log (469 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177305157 / 500000000) ≤ -Real.log (1600 / 2281) ∧
    -Real.log (1600 / 2281) ≤ (70922063 / 200000000) := by
  have h := checkLog_sound (w := (681 / 3881)) (n := 12)
    (lo := (177305157 / 500000000)) (hi := (70922063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2281 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2281 / 1600) = 1/(1600 / 2281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177305157 / 500000000) (70922063 / 200000000) (Real.log (2281 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2281 / 1600) = -Real.log (1600 / 2281) := by
    rw [show ((2281 / 1600) : ℝ) = ((1600 / 2281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110894557 / 200000000) ≤ -Real.log (919 / 1600) ∧
    -Real.log (919 / 1600) ≤ (277236393 / 500000000) := by
  have h := checkLog_sound (w := (681 / 2519)) (n := 12)
    (lo := (110894557 / 200000000)) (hi := (277236393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 919) = 1/(919 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277236393 / 500000000) (-110894557 / 200000000) (Real.log (919 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86561437 / 250000000) ≤ -Real.log (800 / 1131) ∧
    -Real.log (800 / 1131) ≤ (346245749 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1931)) (n := 12)
    (lo := (86561437 / 250000000)) (hi := (346245749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131 / 800) = 1/(800 / 1131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86561437 / 250000000) (346245749 / 1000000000) (Real.log (1131 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1131 / 800) = -Real.log (800 / 1131) := by
    rw [show ((1131 / 800) : ℝ) = ((800 / 1131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (534008959 / 1000000000) ≤ -Real.log (469 / 800) ∧
    -Real.log (469 / 800) ≤ (834389 / 1562500) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 469) = 1/(469 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-834389 / 1562500) (-534008959 / 1000000000) (Real.log (469 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (119774333 / 200000000) ≤ -Real.log (31250 / 56877) ∧
    -Real.log (31250 / 56877) ≤ (299435833 / 500000000) := by
  have h := checkLog_sound (w := (25627 / 88127)) (n := 12)
    (lo := (119774333 / 200000000)) (hi := (299435833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56877 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56877 / 31250) = 1/(31250 / 56877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (119774333 / 200000000) (299435833 / 500000000) (Real.log (56877 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (56877 / 31250) = -Real.log (31250 / 56877) := by
    rw [show ((56877 / 31250) : ℝ) = ((31250 / 56877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (343030809 / 200000000) ≤ -Real.log (5623 / 31250) ∧
    -Real.log (5623 / 31250) ≤ (13399641 / 7812500) := by
  have h := checkLog_sound (w := (4379 / 26871)) (n := 12)
    (lo := (65771937 / 200000000)) (hi := (164429843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11246) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11246) = 1/(5623 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13399641 / 7812500) (-343030809 / 200000000) (Real.log (5623 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (600129071 / 1000000000) ≤ -Real.log (500000 / 911177) ∧
    -Real.log (500000 / 911177) ≤ (37508067 / 62500000) := by
  have h := checkLog_sound (w := (411177 / 1411177)) (n := 12)
    (lo := (600129071 / 1000000000)) (hi := (37508067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911177 / 500000) = 1/(500000 / 911177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (600129071 / 1000000000) (37508067 / 62500000) (Real.log (911177 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (911177 / 500000) = -Real.log (500000 / 911177) := by
    rw [show ((911177 / 500000) : ℝ) = ((500000 / 911177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1727962471 / 1000000000) ≤ -Real.log (88823 / 500000) ∧
    -Real.log (88823 / 500000) ≤ (863981237 / 500000000) := by
  have h := checkLog_sound (w := (36177 / 213823)) (n := 12)
    (lo := (341668111 / 1000000000)) (hi := (21354257 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 88823) = 1/(88823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-863981237 / 500000000) (-1727962471 / 1000000000) (Real.log (88823 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72679009 / 125000000) ≤ -Real.log (500000 / 894299) ∧
    -Real.log (500000 / 894299) ≤ (581432073 / 1000000000) := by
  have h := checkLog_sound (w := (394299 / 1394299)) (n := 12)
    (lo := (72679009 / 125000000)) (hi := (581432073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894299 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894299 / 500000) = 1/(500000 / 894299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72679009 / 125000000) (581432073 / 1000000000) (Real.log (894299 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (894299 / 500000) = -Real.log (500000 / 894299) := by
    rw [show ((894299 / 500000) : ℝ) = ((500000 / 894299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1553993743 / 1000000000) ≤ -Real.log (105701 / 500000) ∧
    -Real.log (105701 / 500000) ≤ (776996873 / 500000000) := by
  have h := checkLog_sound (w := (19299 / 230701)) (n := 12)
    (lo := (167699383 / 1000000000)) (hi := (20962423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105701) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 105701) = 1/(105701 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-776996873 / 500000000) (-1553993743 / 1000000000) (Real.log (105701 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (583582283 / 1000000000) ≤ -Real.log (15625 / 28007) ∧
    -Real.log (15625 / 28007) ≤ (145895571 / 250000000) := by
  have h := checkLog_sound (w := (6191 / 21816)) (n := 12)
    (lo := (583582283 / 1000000000)) (hi := (145895571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28007 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28007 / 15625) = 1/(15625 / 28007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (583582283 / 1000000000) (145895571 / 250000000) (Real.log (28007 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (28007 / 15625) = -Real.log (15625 / 28007) := by
    rw [show ((28007 / 15625) : ℝ) = ((15625 / 28007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1572373367 / 1000000000) ≤ -Real.log (3243 / 15625) ∧
    -Real.log (3243 / 15625) ≤ (157237337 / 100000000) := by
  have h := checkLog_sound (w := (2653 / 28597)) (n := 12)
    (lo := (186079007 / 1000000000)) (hi := (5814969 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12972) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 12972) = 1/(3243 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-157237337 / 100000000) (-1572373367 / 1000000000) (Real.log (3243 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (231402571 / 100000000) ≤ -Real.log (500000000000 / 5057531566779) ∧
    -Real.log (500000000000 / 5057531566779) ≤ (1157012857 / 500000000) := by
  have h := checkLog_sound (w := (1057531566779 / 9057531566779)) (n := 12)
    (lo := (23458417 / 100000000)) (hi := (234584171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5057531566779 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5057531566779 / 4000000000000) = 1/(500000000000 / 5057531566779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (231402571 / 100000000) (1157012857 / 500000000) (Real.log (5057531566779 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5057531566779 / 500000000000) = -Real.log (500000000000 / 5057531566779) := by
    rw [show ((5057531566779 / 500000000000) : ℝ) = ((500000000000 / 5057531566779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2328091543 / 1000000000) ≤ -Real.log (31250000000 / 320573289013) ∧
    -Real.log (31250000000 / 320573289013) ≤ (2328091547 / 1000000000) := by
  have h := checkLog_sound (w := (70573289013 / 570573289013)) (n := 12)
    (lo := (248650003 / 1000000000)) (hi := (62162501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320573289013 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320573289013 / 250000000000) = 1/(31250000000 / 320573289013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2328091543 / 1000000000) (2328091547 / 1000000000) (Real.log (320573289013 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (320573289013 / 31250000000) = -Real.log (31250000000 / 320573289013) := by
    rw [show ((320573289013 / 31250000000) : ℝ) = ((31250000000 / 320573289013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (427085163 / 200000000) ≤ -Real.log (500000000000 / 4230324216421) ∧
    -Real.log (500000000000 / 4230324216421) ≤ (2135425819 / 1000000000) := by
  have h := checkLog_sound (w := (230324216421 / 8230324216421)) (n := 12)
    (lo := (2239371 / 40000000)) (hi := (13996069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4230324216421 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4230324216421 / 4000000000000) = 1/(500000000000 / 4230324216421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (427085163 / 200000000) (2135425819 / 1000000000) (Real.log (4230324216421 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4230324216421 / 500000000000) = -Real.log (500000000000 / 4230324216421) := by
    rw [show ((4230324216421 / 500000000000) : ℝ) = ((500000000000 / 4230324216421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2155955649 / 1000000000) ≤ -Real.log (6250000000 / 53975871107) ∧
    -Real.log (6250000000 / 53975871107) ≤ (2155955653 / 1000000000) := by
  have h := checkLog_sound (w := (3975871107 / 103975871107)) (n := 12)
    (lo := (76514109 / 1000000000)) (hi := (7651411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53975871107 / 50000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(53975871107 / 50000000000) = 1/(6250000000 / 53975871107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2155955649 / 1000000000) (2155955653 / 1000000000) (Real.log (53975871107 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (53975871107 / 6250000000) = -Real.log (6250000000 / 53975871107) := by
    rw [show ((53975871107 / 6250000000) : ℝ) = ((6250000000 / 53975871107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216
