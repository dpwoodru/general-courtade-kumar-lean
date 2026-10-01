import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019
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

theorem reflection_log_1_neg : (116237439 / 500000000) ≤ -Real.log (256 / 323) ∧
    -Real.log (256 / 323) ≤ (232474879 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 579)) (n := 12)
    (lo := (116237439 / 500000000)) (hi := (232474879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 256) = 1/(256 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116237439 / 500000000) (232474879 / 1000000000) (Real.log (323 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (323 / 256) = -Real.log (256 / 323) := by
    rw [show ((323 / 256) : ℝ) = ((256 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303430429 / 1000000000) ≤ -Real.log (189 / 256) ∧
    -Real.log (189 / 256) ≤ (30343043 / 100000000) := by
  have h := checkLog_sound (w := (67 / 445)) (n := 12)
    (lo := (303430429 / 1000000000)) (hi := (30343043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 189) = 1/(189 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30343043 / 100000000) (-303430429 / 1000000000) (Real.log (189 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116005187 / 500000000) ≤ -Real.log (5120 / 6457) ∧
    -Real.log (5120 / 6457) ≤ (1856083 / 8000000) := by
  have h := checkLog_sound (w := (1337 / 11577)) (n := 12)
    (lo := (116005187 / 500000000)) (hi := (1856083 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6457 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6457 / 5120) = 1/(5120 / 6457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116005187 / 500000000) (1856083 / 8000000) (Real.log (6457 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6457 / 5120) = -Real.log (5120 / 6457) := by
    rw [show ((6457 / 5120) : ℝ) = ((5120 / 6457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302637093 / 1000000000) ≤ -Real.log (3783 / 5120) ∧
    -Real.log (3783 / 5120) ≤ (151318547 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 8903)) (n := 12)
    (lo := (302637093 / 1000000000)) (hi := (151318547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3783) = 1/(3783 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) (Real.log (3783 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169901411 / 1000000000) ≤ -Real.log (250000 / 296297) ∧
    -Real.log (250000 / 296297) ≤ (42475353 / 250000000) := by
  have h := checkLog_sound (w := (46297 / 546297)) (n := 12)
    (lo := (169901411 / 1000000000)) (hi := (42475353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296297 / 250000) = 1/(250000 / 296297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169901411 / 1000000000) (42475353 / 250000000) (Real.log (296297 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (296297 / 250000) = -Real.log (250000 / 296297) := by
    rw [show ((296297 / 250000) : ℝ) = ((250000 / 296297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (204797867 / 1000000000) ≤ -Real.log (203703 / 250000) ∧
    -Real.log (203703 / 250000) ≤ (51199467 / 250000000) := by
  have h := checkLog_sound (w := (46297 / 453703)) (n := 12)
    (lo := (204797867 / 1000000000)) (hi := (51199467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203703) = 1/(203703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-51199467 / 250000000) (-204797867 / 1000000000) (Real.log (203703 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (170254879 / 1000000000) ≤ -Real.log (1000000 / 1185607) ∧
    -Real.log (1000000 / 1185607) ≤ (1064093 / 6250000) := by
  have h := checkLog_sound (w := (185607 / 2185607)) (n := 12)
    (lo := (170254879 / 1000000000)) (hi := (1064093 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185607 / 1000000) = 1/(1000000 / 1185607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (170254879 / 1000000000) (1064093 / 6250000) (Real.log (1185607 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1185607 / 1000000) = -Real.log (1000000 / 1185607) := by
    rw [show ((1185607 / 1000000) : ℝ) = ((1000000 / 1185607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51328057 / 250000000) ≤ -Real.log (814393 / 1000000) ∧
    -Real.log (814393 / 1000000) ≤ (205312229 / 1000000000) := by
  have h := checkLog_sound (w := (185607 / 1814393)) (n := 12)
    (lo := (51328057 / 250000000)) (hi := (205312229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814393) = 1/(814393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-205312229 / 1000000000) (-51328057 / 250000000) (Real.log (814393 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4966647 / 40000000) ≤ -Real.log (250000 / 283051) ∧
    -Real.log (250000 / 283051) ≤ (3880193 / 31250000) := by
  have h := checkLog_sound (w := (33051 / 533051)) (n := 12)
    (lo := (4966647 / 40000000)) (hi := (3880193 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283051 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283051 / 250000) = 1/(250000 / 283051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4966647 / 40000000) (3880193 / 31250000) (Real.log (283051 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (283051 / 250000) = -Real.log (250000 / 283051) := by
    rw [show ((283051 / 250000) : ℝ) = ((250000 / 283051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70899307 / 500000000) ≤ -Real.log (216949 / 250000) ∧
    -Real.log (216949 / 250000) ≤ (28359723 / 200000000) := by
  have h := checkLog_sound (w := (33051 / 466949)) (n := 12)
    (lo := (70899307 / 500000000)) (hi := (28359723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 216949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 216949) = 1/(216949 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28359723 / 200000000) (-70899307 / 500000000) (Real.log (216949 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15554551 / 125000000) ≤ -Real.log (100000 / 113251) ∧
    -Real.log (100000 / 113251) ≤ (124436409 / 1000000000) := by
  have h := checkLog_sound (w := (13251 / 213251)) (n := 12)
    (lo := (15554551 / 125000000)) (hi := (124436409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113251 / 100000) = 1/(100000 / 113251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15554551 / 125000000) (124436409 / 1000000000) (Real.log (113251 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (113251 / 100000) = -Real.log (100000 / 113251) := by
    rw [show ((113251 / 100000) : ℝ) = ((100000 / 113251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71075647 / 500000000) ≤ -Real.log (86749 / 100000) ∧
    -Real.log (86749 / 100000) ≤ (28430259 / 200000000) := by
  have h := checkLog_sound (w := (13251 / 186749)) (n := 12)
    (lo := (71075647 / 500000000)) (hi := (28430259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86749) = 1/(86749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-28430259 / 200000000) (-71075647 / 500000000) (Real.log (86749 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (534647467 / 1000000000) ≤ -Real.log (500000000000 / 853423209093) ∧
    -Real.log (500000000000 / 853423209093) ≤ (133661867 / 250000000) := by
  have h := checkLog_sound (w := (353423209093 / 1353423209093)) (n := 12)
    (lo := (534647467 / 1000000000)) (hi := (133661867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853423209093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853423209093 / 500000000000) = 1/(500000000000 / 853423209093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (534647467 / 1000000000) (133661867 / 250000000) (Real.log (853423209093 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (853423209093 / 500000000000) = -Real.log (500000000000 / 853423209093) := by
    rw [show ((853423209093 / 500000000000) : ℝ) = ((500000000000 / 853423209093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133976327 / 250000000) ≤ -Real.log (250000000000 / 427248677249) ∧
    -Real.log (250000000000 / 427248677249) ≤ (535905309 / 1000000000) := by
  have h := checkLog_sound (w := (177248677249 / 677248677249)) (n := 12)
    (lo := (133976327 / 250000000)) (hi := (535905309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427248677249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427248677249 / 250000000000) = 1/(250000000000 / 427248677249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (133976327 / 250000000) (535905309 / 1000000000) (Real.log (427248677249 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (427248677249 / 250000000000) = -Real.log (250000000000 / 427248677249) := by
    rw [show ((427248677249 / 250000000000) : ℝ) = ((250000000000 / 427248677249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (187349639 / 500000000) ≤ -Real.log (125000000000 / 181819241739) ∧
    -Real.log (125000000000 / 181819241739) ≤ (374699279 / 1000000000) := by
  have h := checkLog_sound (w := (56819241739 / 306819241739)) (n := 12)
    (lo := (187349639 / 500000000)) (hi := (374699279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181819241739 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181819241739 / 125000000000) = 1/(125000000000 / 181819241739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (187349639 / 500000000) (374699279 / 1000000000) (Real.log (181819241739 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (181819241739 / 125000000000) = -Real.log (125000000000 / 181819241739) := by
    rw [show ((181819241739 / 125000000000) : ℝ) = ((125000000000 / 181819241739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (93891777 / 250000000) ≤ -Real.log (500000000000 / 727908393123) ∧
    -Real.log (500000000000 / 727908393123) ≤ (375567109 / 1000000000) := by
  have h := checkLog_sound (w := (227908393123 / 1227908393123)) (n := 12)
    (lo := (93891777 / 250000000)) (hi := (375567109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727908393123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727908393123 / 500000000000) = 1/(500000000000 / 727908393123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (93891777 / 250000000) (375567109 / 1000000000) (Real.log (727908393123 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (727908393123 / 500000000000) = -Real.log (500000000000 / 727908393123) := by
    rw [show ((727908393123 / 500000000000) : ℝ) = ((500000000000 / 727908393123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (26596479 / 100000000) ≤ -Real.log (250000000000 / 326172280121) ∧
    -Real.log (250000000000 / 326172280121) ≤ (265964791 / 1000000000) := by
  have h := checkLog_sound (w := (76172280121 / 576172280121)) (n := 12)
    (lo := (26596479 / 100000000)) (hi := (265964791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326172280121 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326172280121 / 250000000000) = 1/(250000000000 / 326172280121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (26596479 / 100000000) (265964791 / 1000000000) (Real.log (326172280121 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (326172280121 / 250000000000) = -Real.log (250000000000 / 326172280121) := by
    rw [show ((326172280121 / 250000000000) : ℝ) = ((250000000000 / 326172280121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (133293851 / 500000000) ≤ -Real.log (250000000000 / 326375520179) ∧
    -Real.log (250000000000 / 326375520179) ≤ (266587703 / 1000000000) := by
  have h := checkLog_sound (w := (76375520179 / 576375520179)) (n := 12)
    (lo := (133293851 / 500000000)) (hi := (266587703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326375520179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326375520179 / 250000000000) = 1/(250000000000 / 326375520179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (133293851 / 500000000) (266587703 / 1000000000) (Real.log (326375520179 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326375520179 / 250000000000) = -Real.log (250000000000 / 326375520179) := by
    rw [show ((326375520179 / 250000000000) : ℝ) = ((250000000000 / 326375520179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8857443 / 500000000) ≤ -Real.log (9824410999 / 10000000000) ∧
    -Real.log (9824410999 / 10000000000) ≤ (17714887 / 1000000000) := by
  have h := checkLog_sound (w := (175589001 / 19824410999)) (n := 12)
    (lo := (8857443 / 500000000)) (hi := (17714887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9824410999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9824410999) = 1/(9824410999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17714887 / 1000000000) (-8857443 / 500000000) (Real.log (9824410999 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17632439 / 1000000000) ≤ -Real.log (61407631399 / 62500000000) ∧
    -Real.log (61407631399 / 62500000000) ≤ (440811 / 25000000) := by
  have h := checkLog_sound (w := (1092368601 / 123907631399)) (n := 12)
    (lo := (17632439 / 1000000000)) (hi := (440811 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61407631399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61407631399) = 1/(61407631399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-440811 / 25000000) (-17632439 / 1000000000) (Real.log (61407631399 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019
