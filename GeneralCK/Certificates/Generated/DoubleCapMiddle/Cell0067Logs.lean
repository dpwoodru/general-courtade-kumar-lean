import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0067
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

theorem reflection_log_1_neg : (180364607 / 500000000) ≤ -Real.log (320 / 459) ∧
    -Real.log (320 / 459) ≤ (72145843 / 200000000) := by
  have h := checkLog_sound (w := (139 / 779)) (n := 12)
    (lo := (180364607 / 500000000)) (hi := (72145843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((459 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(459 / 320) = 1/(320 / 459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (180364607 / 500000000) (72145843 / 200000000) (Real.log (459 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (459 / 320) = -Real.log (320 / 459) := by
    rw [show ((459 / 320) : ℝ) = ((320 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (142455991 / 250000000) ≤ -Real.log (181 / 320) ∧
    -Real.log (181 / 320) ≤ (113964793 / 200000000) := by
  have h := checkLog_sound (w := (139 / 501)) (n := 12)
    (lo := (142455991 / 250000000)) (hi := (113964793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 181) = 1/(181 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113964793 / 200000000) (-142455991 / 250000000) (Real.log (181 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (179955943 / 500000000) ≤ -Real.log (2560 / 3669) ∧
    -Real.log (2560 / 3669) ≤ (359911887 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 6229)) (n := 12)
    (lo := (179955943 / 500000000)) (hi := (359911887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3669 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3669 / 2560) = 1/(2560 / 3669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (179955943 / 500000000) (359911887 / 1000000000) (Real.log (3669 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3669 / 2560) = -Real.log (2560 / 3669) := by
    rw [show ((3669 / 2560) : ℝ) = ((2560 / 3669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141938571 / 250000000) ≤ -Real.log (1451 / 2560) ∧
    -Real.log (1451 / 2560) ≤ (113550857 / 200000000) := by
  have h := checkLog_sound (w := (1109 / 4011)) (n := 12)
    (lo := (141938571 / 250000000)) (hi := (113550857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1451) = 1/(1451 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) (Real.log (1451 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (312634879 / 500000000) ≤ -Real.log (160 / 299) ∧
    -Real.log (160 / 299) ≤ (625269759 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 459)) (n := 12)
    (lo := (312634879 / 500000000)) (hi := (625269759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 160) = 1/(160 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (312634879 / 500000000) (625269759 / 1000000000) (Real.log (299 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299 / 160) = -Real.log (160 / 299) := by
    rw [show ((299 / 160) : ℝ) = ((160 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (126915711 / 62500000) ≤ -Real.log (21 / 160) ∧
    -Real.log (21 / 160) ≤ (2030651379 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 21) = 1/(21 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2030651379 / 1000000000) (-126915711 / 62500000) (Real.log (21 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62401479 / 100000000) ≤ -Real.log (1280 / 2389) ∧
    -Real.log (1280 / 2389) ≤ (624014791 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 3669)) (n := 12)
    (lo := (62401479 / 100000000)) (hi := (624014791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 1280) = 1/(1280 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62401479 / 100000000) (624014791 / 1000000000) (Real.log (2389 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2389 / 1280) = -Real.log (1280 / 2389) := by
    rw [show ((2389 / 1280) : ℝ) = ((1280 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2012951799 / 1000000000) ≤ -Real.log (171 / 1280) ∧
    -Real.log (171 / 1280) ≤ (1006475901 / 500000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 171) = 1/(171 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) (Real.log (171 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62055589 / 125000000) ≤ -Real.log (100000 / 164287) ∧
    -Real.log (100000 / 164287) ≤ (496444713 / 1000000000) := by
  have h := checkLog_sound (w := (64287 / 264287)) (n := 12)
    (lo := (62055589 / 125000000)) (hi := (496444713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164287 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164287 / 100000) = 1/(100000 / 164287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62055589 / 125000000) (496444713 / 1000000000) (Real.log (164287 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164287 / 100000) = -Real.log (100000 / 164287) := by
    rw [show ((164287 / 100000) : ℝ) = ((100000 / 164287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1029655417 / 1000000000) ≤ -Real.log (35713 / 100000) ∧
    -Real.log (35713 / 100000) ≤ (1029655419 / 1000000000) := by
  have h := checkLog_sound (w := (14287 / 85713)) (n := 12)
    (lo := (336508237 / 1000000000)) (hi := (168254119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35713) = 1/(35713 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1029655419 / 1000000000) (-1029655417 / 1000000000) (Real.log (35713 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62209797 / 125000000) ≤ -Real.log (500000 / 822449) ∧
    -Real.log (500000 / 822449) ≤ (497678377 / 1000000000) := by
  have h := checkLog_sound (w := (322449 / 1322449)) (n := 12)
    (lo := (62209797 / 125000000)) (hi := (497678377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822449 / 500000) = 1/(500000 / 822449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62209797 / 125000000) (497678377 / 1000000000) (Real.log (822449 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (822449 / 500000) = -Real.log (500000 / 822449) := by
    rw [show ((822449 / 500000) : ℝ) = ((500000 / 822449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (517675103 / 500000000) ≤ -Real.log (177551 / 500000) ∧
    -Real.log (177551 / 500000) ≤ (16177347 / 15625000) := by
  have h := checkLog_sound (w := (72449 / 427551)) (n := 12)
    (lo := (171101513 / 500000000)) (hi := (342203027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177551) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177551) = 1/(177551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16177347 / 15625000) (-517675103 / 500000000) (Real.log (177551 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (413870351 / 1000000000) ≤ -Real.log (1000000 / 1512661) ∧
    -Real.log (1000000 / 1512661) ≤ (25866897 / 62500000) := by
  have h := checkLog_sound (w := (512661 / 2512661)) (n := 12)
    (lo := (413870351 / 1000000000)) (hi := (25866897 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1512661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1512661 / 1000000) = 1/(1000000 / 1512661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (413870351 / 1000000000) (25866897 / 62500000) (Real.log (1512661 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1512661 / 1000000) = -Real.log (1000000 / 1512661) := by
    rw [show ((1512661 / 1000000) : ℝ) = ((1000000 / 1512661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (359397649 / 500000000) ≤ -Real.log (487339 / 1000000) ∧
    -Real.log (487339 / 1000000) ≤ (7187953 / 10000000) := by
  have h := checkLog_sound (w := (12661 / 987339)) (n := 12)
    (lo := (12824059 / 500000000)) (hi := (25648119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 487339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 487339) = 1/(487339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-7187953 / 10000000) (-359397649 / 500000000) (Real.log (487339 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103802039 / 250000000) ≤ -Real.log (500000 / 757343) ∧
    -Real.log (500000 / 757343) ≤ (415208157 / 1000000000) := by
  have h := checkLog_sound (w := (257343 / 1257343)) (n := 12)
    (lo := (103802039 / 250000000)) (hi := (415208157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757343 / 500000) = 1/(500000 / 757343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103802039 / 250000000) (415208157 / 1000000000) (Real.log (757343 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (757343 / 500000) = -Real.log (500000 / 757343) := by
    rw [show ((757343 / 500000) : ℝ) = ((500000 / 757343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361479587 / 500000000) ≤ -Real.log (242657 / 500000) ∧
    -Real.log (242657 / 500000) ≤ (90369897 / 125000000) := by
  have h := checkLog_sound (w := (7343 / 492657)) (n := 12)
    (lo := (14905997 / 500000000)) (hi := (5962399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 242657) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 242657) = 1/(242657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90369897 / 125000000) (-361479587 / 500000000) (Real.log (242657 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1526100129 / 1000000000) ≤ -Real.log (125000000000 / 575025200907) ∧
    -Real.log (125000000000 / 575025200907) ≤ (381525033 / 250000000) := by
  have h := checkLog_sound (w := (75025200907 / 1075025200907)) (n := 12)
    (lo := (139805769 / 1000000000)) (hi := (13980577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575025200907 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575025200907 / 500000000000) = 1/(125000000000 / 575025200907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1526100129 / 1000000000) (381525033 / 250000000) (Real.log (575025200907 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (575025200907 / 125000000000) = -Real.log (125000000000 / 575025200907) := by
    rw [show ((575025200907 / 125000000000) : ℝ) = ((125000000000 / 575025200907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1533028581 / 1000000000) ≤ -Real.log (31250000000 / 144755767357) ∧
    -Real.log (31250000000 / 144755767357) ≤ (191628573 / 125000000) := by
  have h := checkLog_sound (w := (19755767357 / 269755767357)) (n := 12)
    (lo := (146734221 / 1000000000)) (hi := (73367111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144755767357 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(144755767357 / 125000000000) = 1/(31250000000 / 144755767357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1533028581 / 1000000000) (191628573 / 125000000) (Real.log (144755767357 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (144755767357 / 31250000000) = -Real.log (31250000000 / 144755767357) := by
    rw [show ((144755767357 / 31250000000) : ℝ) = ((31250000000 / 144755767357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22653313 / 20000000) ≤ -Real.log (250000000000 / 775979862067) ∧
    -Real.log (250000000000 / 775979862067) ≤ (283166413 / 250000000) := by
  have h := checkLog_sound (w := (275979862067 / 1275979862067)) (n := 12)
    (lo := (43951847 / 100000000)) (hi := (439518471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775979862067 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(775979862067 / 500000000000) = 1/(250000000000 / 775979862067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (22653313 / 20000000) (283166413 / 250000000) (Real.log (775979862067 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775979862067 / 250000000000) = -Real.log (250000000000 / 775979862067) := by
    rw [show ((775979862067 / 250000000000) : ℝ) = ((250000000000 / 775979862067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1138167331 / 1000000000) ≤ -Real.log (500000000000 / 1560521641659) ∧
    -Real.log (500000000000 / 1560521641659) ≤ (1138167333 / 1000000000) := by
  have h := checkLog_sound (w := (560521641659 / 2560521641659)) (n := 12)
    (lo := (445020151 / 1000000000)) (hi := (55627519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1560521641659 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1560521641659 / 1000000000000) = 1/(500000000000 / 1560521641659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1138167331 / 1000000000) (1138167333 / 1000000000) (Real.log (1560521641659 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1560521641659 / 500000000000) = -Real.log (500000000000 / 1560521641659) := by
    rw [show ((1560521641659 / 500000000000) : ℝ) = ((500000000000 / 1560521641659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0067
