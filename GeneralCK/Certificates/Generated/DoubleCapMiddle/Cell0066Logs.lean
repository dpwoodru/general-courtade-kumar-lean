import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0066
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

theorem reflection_log_1_neg : (180772937 / 500000000) ≤ -Real.log (512 / 735) ∧
    -Real.log (512 / 735) ≤ (2892367 / 8000000) := by
  have h := checkLog_sound (w := (223 / 1247)) (n := 12)
    (lo := (180772937 / 500000000)) (hi := (2892367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735 / 512) = 1/(512 / 735) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (180772937 / 500000000) (2892367 / 8000000) (Real.log (735 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (735 / 512) = -Real.log (512 / 735) := by
    rw [show ((735 / 512) : ℝ) = ((512 / 735) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (35743621 / 62500000) ≤ -Real.log (289 / 512) ∧
    -Real.log (289 / 512) ≤ (571897937 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 801)) (n := 12)
    (lo := (35743621 / 62500000)) (hi := (571897937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 289) = 1/(289 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-571897937 / 1000000000) (-35743621 / 62500000) (Real.log (289 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (180364607 / 500000000) ≤ -Real.log (320 / 459) ∧
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


theorem reflection_log_3 : Bounds (180364607 / 500000000) (72145843 / 200000000) (Real.log (459 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (459 / 320) = -Real.log (320 / 459) := by
    rw [show ((459 / 320) : ℝ) = ((320 / 459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (142455991 / 250000000) ≤ -Real.log (181 / 320) ∧
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


theorem reflection_log_4 : Bounds (-113964793 / 200000000) (-142455991 / 250000000) (Real.log (181 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39157697 / 62500000) ≤ -Real.log (256 / 479) ∧
    -Real.log (256 / 479) ≤ (626523153 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 735)) (n := 12)
    (lo := (39157697 / 62500000)) (hi := (626523153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 256) = 1/(256 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (39157697 / 62500000) (626523153 / 1000000000) (Real.log (479 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (479 / 256) = -Real.log (256 / 479) := by
    rw [show ((479 / 256) : ℝ) = ((256 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2048669881 / 1000000000) ≤ -Real.log (33 / 256) ∧
    -Real.log (33 / 256) ≤ (512167471 / 250000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 33) = 1/(33 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-512167471 / 250000000) (-2048669881 / 1000000000) (Real.log (33 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (312634879 / 500000000) ≤ -Real.log (160 / 299) ∧
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


theorem reflection_log_7 : Bounds (312634879 / 500000000) (625269759 / 1000000000) (Real.log (299 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (299 / 160) = -Real.log (160 / 299) := by
    rw [show ((299 / 160) : ℝ) = ((160 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126915711 / 62500000) ≤ -Real.log (21 / 160) ∧
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


theorem reflection_log_8 : Bounds (-2030651379 / 1000000000) (-126915711 / 62500000) (Real.log (21 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62209721 / 125000000) ≤ -Real.log (1000000 / 1644897) ∧
    -Real.log (1000000 / 1644897) ≤ (497677769 / 1000000000) := by
  have h := checkLog_sound (w := (644897 / 2644897)) (n := 12)
    (lo := (62209721 / 125000000)) (hi := (497677769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1644897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1644897 / 1000000) = 1/(1000000 / 1644897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62209721 / 125000000) (497677769 / 1000000000) (Real.log (1644897 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1644897 / 1000000) = -Real.log (1000000 / 1644897) := by
    rw [show ((1644897 / 1000000) : ℝ) = ((1000000 / 1644897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (103534739 / 100000000) ≤ -Real.log (355103 / 1000000) ∧
    -Real.log (355103 / 1000000) ≤ (16177303 / 15625000) := by
  have h := checkLog_sound (w := (144897 / 855103)) (n := 12)
    (lo := (34220021 / 100000000)) (hi := (342200211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 355103) = 1/(355103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16177303 / 15625000) (-103534739 / 100000000) (Real.log (355103 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (99782711 / 200000000) ≤ -Real.log (1000000 / 1646931) ∧
    -Real.log (1000000 / 1646931) ≤ (124728389 / 250000000) := by
  have h := checkLog_sound (w := (646931 / 2646931)) (n := 12)
    (lo := (99782711 / 200000000)) (hi := (124728389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1646931 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1646931 / 1000000) = 1/(1000000 / 1646931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (99782711 / 200000000) (124728389 / 250000000) (Real.log (1646931 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1646931 / 1000000) = -Real.log (1000000 / 1646931) := by
    rw [show ((1646931 / 1000000) : ℝ) = ((1000000 / 1646931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1041091773 / 1000000000) ≤ -Real.log (353069 / 1000000) ∧
    -Real.log (353069 / 1000000) ≤ (41643671 / 40000000) := by
  have h := checkLog_sound (w := (146931 / 853069)) (n := 12)
    (lo := (347944593 / 1000000000)) (hi := (173972297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353069) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 353069) = 1/(353069 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41643671 / 40000000) (-1041091773 / 1000000000) (Real.log (353069 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51900937 / 125000000) ≤ -Real.log (200000 / 302937) ∧
    -Real.log (200000 / 302937) ≤ (415207497 / 1000000000) := by
  have h := checkLog_sound (w := (102937 / 502937)) (n := 12)
    (lo := (51900937 / 125000000)) (hi := (415207497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302937 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302937 / 200000) = 1/(200000 / 302937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51900937 / 125000000) (415207497 / 1000000000) (Real.log (302937 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302937 / 200000) = -Real.log (200000 / 302937) := by
    rw [show ((302937 / 200000) : ℝ) = ((200000 / 302937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (722957113 / 1000000000) ≤ -Real.log (97063 / 200000) ∧
    -Real.log (97063 / 200000) ≤ (144591423 / 200000000) := by
  have h := checkLog_sound (w := (2937 / 197063)) (n := 12)
    (lo := (29809933 / 1000000000)) (hi := (14904967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 97063) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 97063) = 1/(97063 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144591423 / 200000000) (-722957113 / 1000000000) (Real.log (97063 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (416549449 / 1000000000) ≤ -Real.log (1000000 / 1516719) ∧
    -Real.log (1000000 / 1516719) ≤ (8330989 / 20000000) := by
  have h := checkLog_sound (w := (516719 / 2516719)) (n := 12)
    (lo := (416549449 / 1000000000)) (hi := (8330989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1516719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1516719 / 1000000) = 1/(1000000 / 1516719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (416549449 / 1000000000) (8330989 / 20000000) (Real.log (1516719 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1516719 / 1000000) = -Real.log (1000000 / 1516719) := by
    rw [show ((1516719 / 1000000) : ℝ) = ((1000000 / 1516719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (727157013 / 1000000000) ≤ -Real.log (483281 / 1000000) ∧
    -Real.log (483281 / 1000000) ≤ (145431403 / 200000000) := by
  have h := checkLog_sound (w := (16719 / 983281)) (n := 12)
    (lo := (34009833 / 1000000000)) (hi := (17004917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 483281) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 483281) = 1/(483281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-145431403 / 200000000) (-727157013 / 1000000000) (Real.log (483281 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1533025157 / 1000000000) ≤ -Real.log (250000000000 / 1158042173679) ∧
    -Real.log (250000000000 / 1158042173679) ≤ (38325629 / 25000000) := by
  have h := checkLog_sound (w := (158042173679 / 2158042173679)) (n := 12)
    (lo := (146730797 / 1000000000)) (hi := (73365399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158042173679 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1158042173679 / 1000000000000) = 1/(250000000000 / 1158042173679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1533025157 / 1000000000) (38325629 / 25000000) (Real.log (1158042173679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1158042173679 / 250000000000) = -Real.log (250000000000 / 1158042173679) := by
    rw [show ((1158042173679 / 250000000000) : ℝ) = ((250000000000 / 1158042173679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96250333 / 62500000) ≤ -Real.log (62500000000 / 291538445743) ∧
    -Real.log (62500000000 / 291538445743) ≤ (1540005331 / 1000000000) := by
  have h := checkLog_sound (w := (41538445743 / 541538445743)) (n := 12)
    (lo := (19213871 / 125000000)) (hi := (153710969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291538445743 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(291538445743 / 250000000000) = 1/(62500000000 / 291538445743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96250333 / 62500000) (1540005331 / 1000000000) (Real.log (291538445743 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (291538445743 / 62500000000) = -Real.log (62500000000 / 291538445743) := by
    rw [show ((291538445743 / 62500000000) : ℝ) = ((62500000000 / 291538445743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (113816461 / 100000000) ≤ -Real.log (250000000000 / 780258697959) ∧
    -Real.log (250000000000 / 780258697959) ≤ (284541153 / 250000000) := by
  have h := checkLog_sound (w := (280258697959 / 1280258697959)) (n := 12)
    (lo := (44501743 / 100000000)) (hi := (445017431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780258697959 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(780258697959 / 500000000000) = 1/(250000000000 / 780258697959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (113816461 / 100000000) (284541153 / 250000000) (Real.log (780258697959 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780258697959 / 250000000000) = -Real.log (250000000000 / 780258697959) := by
    rw [show ((780258697959 / 250000000000) : ℝ) = ((250000000000 / 780258697959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (571853231 / 500000000) ≤ -Real.log (20000000000 / 62767582421) ∧
    -Real.log (20000000000 / 62767582421) ≤ (35740827 / 31250000) := by
  have h := checkLog_sound (w := (22767582421 / 102767582421)) (n := 12)
    (lo := (225279641 / 500000000)) (hi := (450559283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62767582421 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62767582421 / 40000000000) = 1/(20000000000 / 62767582421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (571853231 / 500000000) (35740827 / 31250000) (Real.log (62767582421 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (62767582421 / 20000000000) = -Real.log (20000000000 / 62767582421) := by
    rw [show ((62767582421 / 20000000000) : ℝ) = ((20000000000 / 62767582421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0066
