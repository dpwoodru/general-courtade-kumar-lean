import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell155
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

theorem reflection_log_1_neg : (293718503 / 1000000000) ≤ -Real.log (1280 / 1717) ∧
    -Real.log (1280 / 1717) ≤ (36714813 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2997)) (n := 12)
    (lo := (293718503 / 1000000000)) (hi := (36714813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1717 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1717 / 1280) = 1/(1280 / 1717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (293718503 / 1000000000) (36714813 / 125000000) (Real.log (1717 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1717 / 1280) = -Real.log (1280 / 1717) := by
    rw [show ((1717 / 1280) : ℝ) = ((1280 / 1717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208824199 / 500000000) ≤ -Real.log (843 / 1280) ∧
    -Real.log (843 / 1280) ≤ (417648399 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 2123)) (n := 12)
    (lo := (208824199 / 500000000)) (hi := (417648399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 843) = 1/(843 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-417648399 / 1000000000) (-208824199 / 500000000) (Real.log (843 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (183301 / 625000) ≤ -Real.log (1024 / 1373) ∧
    -Real.log (1024 / 1373) ≤ (293281601 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 2397)) (n := 12)
    (lo := (183301 / 625000)) (hi := (293281601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1024) = 1/(1024 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (183301 / 625000) (293281601 / 1000000000) (Real.log (1373 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1373 / 1024) = -Real.log (1024 / 1373) := by
    rw [show ((1373 / 1024) : ℝ) = ((1024 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208379557 / 500000000) ≤ -Real.log (675 / 1024) ∧
    -Real.log (675 / 1024) ≤ (83351823 / 200000000) := by
  have h := checkLog_sound (w := (349 / 1699)) (n := 12)
    (lo := (208379557 / 500000000)) (hi := (83351823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 675) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 675) = 1/(675 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83351823 / 200000000) (-208379557 / 500000000) (Real.log (675 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216901711 / 1000000000) ≤ -Real.log (500000 / 621111) ∧
    -Real.log (500000 / 621111) ≤ (13556357 / 62500000) := by
  have h := checkLog_sound (w := (121111 / 1121111)) (n := 12)
    (lo := (216901711 / 1000000000)) (hi := (13556357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621111 / 500000) = 1/(500000 / 621111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216901711 / 1000000000) (13556357 / 62500000) (Real.log (621111 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (621111 / 500000) = -Real.log (500000 / 621111) := by
    rw [show ((621111 / 500000) : ℝ) = ((500000 / 621111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (69341203 / 250000000) ≤ -Real.log (378889 / 500000) ∧
    -Real.log (378889 / 500000) ≤ (277364813 / 1000000000) := by
  have h := checkLog_sound (w := (121111 / 878889)) (n := 12)
    (lo := (69341203 / 250000000)) (hi := (277364813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378889) = 1/(378889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277364813 / 1000000000) (-69341203 / 250000000) (Real.log (378889 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (217241367 / 1000000000) ≤ -Real.log (250000 / 310661) ∧
    -Real.log (250000 / 310661) ≤ (27155171 / 125000000) := by
  have h := checkLog_sound (w := (60661 / 560661)) (n := 12)
    (lo := (217241367 / 1000000000)) (hi := (27155171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310661 / 250000) = 1/(250000 / 310661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (217241367 / 1000000000) (27155171 / 125000000) (Real.log (310661 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (310661 / 250000) = -Real.log (250000 / 310661) := by
    rw [show ((310661 / 250000) : ℝ) = ((250000 / 310661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138960929 / 500000000) ≤ -Real.log (189339 / 250000) ∧
    -Real.log (189339 / 250000) ≤ (277921859 / 1000000000) := by
  have h := checkLog_sound (w := (60661 / 439339)) (n := 12)
    (lo := (138960929 / 500000000)) (hi := (277921859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189339) = 1/(189339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277921859 / 1000000000) (-138960929 / 500000000) (Real.log (189339 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (80253929 / 500000000) ≤ -Real.log (1000000 / 1174107) ∧
    -Real.log (1000000 / 1174107) ≤ (160507859 / 1000000000) := by
  have h := checkLog_sound (w := (174107 / 2174107)) (n := 12)
    (lo := (80253929 / 500000000)) (hi := (160507859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174107 / 1000000) = 1/(1000000 / 1174107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (80253929 / 500000000) (160507859 / 1000000000) (Real.log (1174107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1174107 / 1000000) = -Real.log (1000000 / 1174107) := by
    rw [show ((1174107 / 1000000) : ℝ) = ((1000000 / 1174107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191290053 / 1000000000) ≤ -Real.log (825893 / 1000000) ∧
    -Real.log (825893 / 1000000) ≤ (95645027 / 500000000) := by
  have h := checkLog_sound (w := (174107 / 1825893)) (n := 12)
    (lo := (191290053 / 1000000000)) (hi := (95645027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825893) = 1/(825893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95645027 / 500000000) (-191290053 / 1000000000) (Real.log (825893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20096801 / 125000000) ≤ -Real.log (50000 / 58721) ∧
    -Real.log (50000 / 58721) ≤ (160774409 / 1000000000) := by
  have h := checkLog_sound (w := (8721 / 108721)) (n := 12)
    (lo := (20096801 / 125000000)) (hi := (160774409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58721 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58721 / 50000) = 1/(50000 / 58721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20096801 / 125000000) (160774409 / 1000000000) (Real.log (58721 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58721 / 50000) = -Real.log (50000 / 58721) := by
    rw [show ((58721 / 50000) : ℝ) = ((50000 / 58721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (191669109 / 1000000000) ≤ -Real.log (41279 / 50000) ∧
    -Real.log (41279 / 50000) ≤ (19166911 / 100000000) := by
  have h := checkLog_sound (w := (8721 / 91279)) (n := 12)
    (lo := (191669109 / 1000000000)) (hi := (19166911 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 41279) = 1/(41279 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19166911 / 100000000) (-191669109 / 1000000000) (Real.log (41279 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (355020357 / 500000000) ≤ -Real.log (500000000000 / 1017037037037) ∧
    -Real.log (500000000000 / 1017037037037) ≤ (177510179 / 250000000) := by
  have h := checkLog_sound (w := (17037037037 / 2017037037037)) (n := 12)
    (lo := (8446767 / 500000000)) (hi := (3378707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017037037037 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1017037037037 / 1000000000000) = 1/(500000000000 / 1017037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (355020357 / 500000000) (177510179 / 250000000) (Real.log (1017037037037 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1017037037037 / 500000000000) = -Real.log (500000000000 / 1017037037037) := by
    rw [show ((1017037037037 / 500000000000) : ℝ) = ((500000000000 / 1017037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355683451 / 500000000) ≤ -Real.log (500000000000 / 1018386714117) ∧
    -Real.log (500000000000 / 1018386714117) ≤ (88920863 / 125000000) := by
  have h := checkLog_sound (w := (18386714117 / 2018386714117)) (n := 12)
    (lo := (9109861 / 500000000)) (hi := (18219723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018386714117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018386714117 / 1000000000000) = 1/(500000000000 / 1018386714117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (355683451 / 500000000) (88920863 / 125000000) (Real.log (1018386714117 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1018386714117 / 500000000000) = -Real.log (500000000000 / 1018386714117) := by
    rw [show ((1018386714117 / 500000000000) : ℝ) = ((500000000000 / 1018386714117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (494266523 / 1000000000) ≤ -Real.log (15625000000 / 25613990839) ∧
    -Real.log (15625000000 / 25613990839) ≤ (123566631 / 250000000) := by
  have h := checkLog_sound (w := (9988990839 / 41238990839)) (n := 12)
    (lo := (494266523 / 1000000000)) (hi := (123566631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25613990839 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25613990839 / 15625000000) = 1/(15625000000 / 25613990839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (494266523 / 1000000000) (123566631 / 250000000) (Real.log (25613990839 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25613990839 / 15625000000) = -Real.log (15625000000 / 25613990839) := by
    rw [show ((25613990839 / 15625000000) : ℝ) = ((15625000000 / 25613990839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (247581613 / 500000000) ≤ -Real.log (250000000000 / 410191508353) ∧
    -Real.log (250000000000 / 410191508353) ≤ (495163227 / 1000000000) := by
  have h := checkLog_sound (w := (160191508353 / 660191508353)) (n := 12)
    (lo := (247581613 / 500000000)) (hi := (495163227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410191508353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410191508353 / 250000000000) = 1/(250000000000 / 410191508353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (247581613 / 500000000) (495163227 / 1000000000) (Real.log (410191508353 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (410191508353 / 250000000000) = -Real.log (250000000000 / 410191508353) := by
    rw [show ((410191508353 / 250000000000) : ℝ) = ((250000000000 / 410191508353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (43974739 / 125000000) ≤ -Real.log (500000000000 / 710810601373) ∧
    -Real.log (500000000000 / 710810601373) ≤ (351797913 / 1000000000) := by
  have h := checkLog_sound (w := (210810601373 / 1210810601373)) (n := 12)
    (lo := (43974739 / 125000000)) (hi := (351797913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710810601373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710810601373 / 500000000000) = 1/(500000000000 / 710810601373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (43974739 / 125000000) (351797913 / 1000000000) (Real.log (710810601373 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (710810601373 / 500000000000) = -Real.log (500000000000 / 710810601373) := by
    rw [show ((710810601373 / 500000000000) : ℝ) = ((500000000000 / 710810601373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (176221759 / 500000000) ≤ -Real.log (500000000000 / 711269652851) ∧
    -Real.log (500000000000 / 711269652851) ≤ (352443519 / 1000000000) := by
  have h := checkLog_sound (w := (211269652851 / 1211269652851)) (n := 12)
    (lo := (176221759 / 500000000)) (hi := (352443519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711269652851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711269652851 / 500000000000) = 1/(500000000000 / 711269652851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (176221759 / 500000000) (352443519 / 1000000000) (Real.log (711269652851 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (711269652851 / 500000000000) = -Real.log (500000000000 / 711269652851) := by
    rw [show ((711269652851 / 500000000000) : ℝ) = ((500000000000 / 711269652851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (308947 / 10000000) ≤ -Real.log (2423944159 / 2500000000) ∧
    -Real.log (2423944159 / 2500000000) ≤ (30894701 / 1000000000) := by
  have h := checkLog_sound (w := (76055841 / 4923944159)) (n := 12)
    (lo := (308947 / 10000000)) (hi := (30894701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2423944159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2423944159) = 1/(2423944159 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30894701 / 1000000000) (-308947 / 10000000) (Real.log (2423944159 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6156439 / 200000000) ≤ -Real.log (969686752551 / 1000000000000) ∧
    -Real.log (969686752551 / 1000000000000) ≤ (7695549 / 250000000) := by
  have h := checkLog_sound (w := (30313247449 / 1969686752551)) (n := 12)
    (lo := (6156439 / 200000000)) (hi := (7695549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969686752551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969686752551) = 1/(969686752551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7695549 / 250000000) (-6156439 / 200000000) (Real.log (969686752551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell155
