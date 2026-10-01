import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12096_neg : (468109 / 1000000000) ≤ -Real.log (249883 / 250000) ∧
    -Real.log (249883 / 250000) ≤ (46811 / 100000000) := by
  have h := checkLog_sound (w := (117 / 499883)) (n := 12)
    (lo := (468109 / 1000000000)) (hi := (46811 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249883) = 1/(249883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12096 : Bounds (-46811 / 100000000) (-468109 / 1000000000) (Real.log (249883 / 250000)) := by
  have h := reflection_log_12096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12097_neg : (21761389 / 100000000) ≤ -Real.log (1000000 / 1243107) ∧
    -Real.log (1000000 / 1243107) ≤ (217613891 / 1000000000) := by
  have h := checkLog_sound (w := (243107 / 2243107)) (n := 12)
    (lo := (21761389 / 100000000)) (hi := (217613891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243107 / 1000000) = 1/(1000000 / 1243107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12097 : Bounds (21761389 / 100000000) (217613891 / 1000000000) (Real.log (1243107 / 1000000)) := by
  have h := reflection_log_12097_neg
  have he : Real.log (1243107 / 1000000) = -Real.log (1000000 / 1243107) := by
    rw [show ((1243107 / 1000000) : ℝ) = ((1000000 / 1243107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12098_neg : (139266691 / 500000000) ≤ -Real.log (756893 / 1000000) ∧
    -Real.log (756893 / 1000000) ≤ (278533383 / 1000000000) := by
  have h := checkLog_sound (w := (243107 / 1756893)) (n := 12)
    (lo := (139266691 / 500000000)) (hi := (278533383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756893) = 1/(756893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12098 : Bounds (-278533383 / 1000000000) (-139266691 / 500000000) (Real.log (756893 / 1000000)) := by
  have h := reflection_log_12098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12099_neg : (27303657 / 125000000) ≤ -Real.log (1000000 / 1244121) ∧
    -Real.log (1000000 / 1244121) ≤ (218429257 / 1000000000) := by
  have h := checkLog_sound (w := (244121 / 2244121)) (n := 12)
    (lo := (27303657 / 125000000)) (hi := (218429257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244121 / 1000000) = 1/(1000000 / 1244121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12099 : Bounds (27303657 / 125000000) (218429257 / 1000000000) (Real.log (1244121 / 1000000)) := by
  have h := reflection_log_12099_neg
  have he : Real.log (1244121 / 1000000) = -Real.log (1000000 / 1244121) := by
    rw [show ((1244121 / 1000000) : ℝ) = ((1000000 / 1244121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12100_neg : (17492123 / 62500000) ≤ -Real.log (755879 / 1000000) ∧
    -Real.log (755879 / 1000000) ≤ (279873969 / 1000000000) := by
  have h := checkLog_sound (w := (244121 / 1755879)) (n := 12)
    (lo := (17492123 / 62500000)) (hi := (279873969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755879) = 1/(755879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12100 : Bounds (-279873969 / 1000000000) (-17492123 / 62500000) (Real.log (755879 / 1000000)) := by
  have h := reflection_log_12100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12101_neg : (7680589 / 125000000) ≤ -Real.log (940404937359 / 1000000000000) ∧
    -Real.log (940404937359 / 1000000000000) ≤ (61444713 / 1000000000) := by
  have h := checkLog_sound (w := (59595062641 / 1940404937359)) (n := 12)
    (lo := (7680589 / 125000000)) (hi := (61444713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940404937359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940404937359) = 1/(940404937359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12101 : Bounds (-61444713 / 1000000000) (-7680589 / 125000000) (Real.log (940404937359 / 1000000000000)) := by
  have h := reflection_log_12101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12102_neg : (15229873 / 250000000) ≤ -Real.log (940898986551 / 1000000000000) ∧
    -Real.log (940898986551 / 1000000000000) ≤ (60919493 / 1000000000) := by
  have h := checkLog_sound (w := (59101013449 / 1940898986551)) (n := 12)
    (lo := (15229873 / 250000000)) (hi := (60919493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940898986551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940898986551) = 1/(940898986551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12102 : Bounds (-60919493 / 1000000000) (-15229873 / 250000000) (Real.log (940898986551 / 1000000000000)) := by
  have h := reflection_log_12102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12103_neg : (496147273 / 1000000000) ≤ -Real.log (100000000000 / 164238141983) ∧
    -Real.log (100000000000 / 164238141983) ≤ (248073637 / 500000000) := by
  have h := checkLog_sound (w := (64238141983 / 264238141983)) (n := 12)
    (lo := (496147273 / 1000000000)) (hi := (248073637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164238141983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164238141983 / 100000000000) = 1/(100000000000 / 164238141983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12103 : Bounds (496147273 / 1000000000) (248073637 / 500000000) (Real.log (164238141983 / 100000000000)) := by
  have h := reflection_log_12103_neg
  have he : Real.log (164238141983 / 100000000000) = -Real.log (100000000000 / 164238141983) := by
    rw [show ((164238141983 / 100000000000) : ℝ) = ((100000000000 / 164238141983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12104_neg : (62287903 / 125000000) ≤ -Real.log (500000000000 / 822963066841) ∧
    -Real.log (500000000000 / 822963066841) ≤ (19932129 / 40000000) := by
  have h := checkLog_sound (w := (322963066841 / 1322963066841)) (n := 12)
    (lo := (62287903 / 125000000)) (hi := (19932129 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822963066841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822963066841 / 500000000000) = 1/(500000000000 / 822963066841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12104 : Bounds (62287903 / 125000000) (19932129 / 40000000) (Real.log (822963066841 / 500000000000)) := by
  have h := reflection_log_12104_neg
  have he : Real.log (822963066841 / 500000000000) = -Real.log (500000000000 / 822963066841) := by
    rw [show ((822963066841 / 500000000000) : ℝ) = ((500000000000 / 822963066841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12105_neg : (1012453353 / 1000000000) ≤ -Real.log (500000000000 / 1376172607879) ∧
    -Real.log (500000000000 / 1376172607879) ≤ (202490671 / 200000000) := by
  have h := checkLog_sound (w := (376172607879 / 2376172607879)) (n := 12)
    (lo := (319306173 / 1000000000)) (hi := (159653087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1376172607879 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1376172607879 / 1000000000000) = 1/(500000000000 / 1376172607879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12105 : Bounds (1012453353 / 1000000000) (202490671 / 200000000) (Real.log (1376172607879 / 500000000000)) := by
  have h := reflection_log_12105_neg
  have he : Real.log (1376172607879 / 500000000000) = -Real.log (500000000000 / 1376172607879) := by
    rw [show ((1376172607879 / 500000000000) : ℝ) = ((500000000000 / 1376172607879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12106_neg : (1015012719 / 1000000000) ≤ -Real.log (500000000000 / 1379699248121) ∧
    -Real.log (500000000000 / 1379699248121) ≤ (1015012721 / 1000000000) := by
  have h := checkLog_sound (w := (379699248121 / 2379699248121)) (n := 12)
    (lo := (321865539 / 1000000000)) (hi := (16093277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379699248121 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1379699248121 / 1000000000000) = 1/(500000000000 / 1379699248121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12106 : Bounds (1015012719 / 1000000000) (1015012721 / 1000000000) (Real.log (1379699248121 / 500000000000)) := by
  have h := reflection_log_12106_neg
  have he : Real.log (1379699248121 / 500000000000) = -Real.log (500000000000 / 1379699248121) := by
    rw [show ((1379699248121 / 500000000000) : ℝ) = ((500000000000 / 1379699248121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12107_neg : (384581897 / 1000000000) ≤ -Real.log (1000 / 1469) ∧
    -Real.log (1000 / 1469) ≤ (192290949 / 500000000) := by
  have h := checkLog_sound (w := (469 / 2469)) (n := 12)
    (lo := (384581897 / 1000000000)) (hi := (192290949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1000) = 1/(1000 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12107 : Bounds (384581897 / 1000000000) (192290949 / 500000000) (Real.log (1469 / 1000)) := by
  have h := reflection_log_12107_neg
  have he : Real.log (1469 / 1000) = -Real.log (1000 / 1469) := by
    rw [show ((1469 / 1000) : ℝ) = ((1000 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12108_neg : (632993257 / 1000000000) ≤ -Real.log (531 / 1000) ∧
    -Real.log (531 / 1000) ≤ (316496629 / 500000000) := by
  have h := checkLog_sound (w := (469 / 1531)) (n := 12)
    (lo := (632993257 / 1000000000)) (hi := (316496629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 531) = 1/(531 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12108 : Bounds (-316496629 / 500000000) (-632993257 / 1000000000) (Real.log (531 / 1000)) := by
  have h := reflection_log_12108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12109_neg : (46889 / 100000000) ≤ -Real.log (1000000 / 1000469) ∧
    -Real.log (1000000 / 1000469) ≤ (468891 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2000469)) (n := 12)
    (lo := (46889 / 100000000)) (hi := (468891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000469 / 1000000) = 1/(1000000 / 1000469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12109 : Bounds (46889 / 100000000) (468891 / 1000000000) (Real.log (1000469 / 1000000)) := by
  have h := reflection_log_12109_neg
  have he : Real.log (1000469 / 1000000) = -Real.log (1000000 / 1000469) := by
    rw [show ((1000469 / 1000000) : ℝ) = ((1000000 / 1000469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12110_neg : (46911 / 100000000) ≤ -Real.log (999531 / 1000000) ∧
    -Real.log (999531 / 1000000) ≤ (469111 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1999531)) (n := 12)
    (lo := (46911 / 100000000)) (hi := (469111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999531) = 1/(999531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12110 : Bounds (-469111 / 1000000000) (-46911 / 100000000) (Real.log (999531 / 1000000)) := by
  have h := reflection_log_12110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12111_neg : (109034549 / 500000000) ≤ -Real.log (1000000 / 1243673) ∧
    -Real.log (1000000 / 1243673) ≤ (218069099 / 1000000000) := by
  have h := checkLog_sound (w := (243673 / 2243673)) (n := 12)
    (lo := (109034549 / 500000000)) (hi := (218069099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243673 / 1000000) = 1/(1000000 / 1243673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12111 : Bounds (109034549 / 500000000) (218069099 / 1000000000) (Real.log (1243673 / 1000000)) := by
  have h := reflection_log_12111_neg
  have he : Real.log (1243673 / 1000000) = -Real.log (1000000 / 1243673) := by
    rw [show ((1243673 / 1000000) : ℝ) = ((1000000 / 1243673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12112_neg : (17455091 / 62500000) ≤ -Real.log (756327 / 1000000) ∧
    -Real.log (756327 / 1000000) ≤ (279281457 / 1000000000) := by
  have h := checkLog_sound (w := (243673 / 1756327)) (n := 12)
    (lo := (17455091 / 62500000)) (hi := (279281457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756327) = 1/(756327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12112 : Bounds (-279281457 / 1000000000) (-17455091 / 62500000) (Real.log (756327 / 1000000)) := by
  have h := reflection_log_12112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12113_neg : (6840153 / 31250000) ≤ -Real.log (62500 / 77793) ∧
    -Real.log (62500 / 77793) ≤ (218884897 / 1000000000) := by
  have h := checkLog_sound (w := (15293 / 140293)) (n := 12)
    (lo := (6840153 / 31250000)) (hi := (218884897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77793 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77793 / 62500) = 1/(62500 / 77793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12113 : Bounds (6840153 / 31250000) (218884897 / 1000000000) (Real.log (77793 / 62500)) := by
  have h := reflection_log_12113_neg
  have he : Real.log (77793 / 62500) = -Real.log (62500 / 77793) := by
    rw [show ((77793 / 62500) : ℝ) = ((62500 / 77793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12114_neg : (28062437 / 100000000) ≤ -Real.log (47207 / 62500) ∧
    -Real.log (47207 / 62500) ≤ (280624371 / 1000000000) := by
  have h := checkLog_sound (w := (15293 / 109707)) (n := 12)
    (lo := (28062437 / 100000000)) (hi := (280624371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47207) = 1/(47207 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12114 : Bounds (-280624371 / 1000000000) (-28062437 / 100000000) (Real.log (47207 / 62500)) := by
  have h := reflection_log_12114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12115_neg : (61739473 / 1000000000) ≤ -Real.log (3672374151 / 3906250000) ∧
    -Real.log (3672374151 / 3906250000) ≤ (30869737 / 500000000) := by
  have h := checkLog_sound (w := (233875849 / 7578624151)) (n := 12)
    (lo := (61739473 / 1000000000)) (hi := (30869737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3672374151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3672374151) = 1/(3672374151 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12115 : Bounds (-30869737 / 500000000) (-61739473 / 1000000000) (Real.log (3672374151 / 3906250000)) := by
  have h := reflection_log_12115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12116_neg : (30606179 / 500000000) ≤ -Real.log (940623469071 / 1000000000000) ∧
    -Real.log (940623469071 / 1000000000000) ≤ (61212359 / 1000000000) := by
  have h := checkLog_sound (w := (59376530929 / 1940623469071)) (n := 12)
    (lo := (30606179 / 500000000)) (hi := (61212359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 940623469071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 940623469071) = 1/(940623469071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12116 : Bounds (-61212359 / 1000000000) (-30606179 / 500000000) (Real.log (940623469071 / 1000000000000)) := by
  have h := reflection_log_12116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12117_neg : (248675277 / 500000000) ≤ -Real.log (500000000000 / 822179427681) ∧
    -Real.log (500000000000 / 822179427681) ≤ (99470111 / 200000000) := by
  have h := checkLog_sound (w := (322179427681 / 1322179427681)) (n := 12)
    (lo := (248675277 / 500000000)) (hi := (99470111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822179427681 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822179427681 / 500000000000) = 1/(500000000000 / 822179427681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12117 : Bounds (248675277 / 500000000) (99470111 / 200000000) (Real.log (822179427681 / 500000000000)) := by
  have h := reflection_log_12117_neg
  have he : Real.log (822179427681 / 500000000000) = -Real.log (500000000000 / 822179427681) := by
    rw [show ((822179427681 / 500000000000) : ℝ) = ((500000000000 / 822179427681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12118_neg : (249754633 / 500000000) ≤ -Real.log (250000000000 / 411978096469) ∧
    -Real.log (250000000000 / 411978096469) ≤ (499509267 / 1000000000) := by
  have h := checkLog_sound (w := (161978096469 / 661978096469)) (n := 12)
    (lo := (249754633 / 500000000)) (hi := (499509267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411978096469 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411978096469 / 250000000000) = 1/(250000000000 / 411978096469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12118 : Bounds (249754633 / 500000000) (499509267 / 1000000000) (Real.log (411978096469 / 250000000000)) := by
  have h := reflection_log_12118_neg
  have he : Real.log (411978096469 / 250000000000) = -Real.log (250000000000 / 411978096469) := by
    rw [show ((411978096469 / 250000000000) : ℝ) = ((250000000000 / 411978096469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12119_neg : (1015012719 / 1000000000) ≤ -Real.log (12500000000 / 34492481203) ∧
    -Real.log (12500000000 / 34492481203) ≤ (1015012721 / 1000000000) := by
  have h := checkLog_sound (w := (9492481203 / 59492481203)) (n := 12)
    (lo := (321865539 / 1000000000)) (hi := (16093277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34492481203 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34492481203 / 25000000000) = 1/(12500000000 / 34492481203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12119 : Bounds (1015012719 / 1000000000) (1015012721 / 1000000000) (Real.log (34492481203 / 12500000000)) := by
  have h := reflection_log_12119_neg
  have he : Real.log (34492481203 / 12500000000) = -Real.log (12500000000 / 34492481203) := by
    rw [show ((34492481203 / 12500000000) : ℝ) = ((12500000000 / 34492481203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12120_neg : (508787577 / 500000000) ≤ -Real.log (4000000000 / 11065913371) ∧
    -Real.log (4000000000 / 11065913371) ≤ (254393789 / 250000000) := by
  have h := checkLog_sound (w := (3065913371 / 19065913371)) (n := 12)
    (lo := (162213987 / 500000000)) (hi := (12977119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11065913371 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11065913371 / 8000000000) = 1/(4000000000 / 11065913371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12120 : Bounds (508787577 / 500000000) (254393789 / 250000000) (Real.log (11065913371 / 4000000000)) := by
  have h := reflection_log_12120_neg
  have he : Real.log (11065913371 / 4000000000) = -Real.log (4000000000 / 11065913371) := by
    rw [show ((11065913371 / 4000000000) : ℝ) = ((4000000000 / 11065913371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12121_neg : (240789 / 625000) ≤ -Real.log (100 / 147) ∧
    -Real.log (100 / 147) ≤ (385262401 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 247)) (n := 12)
    (lo := (240789 / 625000)) (hi := (385262401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 100) = 1/(100 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12121 : Bounds (240789 / 625000) (385262401 / 1000000000) (Real.log (147 / 100)) := by
  have h := reflection_log_12121_neg
  have he : Real.log (147 / 100) = -Real.log (100 / 147) := by
    rw [show ((147 / 100) : ℝ) = ((100 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12122_neg : (9919973 / 15625000) ≤ -Real.log (53 / 100) ∧
    -Real.log (53 / 100) ≤ (634878273 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 153)) (n := 12)
    (lo := (9919973 / 15625000)) (hi := (634878273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 53) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 53) = 1/(53 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12122 : Bounds (-634878273 / 1000000000) (-9919973 / 15625000) (Real.log (53 / 100)) := by
  have h := reflection_log_12122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12123_neg : (469889 / 1000000000) ≤ -Real.log (100000 / 100047) ∧
    -Real.log (100000 / 100047) ≤ (46989 / 100000000) := by
  have h := checkLog_sound (w := (47 / 200047)) (n := 12)
    (lo := (469889 / 1000000000)) (hi := (46989 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100047 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100047 / 100000) = 1/(100000 / 100047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12123 : Bounds (469889 / 1000000000) (46989 / 100000000) (Real.log (100047 / 100000)) := by
  have h := reflection_log_12123_neg
  have he : Real.log (100047 / 100000) = -Real.log (100000 / 100047) := by
    rw [show ((100047 / 100000) : ℝ) = ((100000 / 100047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12124_neg : (47011 / 100000000) ≤ -Real.log (99953 / 100000) ∧
    -Real.log (99953 / 100000) ≤ (470111 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 199953)) (n := 12)
    (lo := (47011 / 100000000)) (hi := (470111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99953) = 1/(99953 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12124 : Bounds (-470111 / 1000000000) (-47011 / 100000000) (Real.log (99953 / 100000)) := by
  have h := reflection_log_12124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12125_neg : (218524901 / 1000000000) ≤ -Real.log (12500 / 15553) ∧
    -Real.log (12500 / 15553) ≤ (109262451 / 500000000) := by
  have h := checkLog_sound (w := (3053 / 28053)) (n := 12)
    (lo := (218524901 / 1000000000)) (hi := (109262451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15553 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15553 / 12500) = 1/(12500 / 15553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12125 : Bounds (218524901 / 1000000000) (109262451 / 500000000) (Real.log (15553 / 12500)) := by
  have h := reflection_log_12125_neg
  have he : Real.log (15553 / 12500) = -Real.log (12500 / 15553) := by
    rw [show ((15553 / 12500) : ℝ) = ((12500 / 15553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12126_neg : (280031413 / 1000000000) ≤ -Real.log (9447 / 12500) ∧
    -Real.log (9447 / 12500) ≤ (140015707 / 500000000) := by
  have h := checkLog_sound (w := (3053 / 21947)) (n := 12)
    (lo := (280031413 / 1000000000)) (hi := (140015707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9447) = 1/(9447 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12126 : Bounds (-140015707 / 500000000) (-280031413 / 1000000000) (Real.log (9447 / 12500)) := by
  have h := reflection_log_12126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12127_neg : (219341131 / 1000000000) ≤ -Real.log (125000 / 155657) ∧
    -Real.log (125000 / 155657) ≤ (54835283 / 250000000) := by
  have h := checkLog_sound (w := (30657 / 280657)) (n := 12)
    (lo := (219341131 / 1000000000)) (hi := (54835283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155657 / 125000) = 1/(125000 / 155657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12127 : Bounds (219341131 / 1000000000) (54835283 / 250000000) (Real.log (155657 / 125000)) := by
  have h := reflection_log_12127_neg
  have he : Real.log (155657 / 125000) = -Real.log (125000 / 155657) := by
    rw [show ((155657 / 125000) : ℝ) = ((125000 / 155657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12128_neg : (14068833 / 50000000) ≤ -Real.log (94343 / 125000) ∧
    -Real.log (94343 / 125000) ≤ (281376661 / 1000000000) := by
  have h := checkLog_sound (w := (30657 / 219343)) (n := 12)
    (lo := (14068833 / 50000000)) (hi := (281376661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94343) = 1/(94343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12128 : Bounds (-281376661 / 1000000000) (-14068833 / 50000000) (Real.log (94343 / 125000)) := by
  have h := reflection_log_12128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12129_neg : (7754441 / 125000000) ≤ -Real.log (14685148351 / 15625000000) ∧
    -Real.log (14685148351 / 15625000000) ≤ (62035529 / 1000000000) := by
  have h := checkLog_sound (w := (939851649 / 30310148351)) (n := 12)
    (lo := (7754441 / 125000000)) (hi := (62035529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14685148351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14685148351) = 1/(14685148351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12129 : Bounds (-62035529 / 1000000000) (-7754441 / 125000000) (Real.log (14685148351 / 15625000000)) := by
  have h := reflection_log_12129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12130_neg : (61506511 / 1000000000) ≤ -Real.log (146929191 / 156250000) ∧
    -Real.log (146929191 / 156250000) ≤ (3844157 / 62500000) := by
  have h := checkLog_sound (w := (9320809 / 303179191)) (n := 12)
    (lo := (61506511 / 1000000000)) (hi := (3844157 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 146929191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 146929191) = 1/(146929191 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12130 : Bounds (-3844157 / 62500000) (-61506511 / 1000000000) (Real.log (146929191 / 156250000)) := by
  have h := reflection_log_12130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12131_neg : (99711263 / 200000000) ≤ -Real.log (125000000000 / 205792844289) ∧
    -Real.log (125000000000 / 205792844289) ≤ (124639079 / 250000000) := by
  have h := checkLog_sound (w := (80792844289 / 330792844289)) (n := 12)
    (lo := (99711263 / 200000000)) (hi := (124639079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205792844289 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205792844289 / 125000000000) = 1/(125000000000 / 205792844289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12131 : Bounds (99711263 / 200000000) (124639079 / 250000000) (Real.log (205792844289 / 125000000000)) := by
  have h := reflection_log_12131_neg
  have he : Real.log (205792844289 / 125000000000) = -Real.log (125000000000 / 205792844289) := by
    rw [show ((205792844289 / 125000000000) : ℝ) = ((125000000000 / 205792844289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12132_neg : (500717791 / 1000000000) ≤ -Real.log (500000000000 / 824952566699) ∧
    -Real.log (500000000000 / 824952566699) ≤ (15647431 / 31250000) := by
  have h := checkLog_sound (w := (324952566699 / 1324952566699)) (n := 12)
    (lo := (500717791 / 1000000000)) (hi := (15647431 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824952566699 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824952566699 / 500000000000) = 1/(500000000000 / 824952566699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12132 : Bounds (500717791 / 1000000000) (15647431 / 31250000) (Real.log (824952566699 / 500000000000)) := by
  have h := reflection_log_12132_neg
  have he : Real.log (824952566699 / 500000000000) = -Real.log (500000000000 / 824952566699) := by
    rw [show ((824952566699 / 500000000000) : ℝ) = ((500000000000 / 824952566699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12133_neg : (508787577 / 500000000) ≤ -Real.log (250000000000 / 691619585687) ∧
    -Real.log (250000000000 / 691619585687) ≤ (254393789 / 250000000) := by
  have h := checkLog_sound (w := (191619585687 / 1191619585687)) (n := 12)
    (lo := (162213987 / 500000000)) (hi := (12977119 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691619585687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(691619585687 / 500000000000) = 1/(250000000000 / 691619585687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12133 : Bounds (508787577 / 500000000) (254393789 / 250000000) (Real.log (691619585687 / 250000000000)) := by
  have h := reflection_log_12133_neg
  have he : Real.log (691619585687 / 250000000000) = -Real.log (250000000000 / 691619585687) := by
    rw [show ((691619585687 / 250000000000) : ℝ) = ((250000000000 / 691619585687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12134_neg : (7969849 / 7812500) ≤ -Real.log (500000000000 / 1386792452831) ∧
    -Real.log (500000000000 / 1386792452831) ≤ (510070337 / 500000000) := by
  have h := checkLog_sound (w := (386792452831 / 2386792452831)) (n := 12)
    (lo := (81748373 / 250000000)) (hi := (326993493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386792452831 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1386792452831 / 1000000000000) = 1/(500000000000 / 1386792452831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12134 : Bounds (7969849 / 7812500) (510070337 / 500000000) (Real.log (1386792452831 / 500000000000)) := by
  have h := reflection_log_12134_neg
  have he : Real.log (1386792452831 / 500000000000) = -Real.log (500000000000 / 1386792452831) := by
    rw [show ((1386792452831 / 500000000000) : ℝ) = ((500000000000 / 1386792452831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12135_neg : (385942441 / 1000000000) ≤ -Real.log (1000 / 1471) ∧
    -Real.log (1000 / 1471) ≤ (192971221 / 500000000) := by
  have h := checkLog_sound (w := (471 / 2471)) (n := 12)
    (lo := (385942441 / 1000000000)) (hi := (192971221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471 / 1000) = 1/(1000 / 1471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12135 : Bounds (385942441 / 1000000000) (192971221 / 500000000) (Real.log (1471 / 1000)) := by
  have h := reflection_log_12135_neg
  have he : Real.log (1471 / 1000) = -Real.log (1000 / 1471) := by
    rw [show ((1471 / 1000) : ℝ) = ((1000 / 1471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12136_neg : (636766847 / 1000000000) ≤ -Real.log (529 / 1000) ∧
    -Real.log (529 / 1000) ≤ (4974741 / 7812500) := by
  have h := checkLog_sound (w := (471 / 1529)) (n := 12)
    (lo := (636766847 / 1000000000)) (hi := (4974741 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 529) = 1/(529 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12136 : Bounds (-4974741 / 7812500) (-636766847 / 1000000000) (Real.log (529 / 1000)) := by
  have h := reflection_log_12136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12137_neg : (470889 / 1000000000) ≤ -Real.log (1000000 / 1000471) ∧
    -Real.log (1000000 / 1000471) ≤ (47089 / 100000000) := by
  have h := checkLog_sound (w := (471 / 2000471)) (n := 12)
    (lo := (470889 / 1000000000)) (hi := (47089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000471 / 1000000) = 1/(1000000 / 1000471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12137 : Bounds (470889 / 1000000000) (47089 / 100000000) (Real.log (1000471 / 1000000)) := by
  have h := reflection_log_12137_neg
  have he : Real.log (1000471 / 1000000) = -Real.log (1000000 / 1000471) := by
    rw [show ((1000471 / 1000000) : ℝ) = ((1000000 / 1000471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12138_neg : (47111 / 100000000) ≤ -Real.log (999529 / 1000000) ∧
    -Real.log (999529 / 1000000) ≤ (471111 / 1000000000) := by
  have h := checkLog_sound (w := (471 / 1999529)) (n := 12)
    (lo := (47111 / 100000000)) (hi := (471111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999529) = 1/(999529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12138 : Bounds (-471111 / 1000000000) (-47111 / 100000000) (Real.log (999529 / 1000000)) := by
  have h := reflection_log_12138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12139_neg : (109489847 / 500000000) ≤ -Real.log (500000 / 622403) ∧
    -Real.log (500000 / 622403) ≤ (43795939 / 200000000) := by
  have h := checkLog_sound (w := (122403 / 1122403)) (n := 12)
    (lo := (109489847 / 500000000)) (hi := (43795939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(622403 / 500000) = 1/(500000 / 622403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12139 : Bounds (109489847 / 500000000) (43795939 / 200000000) (Real.log (622403 / 500000)) := by
  have h := reflection_log_12139_neg
  have he : Real.log (622403 / 500000) = -Real.log (500000 / 622403) := by
    rw [show ((622403 / 500000) : ℝ) = ((500000 / 622403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12140_neg : (280780609 / 1000000000) ≤ -Real.log (377597 / 500000) ∧
    -Real.log (377597 / 500000) ≤ (28078061 / 100000000) := by
  have h := checkLog_sound (w := (122403 / 877597)) (n := 12)
    (lo := (280780609 / 1000000000)) (hi := (28078061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 377597) = 1/(377597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12140 : Bounds (-28078061 / 100000000) (-280780609 / 1000000000) (Real.log (377597 / 500000)) := by
  have h := reflection_log_12140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12141_neg : (109898579 / 500000000) ≤ -Real.log (15625 / 19466) ∧
    -Real.log (15625 / 19466) ≤ (219797159 / 1000000000) := by
  have h := checkLog_sound (w := (3841 / 35091)) (n := 12)
    (lo := (109898579 / 500000000)) (hi := (219797159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19466 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19466 / 15625) = 1/(15625 / 19466) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12141 : Bounds (109898579 / 500000000) (219797159 / 1000000000) (Real.log (19466 / 15625)) := by
  have h := reflection_log_12141_neg
  have he : Real.log (19466 / 15625) = -Real.log (15625 / 19466) := by
    rw [show ((19466 / 15625) : ℝ) = ((15625 / 19466) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12142_neg : (70532379 / 250000000) ≤ -Real.log (11784 / 15625) ∧
    -Real.log (11784 / 15625) ≤ (282129517 / 1000000000) := by
  have h := checkLog_sound (w := (3841 / 27409)) (n := 12)
    (lo := (70532379 / 250000000)) (hi := (282129517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11784) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11784) = 1/(11784 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12142 : Bounds (-282129517 / 1000000000) (-70532379 / 250000000) (Real.log (11784 / 15625)) := by
  have h := reflection_log_12142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12143_neg : (31166179 / 500000000) ≤ -Real.log (229387344 / 244140625) ∧
    -Real.log (229387344 / 244140625) ≤ (62332359 / 1000000000) := by
  have h := checkLog_sound (w := (14753281 / 473527969)) (n := 12)
    (lo := (31166179 / 500000000)) (hi := (62332359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 229387344) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 229387344) = 1/(229387344 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12143 : Bounds (-62332359 / 1000000000) (-31166179 / 500000000) (Real.log (229387344 / 244140625)) := by
  have h := reflection_log_12143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12144_neg : (30900457 / 500000000) ≤ -Real.log (235017505591 / 250000000000) ∧
    -Real.log (235017505591 / 250000000000) ≤ (12360183 / 200000000) := by
  have h := checkLog_sound (w := (14982494409 / 485017505591)) (n := 12)
    (lo := (30900457 / 500000000)) (hi := (12360183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235017505591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235017505591) = 1/(235017505591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12144 : Bounds (-12360183 / 200000000) (-30900457 / 500000000) (Real.log (235017505591 / 250000000000)) := by
  have h := reflection_log_12144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12145_neg : (499760303 / 1000000000) ≤ -Real.log (31250000000 / 51510191421) ∧
    -Real.log (31250000000 / 51510191421) ≤ (31235019 / 62500000) := by
  have h := checkLog_sound (w := (20260191421 / 82760191421)) (n := 12)
    (lo := (499760303 / 1000000000)) (hi := (31235019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51510191421 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51510191421 / 31250000000) = 1/(31250000000 / 51510191421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12145 : Bounds (499760303 / 1000000000) (31235019 / 62500000) (Real.log (51510191421 / 31250000000)) := by
  have h := reflection_log_12145_neg
  have he : Real.log (51510191421 / 31250000000) = -Real.log (31250000000 / 51510191421) := by
    rw [show ((51510191421 / 31250000000) : ℝ) = ((31250000000 / 51510191421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12146_neg : (250963337 / 500000000) ≤ -Real.log (500000000000 / 825950441277) ∧
    -Real.log (500000000000 / 825950441277) ≤ (20077067 / 40000000) := by
  have h := checkLog_sound (w := (325950441277 / 1325950441277)) (n := 12)
    (lo := (250963337 / 500000000)) (hi := (20077067 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825950441277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825950441277 / 500000000000) = 1/(500000000000 / 825950441277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12146 : Bounds (250963337 / 500000000) (20077067 / 40000000) (Real.log (825950441277 / 500000000000)) := by
  have h := reflection_log_12146_neg
  have he : Real.log (825950441277 / 500000000000) = -Real.log (500000000000 / 825950441277) := by
    rw [show ((825950441277 / 500000000000) : ℝ) = ((500000000000 / 825950441277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12147_neg : (7969849 / 7812500) ≤ -Real.log (50000000000 / 138679245283) ∧
    -Real.log (50000000000 / 138679245283) ≤ (510070337 / 500000000) := by
  have h := checkLog_sound (w := (38679245283 / 238679245283)) (n := 12)
    (lo := (81748373 / 250000000)) (hi := (326993493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138679245283 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138679245283 / 100000000000) = 1/(50000000000 / 138679245283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12147 : Bounds (7969849 / 7812500) (510070337 / 500000000) (Real.log (138679245283 / 50000000000)) := by
  have h := reflection_log_12147_neg
  have he : Real.log (138679245283 / 50000000000) = -Real.log (50000000000 / 138679245283) := by
    rw [show ((138679245283 / 50000000000) : ℝ) = ((50000000000 / 138679245283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12148_neg : (127838661 / 125000000) ≤ -Real.log (250000000000 / 695179584121) ∧
    -Real.log (250000000000 / 695179584121) ≤ (102270929 / 100000000) := by
  have h := checkLog_sound (w := (195179584121 / 1195179584121)) (n := 12)
    (lo := (82390527 / 250000000)) (hi := (329562109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695179584121 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(695179584121 / 500000000000) = 1/(250000000000 / 695179584121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12148 : Bounds (127838661 / 125000000) (102270929 / 100000000) (Real.log (695179584121 / 250000000000)) := by
  have h := reflection_log_12148_neg
  have he : Real.log (695179584121 / 250000000000) = -Real.log (250000000000 / 695179584121) := by
    rw [show ((695179584121 / 250000000000) : ℝ) = ((250000000000 / 695179584121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12149_neg : (19331101 / 50000000) ≤ -Real.log (125 / 184) ∧
    -Real.log (125 / 184) ≤ (386622021 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 309)) (n := 12)
    (lo := (19331101 / 50000000)) (hi := (386622021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184 / 125) = 1/(125 / 184) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12149 : Bounds (19331101 / 50000000) (386622021 / 1000000000) (Real.log (184 / 125)) := by
  have h := reflection_log_12149_neg
  have he : Real.log (184 / 125) = -Real.log (125 / 184) := by
    rw [show ((184 / 125) : ℝ) = ((125 / 184) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12150_neg : (127731799 / 200000000) ≤ -Real.log (66 / 125) ∧
    -Real.log (66 / 125) ≤ (159664749 / 250000000) := by
  have h := checkLog_sound (w := (59 / 191)) (n := 12)
    (lo := (127731799 / 200000000)) (hi := (159664749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 66) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 66) = 1/(66 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12150 : Bounds (-159664749 / 250000000) (-127731799 / 200000000) (Real.log (66 / 125)) := by
  have h := reflection_log_12150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12151_neg : (29493 / 62500000) ≤ -Real.log (125000 / 125059) ∧
    -Real.log (125000 / 125059) ≤ (471889 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 250059)) (n := 12)
    (lo := (29493 / 62500000)) (hi := (471889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125059 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125059 / 125000) = 1/(125000 / 125059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12151 : Bounds (29493 / 62500000) (471889 / 1000000000) (Real.log (125059 / 125000)) := by
  have h := reflection_log_12151_neg
  have he : Real.log (125059 / 125000) = -Real.log (125000 / 125059) := by
    rw [show ((125059 / 125000) : ℝ) = ((125000 / 125059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12152_neg : (472111 / 1000000000) ≤ -Real.log (124941 / 125000) ∧
    -Real.log (124941 / 125000) ≤ (29507 / 62500000) := by
  have h := checkLog_sound (w := (59 / 249941)) (n := 12)
    (lo := (472111 / 1000000000)) (hi := (29507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124941) = 1/(124941 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12152 : Bounds (-29507 / 62500000) (-472111 / 1000000000) (Real.log (124941 / 125000)) := by
  have h := reflection_log_12152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12153_neg : (219435083 / 1000000000) ≤ -Real.log (1000000 / 1245373) ∧
    -Real.log (1000000 / 1245373) ≤ (54858771 / 250000000) := by
  have h := checkLog_sound (w := (245373 / 2245373)) (n := 12)
    (lo := (219435083 / 1000000000)) (hi := (54858771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245373 / 1000000) = 1/(1000000 / 1245373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12153 : Bounds (219435083 / 1000000000) (54858771 / 250000000) (Real.log (1245373 / 1000000)) := by
  have h := reflection_log_12153_neg
  have he : Real.log (1245373 / 1000000) = -Real.log (1000000 / 1245373) := by
    rw [show ((1245373 / 1000000) : ℝ) = ((1000000 / 1245373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12154_neg : (281531691 / 1000000000) ≤ -Real.log (754627 / 1000000) ∧
    -Real.log (754627 / 1000000) ≤ (70382923 / 250000000) := by
  have h := checkLog_sound (w := (245373 / 1754627)) (n := 12)
    (lo := (281531691 / 1000000000)) (hi := (70382923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754627) = 1/(754627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12154 : Bounds (-70382923 / 250000000) (-281531691 / 1000000000) (Real.log (754627 / 1000000)) := by
  have h := reflection_log_12154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12155_neg : (220252977 / 1000000000) ≤ -Real.log (125000 / 155799) ∧
    -Real.log (125000 / 155799) ≤ (110126489 / 500000000) := by
  have h := checkLog_sound (w := (30799 / 280799)) (n := 12)
    (lo := (220252977 / 1000000000)) (hi := (110126489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155799 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155799 / 125000) = 1/(125000 / 155799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12155 : Bounds (220252977 / 1000000000) (110126489 / 500000000) (Real.log (155799 / 125000)) := by
  have h := reflection_log_12155_neg
  have he : Real.log (155799 / 125000) = -Real.log (125000 / 155799) := by
    rw [show ((155799 / 125000) : ℝ) = ((125000 / 155799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12156_neg : (14144147 / 50000000) ≤ -Real.log (94201 / 125000) ∧
    -Real.log (94201 / 125000) ≤ (282882941 / 1000000000) := by
  have h := checkLog_sound (w := (30799 / 219201)) (n := 12)
    (lo := (14144147 / 50000000)) (hi := (282882941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94201) = 1/(94201 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12156 : Bounds (-282882941 / 1000000000) (-14144147 / 50000000) (Real.log (94201 / 125000)) := by
  have h := reflection_log_12156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12157_neg : (31314981 / 500000000) ≤ -Real.log (14676421599 / 15625000000) ∧
    -Real.log (14676421599 / 15625000000) ≤ (62629963 / 1000000000) := by
  have h := checkLog_sound (w := (948578401 / 30301421599)) (n := 12)
    (lo := (31314981 / 500000000)) (hi := (62629963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14676421599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14676421599) = 1/(14676421599 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12157 : Bounds (-62629963 / 1000000000) (-31314981 / 500000000) (Real.log (14676421599 / 15625000000)) := by
  have h := reflection_log_12157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12158_neg : (1940519 / 31250000) ≤ -Real.log (939792090871 / 1000000000000) ∧
    -Real.log (939792090871 / 1000000000000) ≤ (62096609 / 1000000000) := by
  have h := checkLog_sound (w := (60207909129 / 1939792090871)) (n := 12)
    (lo := (1940519 / 31250000)) (hi := (62096609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 939792090871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 939792090871) = 1/(939792090871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12158 : Bounds (-62096609 / 1000000000) (-1940519 / 31250000) (Real.log (939792090871 / 1000000000000)) := by
  have h := reflection_log_12158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12159_neg : (250483387 / 500000000) ≤ -Real.log (500000000000 / 825157991961) ∧
    -Real.log (500000000000 / 825157991961) ≤ (20038671 / 40000000) := by
  have h := checkLog_sound (w := (325157991961 / 1325157991961)) (n := 12)
    (lo := (250483387 / 500000000)) (hi := (20038671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825157991961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825157991961 / 500000000000) = 1/(500000000000 / 825157991961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12159 : Bounds (250483387 / 500000000) (20038671 / 40000000) (Real.log (825157991961 / 500000000000)) := by
  have h := reflection_log_12159_neg
  have he : Real.log (825157991961 / 500000000000) = -Real.log (500000000000 / 825157991961) := by
    rw [show ((825157991961 / 500000000000) : ℝ) = ((500000000000 / 825157991961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
