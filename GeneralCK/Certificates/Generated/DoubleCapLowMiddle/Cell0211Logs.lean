import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0211
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

theorem reflection_log_1_neg : (555320863 / 1000000000) ≤ -Real.log (400 / 697) ∧
    -Real.log (400 / 697) ≤ (17353777 / 31250000) := by
  have h := checkLog_sound (w := (297 / 1097)) (n := 12)
    (lo := (555320863 / 1000000000)) (hi := (17353777 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 400) = 1/(400 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (555320863 / 1000000000) (17353777 / 31250000) (Real.log (697 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (697 / 400) = -Real.log (400 / 697) := by
    rw [show ((697 / 400) : ℝ) = ((400 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (678367779 / 500000000) ≤ -Real.log (103 / 400) ∧
    -Real.log (103 / 400) ≤ (33918389 / 25000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 103) = 1/(103 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33918389 / 25000000) (-678367779 / 500000000) (Real.log (103 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2155889 / 3906250) ≤ -Real.log (3200 / 5557) ∧
    -Real.log (3200 / 5557) ≤ (110381517 / 200000000) := by
  have h := checkLog_sound (w := (2357 / 8757)) (n := 12)
    (lo := (2155889 / 3906250)) (hi := (110381517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5557 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5557 / 3200) = 1/(3200 / 5557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2155889 / 3906250) (110381517 / 200000000) (Real.log (5557 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5557 / 3200) = -Real.log (3200 / 5557) := by
    rw [show ((5557 / 3200) : ℝ) = ((3200 / 5557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133393913 / 100000000) ≤ -Real.log (843 / 3200) ∧
    -Real.log (843 / 3200) ≤ (333484783 / 250000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 843) = 1/(843 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-333484783 / 250000000) (-133393913 / 100000000) (Real.log (843 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193692997 / 500000000) ≤ -Real.log (1600 / 2357) ∧
    -Real.log (1600 / 2357) ≤ (77477199 / 200000000) := by
  have h := checkLog_sound (w := (757 / 3957)) (n := 12)
    (lo := (193692997 / 500000000)) (hi := (77477199 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2357 / 1600) = 1/(1600 / 2357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193692997 / 500000000) (77477199 / 200000000) (Real.log (2357 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2357 / 1600) = -Real.log (1600 / 2357) := by
    rw [show ((2357 / 1600) : ℝ) = ((1600 / 2357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12815839 / 20000000) ≤ -Real.log (843 / 1600) ∧
    -Real.log (843 / 1600) ≤ (640791951 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 843) = 1/(843 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-640791951 / 1000000000) (-12815839 / 20000000) (Real.log (843 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (121092679 / 200000000) ≤ -Real.log (1000000 / 1832101) ∧
    -Real.log (1000000 / 1832101) ≤ (151365849 / 250000000) := by
  have h := checkLog_sound (w := (832101 / 2832101)) (n := 12)
    (lo := (121092679 / 200000000)) (hi := (151365849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1832101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1832101 / 1000000) = 1/(1000000 / 1832101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (121092679 / 200000000) (151365849 / 250000000) (Real.log (1832101 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1832101 / 1000000) = -Real.log (1000000 / 1832101) := by
    rw [show ((1832101 / 1000000) : ℝ) = ((1000000 / 1832101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1784392669 / 1000000000) ≤ -Real.log (167899 / 1000000) ∧
    -Real.log (167899 / 1000000) ≤ (55762271 / 31250000) := by
  have h := checkLog_sound (w := (82101 / 417899)) (n := 12)
    (lo := (398098309 / 1000000000)) (hi := (39809831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167899) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 167899) = 1/(167899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55762271 / 31250000) (-1784392669 / 1000000000) (Real.log (167899 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151718201 / 250000000) ≤ -Real.log (200000 / 366937) ∧
    -Real.log (200000 / 366937) ≤ (121374561 / 200000000) := by
  have h := checkLog_sound (w := (166937 / 566937)) (n := 12)
    (lo := (151718201 / 250000000)) (hi := (121374561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366937 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366937 / 200000) = 1/(200000 / 366937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151718201 / 250000000) (121374561 / 200000000) (Real.log (366937 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (366937 / 200000) = -Real.log (200000 / 366937) := by
    rw [show ((366937 / 200000) : ℝ) = ((200000 / 366937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1799902533 / 1000000000) ≤ -Real.log (33063 / 200000) ∧
    -Real.log (33063 / 200000) ≤ (224987817 / 125000000) := by
  have h := checkLog_sound (w := (16937 / 83063)) (n := 12)
    (lo := (413608173 / 1000000000)) (hi := (206804087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33063) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 33063) = 1/(33063 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224987817 / 125000000) (-1799902533 / 1000000000) (Real.log (33063 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (592195819 / 1000000000) ≤ -Real.log (500000 / 903977) ∧
    -Real.log (500000 / 903977) ≤ (29609791 / 50000000) := by
  have h := checkLog_sound (w := (403977 / 1403977)) (n := 12)
    (lo := (592195819 / 1000000000)) (hi := (29609791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903977 / 500000) = 1/(500000 / 903977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (592195819 / 1000000000) (29609791 / 50000000) (Real.log (903977 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (903977 / 500000) = -Real.log (500000 / 903977) := by
    rw [show ((903977 / 500000) : ℝ) = ((500000 / 903977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1650020351 / 1000000000) ≤ -Real.log (96023 / 500000) ∧
    -Real.log (96023 / 500000) ≤ (825010177 / 500000000) := by
  have h := checkLog_sound (w := (28977 / 221023)) (n := 12)
    (lo := (263725991 / 1000000000)) (hi := (32965749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96023) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 96023) = 1/(96023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-825010177 / 500000000) (-1650020351 / 1000000000) (Real.log (96023 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (594353941 / 1000000000) ≤ -Real.log (50000 / 90593) ∧
    -Real.log (50000 / 90593) ≤ (297176971 / 500000000) := by
  have h := checkLog_sound (w := (40593 / 140593)) (n := 12)
    (lo := (594353941 / 1000000000)) (hi := (297176971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90593 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90593 / 50000) = 1/(50000 / 90593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (594353941 / 1000000000) (297176971 / 500000000) (Real.log (90593 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90593 / 50000) = -Real.log (50000 / 90593) := by
    rw [show ((90593 / 50000) : ℝ) = ((50000 / 90593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1670568911 / 1000000000) ≤ -Real.log (9407 / 50000) ∧
    -Real.log (9407 / 50000) ≤ (835284457 / 500000000) := by
  have h := checkLog_sound (w := (3093 / 21907)) (n := 12)
    (lo := (284274551 / 1000000000)) (hi := (35534319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9407) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9407) = 1/(9407 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-835284457 / 500000000) (-1670568911 / 1000000000) (Real.log (9407 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37341501 / 15625000) ≤ -Real.log (500000000000 / 5455961619783) ∧
    -Real.log (500000000000 / 5455961619783) ≤ (597464017 / 250000000) := by
  have h := checkLog_sound (w := (1455961619783 / 9455961619783)) (n := 12)
    (lo := (77603631 / 250000000)) (hi := (12416581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5455961619783 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5455961619783 / 4000000000000) = 1/(500000000000 / 5455961619783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37341501 / 15625000) (597464017 / 250000000) (Real.log (5455961619783 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5455961619783 / 500000000000) = -Real.log (500000000000 / 5455961619783) := by
    rw [show ((5455961619783 / 500000000000) : ℝ) = ((500000000000 / 5455961619783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2406775337 / 1000000000) ≤ -Real.log (500000000000 / 5549057859239) ∧
    -Real.log (500000000000 / 5549057859239) ≤ (2406775341 / 1000000000) := by
  have h := checkLog_sound (w := (1549057859239 / 9549057859239)) (n := 12)
    (lo := (327333797 / 1000000000)) (hi := (163666899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5549057859239 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5549057859239 / 4000000000000) = 1/(500000000000 / 5549057859239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2406775337 / 1000000000) (2406775341 / 1000000000) (Real.log (5549057859239 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5549057859239 / 500000000000) = -Real.log (500000000000 / 5549057859239) := by
    rw [show ((5549057859239 / 500000000000) : ℝ) = ((500000000000 / 5549057859239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2242216169 / 1000000000) ≤ -Real.log (500000000000 / 4707085802359) ∧
    -Real.log (500000000000 / 4707085802359) ≤ (2242216173 / 1000000000) := by
  have h := checkLog_sound (w := (707085802359 / 8707085802359)) (n := 12)
    (lo := (162774629 / 1000000000)) (hi := (16277463 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4707085802359 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4707085802359 / 4000000000000) = 1/(500000000000 / 4707085802359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2242216169 / 1000000000) (2242216173 / 1000000000) (Real.log (4707085802359 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4707085802359 / 500000000000) = -Real.log (500000000000 / 4707085802359) := by
    rw [show ((4707085802359 / 500000000000) : ℝ) = ((500000000000 / 4707085802359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (566230713 / 250000000) ≤ -Real.log (500000000000 / 4815190815351) ∧
    -Real.log (500000000000 / 4815190815351) ≤ (283115357 / 125000000) := by
  have h := checkLog_sound (w := (815190815351 / 8815190815351)) (n := 12)
    (lo := (5796291 / 31250000)) (hi := (185481313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4815190815351 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4815190815351 / 4000000000000) = 1/(500000000000 / 4815190815351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (566230713 / 250000000) (283115357 / 125000000) (Real.log (4815190815351 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4815190815351 / 500000000000) = -Real.log (500000000000 / 4815190815351) := by
    rw [show ((4815190815351 / 500000000000) : ℝ) = ((500000000000 / 4815190815351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0211
