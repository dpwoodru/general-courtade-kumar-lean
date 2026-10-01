import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell235
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

theorem reflection_log_1_neg : (328066471 / 1000000000) ≤ -Real.log (1280 / 1777) ∧
    -Real.log (1280 / 1777) ≤ (41008309 / 125000000) := by
  have h := checkLog_sound (w := (497 / 3057)) (n := 12)
    (lo := (328066471 / 1000000000)) (hi := (41008309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777 / 1280) = 1/(1280 / 1777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (328066471 / 1000000000) (41008309 / 125000000) (Real.log (1777 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1777 / 1280) = -Real.log (1280 / 1777) := by
    rw [show ((1777 / 1280) : ℝ) = ((1280 / 1777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24574133 / 50000000) ≤ -Real.log (783 / 1280) ∧
    -Real.log (783 / 1280) ≤ (491482661 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 2063)) (n := 12)
    (lo := (24574133 / 50000000)) (hi := (491482661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 783) = 1/(783 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-491482661 / 1000000000) (-24574133 / 50000000) (Real.log (783 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (163822161 / 500000000) ≤ -Real.log (1024 / 1421) ∧
    -Real.log (1024 / 1421) ≤ (327644323 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 2445)) (n := 12)
    (lo := (163822161 / 500000000)) (hi := (327644323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1024) = 1/(1024 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (163822161 / 500000000) (327644323 / 1000000000) (Real.log (1421 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1421 / 1024) = -Real.log (1024 / 1421) := by
    rw [show ((1421 / 1024) : ℝ) = ((1024 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (30657829 / 62500000) ≤ -Real.log (627 / 1024) ∧
    -Real.log (627 / 1024) ≤ (98105053 / 200000000) := by
  have h := checkLog_sound (w := (397 / 1651)) (n := 12)
    (lo := (30657829 / 62500000)) (hi := (98105053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 627) = 1/(627 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-98105053 / 200000000) (-30657829 / 62500000) (Real.log (627 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1903989 / 7812500) ≤ -Real.log (40000 / 51039) ∧
    -Real.log (40000 / 51039) ≤ (243710593 / 1000000000) := by
  have h := checkLog_sound (w := (11039 / 91039)) (n := 12)
    (lo := (1903989 / 7812500)) (hi := (243710593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51039 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51039 / 40000) = 1/(40000 / 51039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1903989 / 7812500) (243710593 / 1000000000) (Real.log (51039 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (51039 / 40000) = -Real.log (40000 / 51039) := by
    rw [show ((51039 / 40000) : ℝ) = ((40000 / 51039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (80732339 / 250000000) ≤ -Real.log (28961 / 40000) ∧
    -Real.log (28961 / 40000) ≤ (322929357 / 1000000000) := by
  have h := checkLog_sound (w := (11039 / 68961)) (n := 12)
    (lo := (80732339 / 250000000)) (hi := (322929357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28961) = 1/(28961 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-322929357 / 1000000000) (-80732339 / 250000000) (Real.log (28961 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (244042831 / 1000000000) ≤ -Real.log (1000000 / 1276399) ∧
    -Real.log (1000000 / 1276399) ≤ (15252677 / 62500000) := by
  have h := checkLog_sound (w := (276399 / 2276399)) (n := 12)
    (lo := (244042831 / 1000000000)) (hi := (15252677 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276399 / 1000000) = 1/(1000000 / 1276399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (244042831 / 1000000000) (15252677 / 62500000) (Real.log (1276399 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1276399 / 1000000) = -Real.log (1000000 / 1276399) := by
    rw [show ((1276399 / 1000000) : ℝ) = ((1000000 / 1276399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323515143 / 1000000000) ≤ -Real.log (723601 / 1000000) ∧
    -Real.log (723601 / 1000000) ≤ (40439393 / 125000000) := by
  have h := checkLog_sound (w := (276399 / 1723601)) (n := 12)
    (lo := (323515143 / 1000000000)) (hi := (40439393 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723601) = 1/(723601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40439393 / 125000000) (-323515143 / 1000000000) (Real.log (723601 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7271123 / 40000000) ≤ -Real.log (250000 / 299837) ∧
    -Real.log (250000 / 299837) ≤ (45444519 / 250000000) := by
  have h := checkLog_sound (w := (49837 / 549837)) (n := 12)
    (lo := (7271123 / 40000000)) (hi := (45444519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299837 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299837 / 250000) = 1/(250000 / 299837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7271123 / 40000000) (45444519 / 250000000) (Real.log (299837 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299837 / 250000) = -Real.log (250000 / 299837) := by
    rw [show ((299837 / 250000) : ℝ) = ((250000 / 299837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (222328883 / 1000000000) ≤ -Real.log (200163 / 250000) ∧
    -Real.log (200163 / 250000) ≤ (55582221 / 250000000) := by
  have h := checkLog_sound (w := (49837 / 450163)) (n := 12)
    (lo := (222328883 / 1000000000)) (hi := (55582221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200163) = 1/(200163 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55582221 / 250000000) (-222328883 / 1000000000) (Real.log (200163 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182044851 / 1000000000) ≤ -Real.log (250000 / 299917) ∧
    -Real.log (250000 / 299917) ≤ (45511213 / 250000000) := by
  have h := checkLog_sound (w := (49917 / 549917)) (n := 12)
    (lo := (182044851 / 1000000000)) (hi := (45511213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299917 / 250000) = 1/(250000 / 299917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182044851 / 1000000000) (45511213 / 250000000) (Real.log (299917 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (299917 / 250000) = -Real.log (250000 / 299917) := by
    rw [show ((299917 / 250000) : ℝ) = ((250000 / 299917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (222728637 / 1000000000) ≤ -Real.log (200083 / 250000) ∧
    -Real.log (200083 / 250000) ≤ (111364319 / 500000000) := by
  have h := checkLog_sound (w := (49917 / 450083)) (n := 12)
    (lo := (222728637 / 1000000000)) (hi := (111364319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200083) = 1/(200083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-111364319 / 500000000) (-222728637 / 1000000000) (Real.log (200083 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (409084793 / 500000000) ≤ -Real.log (5000000000 / 11331738437) ∧
    -Real.log (5000000000 / 11331738437) ≤ (204542397 / 250000000) := by
  have h := checkLog_sound (w := (1331738437 / 21331738437)) (n := 12)
    (lo := (62511203 / 500000000)) (hi := (125022407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11331738437 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11331738437 / 10000000000) = 1/(5000000000 / 11331738437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (409084793 / 500000000) (204542397 / 250000000) (Real.log (11331738437 / 5000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (11331738437 / 5000000000) = -Real.log (5000000000 / 11331738437) := by
    rw [show ((11331738437 / 5000000000) : ℝ) = ((5000000000 / 11331738437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (819549131 / 1000000000) ≤ -Real.log (500000000000 / 1134738186463) ∧
    -Real.log (500000000000 / 1134738186463) ≤ (819549133 / 1000000000) := by
  have h := checkLog_sound (w := (134738186463 / 2134738186463)) (n := 12)
    (lo := (126401951 / 1000000000)) (hi := (3950061 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134738186463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1134738186463 / 1000000000000) = 1/(500000000000 / 1134738186463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (819549131 / 1000000000) (819549133 / 1000000000) (Real.log (1134738186463 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1134738186463 / 500000000000) = -Real.log (500000000000 / 1134738186463) := by
    rw [show ((1134738186463 / 500000000000) : ℝ) = ((500000000000 / 1134738186463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (566639949 / 1000000000) ≤ -Real.log (100000000000 / 176233555471) ∧
    -Real.log (100000000000 / 176233555471) ≤ (11332799 / 20000000) := by
  have h := checkLog_sound (w := (76233555471 / 276233555471)) (n := 12)
    (lo := (566639949 / 1000000000)) (hi := (11332799 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176233555471 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176233555471 / 100000000000) = 1/(100000000000 / 176233555471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (566639949 / 1000000000) (11332799 / 20000000) (Real.log (176233555471 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (176233555471 / 100000000000) = -Real.log (100000000000 / 176233555471) := by
    rw [show ((176233555471 / 100000000000) : ℝ) = ((100000000000 / 176233555471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22702319 / 40000000) ≤ -Real.log (62500000000 / 110247135507) ∧
    -Real.log (62500000000 / 110247135507) ≤ (70944747 / 125000000) := by
  have h := checkLog_sound (w := (47747135507 / 172747135507)) (n := 12)
    (lo := (22702319 / 40000000)) (hi := (70944747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110247135507 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110247135507 / 62500000000) = 1/(62500000000 / 110247135507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (22702319 / 40000000) (70944747 / 125000000) (Real.log (110247135507 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (110247135507 / 62500000000) = -Real.log (62500000000 / 110247135507) := by
    rw [show ((110247135507 / 62500000000) : ℝ) = ((62500000000 / 110247135507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (404106959 / 1000000000) ≤ -Real.log (100000000000 / 149796415921) ∧
    -Real.log (100000000000 / 149796415921) ≤ (5051337 / 12500000) := by
  have h := checkLog_sound (w := (49796415921 / 249796415921)) (n := 12)
    (lo := (404106959 / 1000000000)) (hi := (5051337 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149796415921 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149796415921 / 100000000000) = 1/(100000000000 / 149796415921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (404106959 / 1000000000) (5051337 / 12500000) (Real.log (149796415921 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (149796415921 / 100000000000) = -Real.log (100000000000 / 149796415921) := by
    rw [show ((149796415921 / 100000000000) : ℝ) = ((100000000000 / 149796415921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404773489 / 1000000000) ≤ -Real.log (62500000000 / 93685183149) ∧
    -Real.log (62500000000 / 93685183149) ≤ (40477349 / 100000000) := by
  have h := checkLog_sound (w := (31185183149 / 156185183149)) (n := 12)
    (lo := (404773489 / 1000000000)) (hi := (40477349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93685183149 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93685183149 / 62500000000) = 1/(62500000000 / 93685183149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404773489 / 1000000000) (40477349 / 100000000) (Real.log (93685183149 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (93685183149 / 62500000000) = -Real.log (62500000000 / 93685183149) := by
    rw [show ((93685183149 / 62500000000) : ℝ) = ((62500000000 / 93685183149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8136757 / 200000000) ≤ -Real.log (60008293111 / 62500000000) ∧
    -Real.log (60008293111 / 62500000000) ≤ (20341893 / 500000000) := by
  have h := checkLog_sound (w := (2491706889 / 122508293111)) (n := 12)
    (lo := (8136757 / 200000000)) (hi := (20341893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60008293111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60008293111) = 1/(60008293111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20341893 / 500000000) (-8136757 / 200000000) (Real.log (60008293111 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (40550807 / 1000000000) ≤ -Real.log (60016273431 / 62500000000) ∧
    -Real.log (60016273431 / 62500000000) ≤ (5068851 / 125000000) := by
  have h := checkLog_sound (w := (2483726569 / 122516273431)) (n := 12)
    (lo := (40550807 / 1000000000)) (hi := (5068851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60016273431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60016273431) = 1/(60016273431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5068851 / 125000000) (-40550807 / 1000000000) (Real.log (60016273431 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell235
