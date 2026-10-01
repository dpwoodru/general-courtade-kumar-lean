import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0176
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

theorem reflection_log_1_neg : (126470329 / 200000000) ≤ -Real.log (1280 / 2409) ∧
    -Real.log (1280 / 2409) ≤ (316175823 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3689)) (n := 12)
    (lo := (126470329 / 200000000)) (hi := (316175823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2409 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2409 / 1280) = 1/(1280 / 2409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (126470329 / 200000000) (316175823 / 500000000) (Real.log (2409 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2409 / 1280) = -Real.log (1280 / 2409) := by
    rw [show ((2409 / 1280) : ℝ) = ((1280 / 2409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1068667759 / 500000000) ≤ -Real.log (151 / 1280) ∧
    -Real.log (151 / 1280) ≤ (1068667761 / 500000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 151) = 1/(151 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1068667761 / 500000000) (-1068667759 / 500000000) (Real.log (151 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (315386491 / 500000000) ≤ -Real.log (3200 / 6013) ∧
    -Real.log (3200 / 6013) ≤ (630772983 / 1000000000) := by
  have h := checkLog_sound (w := (2813 / 9213)) (n := 12)
    (lo := (315386491 / 500000000)) (hi := (630772983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013 / 3200) = 1/(3200 / 6013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (315386491 / 500000000) (630772983 / 1000000000) (Real.log (6013 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6013 / 3200) = -Real.log (3200 / 6013) := by
    rw [show ((6013 / 3200) : ℝ) = ((3200 / 6013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1056240697 / 500000000) ≤ -Real.log (387 / 3200) ∧
    -Real.log (387 / 3200) ≤ (1056240699 / 500000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 387) = 1/(387 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1056240699 / 500000000) (-1056240697 / 500000000) (Real.log (387 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (567619387 / 1000000000) ≤ -Real.log (640 / 1129) ∧
    -Real.log (640 / 1129) ≤ (141904847 / 250000000) := by
  have h := checkLog_sound (w := (489 / 1769)) (n := 12)
    (lo := (567619387 / 1000000000)) (hi := (141904847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129 / 640) = 1/(640 / 1129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (567619387 / 1000000000) (141904847 / 250000000) (Real.log (1129 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1129 / 640) = -Real.log (640 / 1129) := by
    rw [show ((1129 / 640) : ℝ) = ((640 / 1129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (722094169 / 500000000) ≤ -Real.log (151 / 640) ∧
    -Real.log (151 / 640) ≤ (1444188341 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 151) = 1/(151 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1444188341 / 1000000000) (-722094169 / 500000000) (Real.log (151 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (5642479 / 10000000) ≤ -Real.log (1600 / 2813) ∧
    -Real.log (1600 / 2813) ≤ (564247901 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 4413)) (n := 12)
    (lo := (5642479 / 10000000)) (hi := (564247901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2813 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2813 / 1600) = 1/(1600 / 2813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (5642479 / 10000000) (564247901 / 1000000000) (Real.log (2813 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2813 / 1600) = -Real.log (1600 / 2813) := by
    rw [show ((2813 / 1600) : ℝ) = ((1600 / 2813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (709667107 / 500000000) ≤ -Real.log (387 / 1600) ∧
    -Real.log (387 / 1600) ≤ (1419334217 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 787)) (n := 12)
    (lo := (16519927 / 500000000)) (hi := (6607971 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 387) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 387) = 1/(387 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1419334217 / 1000000000) (-709667107 / 500000000) (Real.log (387 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (646803197 / 1000000000) ≤ -Real.log (1000000 / 1909427) ∧
    -Real.log (1000000 / 1909427) ≤ (323401599 / 500000000) := by
  have h := checkLog_sound (w := (909427 / 2909427)) (n := 12)
    (lo := (646803197 / 1000000000)) (hi := (323401599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909427 / 1000000) = 1/(1000000 / 1909427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (646803197 / 1000000000) (323401599 / 500000000) (Real.log (1909427 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1909427 / 1000000) = -Real.log (1000000 / 1909427) := by
    rw [show ((1909427 / 1000000) : ℝ) = ((1000000 / 1909427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2401599121 / 1000000000) ≤ -Real.log (90573 / 1000000) ∧
    -Real.log (90573 / 1000000) ≤ (19212793 / 8000000) := by
  have h := checkLog_sound (w := (34427 / 215573)) (n := 12)
    (lo := (322157581 / 1000000000)) (hi := (161078791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90573) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 90573) = 1/(90573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19212793 / 8000000) (-2401599121 / 1000000000) (Real.log (90573 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (647818169 / 1000000000) ≤ -Real.log (500000 / 955683) ∧
    -Real.log (500000 / 955683) ≤ (64781817 / 100000000) := by
  have h := checkLog_sound (w := (455683 / 1455683)) (n := 12)
    (lo := (647818169 / 1000000000)) (hi := (64781817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955683 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955683 / 500000) = 1/(500000 / 955683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (647818169 / 1000000000) (64781817 / 100000000) (Real.log (955683 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (955683 / 500000) = -Real.log (500000 / 955683) := by
    rw [show ((955683 / 500000) : ℝ) = ((500000 / 955683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1211619873 / 500000000) ≤ -Real.log (44317 / 500000) ∧
    -Real.log (44317 / 500000) ≤ (9692959 / 4000000) := by
  have h := checkLog_sound (w := (18183 / 106817)) (n := 12)
    (lo := (171899103 / 500000000)) (hi := (343798207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44317) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44317) = 1/(44317 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9692959 / 4000000) (-1211619873 / 500000000) (Real.log (44317 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (322432831 / 500000000) ≤ -Real.log (1000000 / 1905731) ∧
    -Real.log (1000000 / 1905731) ≤ (644865663 / 1000000000) := by
  have h := checkLog_sound (w := (905731 / 2905731)) (n := 12)
    (lo := (322432831 / 500000000)) (hi := (644865663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1905731 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1905731 / 1000000) = 1/(1000000 / 1905731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (322432831 / 500000000) (644865663 / 1000000000) (Real.log (1905731 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1905731 / 1000000) = -Real.log (1000000 / 1905731) := by
    rw [show ((1905731 / 1000000) : ℝ) = ((1000000 / 1905731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2361602879 / 1000000000) ≤ -Real.log (94269 / 1000000) ∧
    -Real.log (94269 / 1000000) ≤ (2361602883 / 1000000000) := by
  have h := checkLog_sound (w := (30731 / 219269)) (n := 12)
    (lo := (282161339 / 1000000000)) (hi := (14108067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94269) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 94269) = 1/(94269 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2361602883 / 1000000000) (-2361602879 / 1000000000) (Real.log (94269 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (322996601 / 500000000) ≤ -Real.log (1000000 / 1907881) ∧
    -Real.log (1000000 / 1907881) ≤ (645993203 / 1000000000) := by
  have h := checkLog_sound (w := (907881 / 2907881)) (n := 12)
    (lo := (322996601 / 500000000)) (hi := (645993203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1907881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1907881 / 1000000) = 1/(1000000 / 1907881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (322996601 / 500000000) (645993203 / 1000000000) (Real.log (1907881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1907881 / 1000000) = -Real.log (1000000 / 1907881) := by
    rw [show ((1907881 / 1000000) : ℝ) = ((1000000 / 1907881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2384674057 / 1000000000) ≤ -Real.log (92119 / 1000000) ∧
    -Real.log (92119 / 1000000) ≤ (2384674061 / 1000000000) := by
  have h := checkLog_sound (w := (32881 / 217119)) (n := 12)
    (lo := (305232517 / 1000000000)) (hi := (152616259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 92119) = 1/(92119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2384674061 / 1000000000) (-2384674057 / 1000000000) (Real.log (92119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1524201159 / 500000000) ≤ -Real.log (50000000000 / 1054081790379) ∧
    -Real.log (50000000000 / 1054081790379) ≤ (3048402323 / 1000000000) := by
  have h := checkLog_sound (w := (254081790379 / 1854081790379)) (n := 12)
    (lo := (137906799 / 500000000)) (hi := (275813599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054081790379 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1054081790379 / 800000000000) = 1/(50000000000 / 1054081790379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1524201159 / 500000000) (3048402323 / 1000000000) (Real.log (1054081790379 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1054081790379 / 50000000000) = -Real.log (50000000000 / 1054081790379) := by
    rw [show ((1054081790379 / 50000000000) : ℝ) = ((50000000000 / 1054081790379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (614211583 / 200000000) ≤ -Real.log (62500000000 / 1347794018097) ∧
    -Real.log (62500000000 / 1347794018097) ≤ (1199632 / 390625) := by
  have h := checkLog_sound (w := (347794018097 / 2347794018097)) (n := 12)
    (lo := (59693839 / 200000000)) (hi := (74617299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347794018097 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1347794018097 / 1000000000000) = 1/(62500000000 / 1347794018097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (614211583 / 200000000) (1199632 / 390625) (Real.log (1347794018097 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1347794018097 / 62500000000) = -Real.log (62500000000 / 1347794018097) := by
    rw [show ((1347794018097 / 62500000000) : ℝ) = ((62500000000 / 1347794018097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3006468541 / 1000000000) ≤ -Real.log (50000000000 / 1010794110471) ∧
    -Real.log (50000000000 / 1010794110471) ≤ (1503234273 / 500000000) := by
  have h := checkLog_sound (w := (210794110471 / 1810794110471)) (n := 12)
    (lo := (233879821 / 1000000000)) (hi := (116939911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1010794110471 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1010794110471 / 800000000000) = 1/(50000000000 / 1010794110471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3006468541 / 1000000000) (1503234273 / 500000000) (Real.log (1010794110471 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1010794110471 / 50000000000) = -Real.log (50000000000 / 1010794110471) := by
    rw [show ((1010794110471 / 50000000000) : ℝ) = ((50000000000 / 1010794110471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3030667259 / 1000000000) ≤ -Real.log (500000000000 / 10355523833303) ∧
    -Real.log (500000000000 / 10355523833303) ≤ (5919272 / 1953125) := by
  have h := checkLog_sound (w := (2355523833303 / 18355523833303)) (n := 12)
    (lo := (258078539 / 1000000000)) (hi := (12903927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10355523833303 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10355523833303 / 8000000000000) = 1/(500000000000 / 10355523833303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3030667259 / 1000000000) (5919272 / 1953125) (Real.log (10355523833303 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10355523833303 / 500000000000) = -Real.log (500000000000 / 10355523833303) := by
    rw [show ((10355523833303 / 500000000000) : ℝ) = ((500000000000 / 10355523833303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0176
