import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046
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

theorem reflection_log_1_neg : (339717719 / 500000000) ≤ -Real.log (102400 / 202011) ∧
    -Real.log (102400 / 202011) ≤ (679435439 / 1000000000) := by
  have h := checkLog_sound (w := (99611 / 304411)) (n := 12)
    (lo := (339717719 / 500000000)) (hi := (679435439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202011 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202011 / 102400) = 1/(102400 / 202011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (339717719 / 500000000) (679435439 / 1000000000) (Real.log (202011 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202011 / 102400) = -Real.log (102400 / 202011) := by
    rw [show ((202011 / 102400) : ℝ) = ((102400 / 202011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3603203601 / 1000000000) ≤ -Real.log (2789 / 102400) ∧
    -Real.log (2789 / 102400) ≤ (3603203607 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2789) = 1/(2789 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3603203607 / 1000000000) (-3603203601 / 1000000000) (Real.log (2789 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33967069 / 50000000) ≤ -Real.log (12800 / 25249) ∧
    -Real.log (12800 / 25249) ≤ (679341381 / 1000000000) := by
  have h := checkLog_sound (w := (12449 / 38049)) (n := 12)
    (lo := (33967069 / 50000000)) (hi := (679341381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25249 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25249 / 12800) = 1/(12800 / 25249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33967069 / 50000000) (679341381 / 1000000000) (Real.log (25249 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25249 / 12800) = -Real.log (12800 / 25249) := by
    rw [show ((25249 / 12800) : ℝ) = ((12800 / 25249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3596414223 / 1000000000) ≤ -Real.log (351 / 12800) ∧
    -Real.log (351 / 12800) ≤ (3596414229 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 351) = 1/(351 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3596414229 / 1000000000) (-3596414223 / 1000000000) (Real.log (351 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166383267 / 250000000) ≤ -Real.log (51200 / 99611) ∧
    -Real.log (51200 / 99611) ≤ (665533069 / 1000000000) := by
  have h := checkLog_sound (w := (48411 / 150811)) (n := 12)
    (lo := (166383267 / 250000000)) (hi := (665533069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99611 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99611 / 51200) = 1/(51200 / 99611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166383267 / 250000000) (665533069 / 1000000000) (Real.log (99611 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99611 / 51200) = -Real.log (51200 / 99611) := by
    rw [show ((99611 / 51200) : ℝ) = ((51200 / 99611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2910056421 / 1000000000) ≤ -Real.log (2789 / 51200) ∧
    -Real.log (2789 / 51200) ≤ (1455028213 / 500000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2789) = 1/(2789 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1455028213 / 500000000) (-2910056421 / 1000000000) (Real.log (2789 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166335577 / 250000000) ≤ -Real.log (6400 / 12449) ∧
    -Real.log (6400 / 12449) ≤ (665342309 / 1000000000) := by
  have h := checkLog_sound (w := (6049 / 18849)) (n := 12)
    (lo := (166335577 / 250000000)) (hi := (665342309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12449 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12449 / 6400) = 1/(6400 / 12449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166335577 / 250000000) (665342309 / 1000000000) (Real.log (12449 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12449 / 6400) = -Real.log (6400 / 12449) := by
    rw [show ((12449 / 6400) : ℝ) = ((6400 / 12449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2903267043 / 1000000000) ≤ -Real.log (351 / 6400) ∧
    -Real.log (351 / 6400) ≤ (362908381 / 125000000) := by
  have h := checkLog_sound (w := (49 / 751)) (n := 12)
    (lo := (130678323 / 1000000000)) (hi := (32669581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 351) = 1/(351 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-362908381 / 125000000) (-2903267043 / 1000000000) (Real.log (351 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681569921 / 1000000000) ≤ -Real.log (1000000 / 1976979) ∧
    -Real.log (1000000 / 1976979) ≤ (340784961 / 500000000) := by
  have h := checkLog_sound (w := (976979 / 2976979)) (n := 12)
    (lo := (681569921 / 1000000000)) (hi := (340784961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976979 / 1000000) = 1/(1000000 / 1976979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681569921 / 1000000000) (340784961 / 500000000) (Real.log (1976979 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1976979 / 1000000) = -Real.log (1000000 / 1976979) := by
    rw [show ((1976979 / 1000000) : ℝ) = ((1000000 / 1976979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3771348433 / 1000000000) ≤ -Real.log (23021 / 1000000) ∧
    -Real.log (23021 / 1000000) ≤ (3771348439 / 1000000000) := by
  have h := checkLog_sound (w := (8229 / 54271)) (n := 12)
    (lo := (305612533 / 1000000000)) (hi := (152806267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23021) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23021) = 1/(23021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3771348439 / 1000000000) (-3771348433 / 1000000000) (Real.log (23021 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21301431 / 31250000) ≤ -Real.log (1000000 / 1977129) ∧
    -Real.log (1000000 / 1977129) ≤ (681645793 / 1000000000) := by
  have h := checkLog_sound (w := (977129 / 2977129)) (n := 12)
    (lo := (21301431 / 31250000)) (hi := (681645793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977129 / 1000000) = 1/(1000000 / 1977129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21301431 / 31250000) (681645793 / 1000000000) (Real.log (1977129 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1977129 / 1000000) = -Real.log (1000000 / 1977129) := by
    rw [show ((1977129 / 1000000) : ℝ) = ((1000000 / 1977129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3777885543 / 1000000000) ≤ -Real.log (22871 / 1000000) ∧
    -Real.log (22871 / 1000000) ≤ (3777885549 / 1000000000) := by
  have h := checkLog_sound (w := (8379 / 54121)) (n := 12)
    (lo := (312149643 / 1000000000)) (hi := (78037411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22871) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22871) = 1/(22871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3777885549 / 1000000000) (-3777885543 / 1000000000) (Real.log (22871 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (340753599 / 500000000) ≤ -Real.log (200000 / 395371) ∧
    -Real.log (200000 / 395371) ≤ (681507199 / 1000000000) := by
  have h := checkLog_sound (w := (195371 / 595371)) (n := 12)
    (lo := (340753599 / 500000000)) (hi := (681507199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395371 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395371 / 200000) = 1/(200000 / 395371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (340753599 / 500000000) (681507199 / 1000000000) (Real.log (395371 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395371 / 200000) = -Real.log (200000 / 395371) := by
    rw [show ((395371 / 200000) : ℝ) = ((200000 / 395371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3765976501 / 1000000000) ≤ -Real.log (4629 / 200000) ∧
    -Real.log (4629 / 200000) ≤ (3765976507 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 10879)) (n := 12)
    (lo := (300240601 / 1000000000)) (hi := (150120301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4629) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4629) = 1/(4629 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3765976507 / 1000000000) (-3765976501 / 1000000000) (Real.log (4629 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681583579 / 1000000000) ≤ -Real.log (500000 / 988503) ∧
    -Real.log (500000 / 988503) ≤ (34079179 / 50000000) := by
  have h := checkLog_sound (w := (488503 / 1488503)) (n := 12)
    (lo := (681583579 / 1000000000)) (hi := (34079179 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988503 / 500000) = 1/(500000 / 988503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681583579 / 1000000000) (34079179 / 50000000) (Real.log (988503 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (988503 / 500000) = -Real.log (500000 / 988503) := by
    rw [show ((988503 / 500000) : ℝ) = ((500000 / 988503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3772521963 / 1000000000) ≤ -Real.log (11497 / 500000) ∧
    -Real.log (11497 / 500000) ≤ (3772521969 / 1000000000) := by
  have h := checkLog_sound (w := (2064 / 13561)) (n := 12)
    (lo := (306786063 / 1000000000)) (hi := (19174129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11497) = 1/(11497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3772521969 / 1000000000) (-3772521963 / 1000000000) (Real.log (11497 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2226459177 / 500000000) ≤ -Real.log (10000000000 / 858771990791) ∧
    -Real.log (10000000000 / 858771990791) ≤ (4452918361 / 1000000000) := by
  have h := checkLog_sound (w := (218771990791 / 1498771990791)) (n := 12)
    (lo := (147017637 / 500000000)) (hi := (11761411 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858771990791 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(858771990791 / 640000000000) = 1/(10000000000 / 858771990791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2226459177 / 500000000) (4452918361 / 1000000000) (Real.log (858771990791 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (858771990791 / 10000000000) = -Real.log (10000000000 / 858771990791) := by
    rw [show ((858771990791 / 10000000000) : ℝ) = ((10000000000 / 858771990791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (891906267 / 200000000) ≤ -Real.log (31250000000 / 2701468289537) ∧
    -Real.log (31250000000 / 2701468289537) ≤ (2229765671 / 500000000) := by
  have h := checkLog_sound (w := (701468289537 / 4701468289537)) (n := 12)
    (lo := (60129651 / 200000000)) (hi := (4697629 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2701468289537 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2701468289537 / 2000000000000) = 1/(31250000000 / 2701468289537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (891906267 / 200000000) (2229765671 / 500000000) (Real.log (2701468289537 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2701468289537 / 31250000000) = -Real.log (31250000000 / 2701468289537) := by
    rw [show ((2701468289537 / 31250000000) : ℝ) = ((31250000000 / 2701468289537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4447483699 / 1000000000) ≤ -Real.log (100000000000 / 8541175199827) ∧
    -Real.log (100000000000 / 8541175199827) ≤ (2223741853 / 500000000) := by
  have h := checkLog_sound (w := (2141175199827 / 14941175199827)) (n := 12)
    (lo := (288600619 / 1000000000)) (hi := (14430031 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8541175199827 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8541175199827 / 6400000000000) = 1/(100000000000 / 8541175199827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4447483699 / 1000000000) (2223741853 / 500000000) (Real.log (8541175199827 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8541175199827 / 100000000000) = -Real.log (100000000000 / 8541175199827) := by
    rw [show ((8541175199827 / 100000000000) : ℝ) = ((100000000000 / 8541175199827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2227052771 / 500000000) ≤ -Real.log (50000000000 / 4298960598417) ∧
    -Real.log (50000000000 / 4298960598417) ≤ (4454105549 / 1000000000) := by
  have h := checkLog_sound (w := (1098960598417 / 7498960598417)) (n := 12)
    (lo := (147611231 / 500000000)) (hi := (295222463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4298960598417 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4298960598417 / 3200000000000) = 1/(50000000000 / 4298960598417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2227052771 / 500000000) (4454105549 / 1000000000) (Real.log (4298960598417 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4298960598417 / 50000000000) = -Real.log (50000000000 / 4298960598417) := by
    rw [show ((4298960598417 / 50000000000) : ℝ) = ((50000000000 / 4298960598417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046
