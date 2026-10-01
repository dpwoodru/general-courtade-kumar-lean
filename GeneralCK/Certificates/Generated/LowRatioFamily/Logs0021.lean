import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1344_neg : (87117173 / 500000000) ≤ -Real.log (8401 / 10000) ∧
    -Real.log (8401 / 10000) ≤ (174234347 / 1000000000) := by
  have h := checkLog_sound (w := (1599 / 18401)) (n := 12)
    (lo := (87117173 / 500000000)) (hi := (174234347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8401) = 1/(8401 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1344 : Bounds (-174234347 / 1000000000) (-87117173 / 500000000) (Real.log (8401 / 10000)) := by
  have h := reflection_log_1344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1345_neg : (159887 / 1000000000) ≤ -Real.log (10000000 / 10001599) ∧
    -Real.log (10000000 / 10001599) ≤ (9993 / 62500000) := by
  have h := checkLog_sound (w := (1599 / 20001599)) (n := 12)
    (lo := (159887 / 1000000000)) (hi := (9993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001599 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001599 / 10000000) = 1/(10000000 / 10001599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1345 : Bounds (159887 / 1000000000) (9993 / 62500000) (Real.log (10001599 / 10000000)) := by
  have h := reflection_log_1345_neg
  have he : Real.log (10001599 / 10000000) = -Real.log (10000000 / 10001599) := by
    rw [show ((10001599 / 10000000) : ℝ) = ((10000000 / 10001599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1346_neg : (19989 / 125000000) ≤ -Real.log (9998401 / 10000000) ∧
    -Real.log (9998401 / 10000000) ≤ (159913 / 1000000000) := by
  have h := checkLog_sound (w := (1599 / 19998401)) (n := 12)
    (lo := (19989 / 125000000)) (hi := (159913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998401) = 1/(9998401 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1346 : Bounds (-159913 / 1000000000) (-19989 / 125000000) (Real.log (9998401 / 10000000)) := by
  have h := reflection_log_1346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1347_neg : (77137877 / 1000000000) ≤ -Real.log (1000000 / 1080191) ∧
    -Real.log (1000000 / 1080191) ≤ (38568939 / 500000000) := by
  have h := checkLog_sound (w := (80191 / 2080191)) (n := 12)
    (lo := (77137877 / 1000000000)) (hi := (38568939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080191 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080191 / 1000000) = 1/(1000000 / 1080191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1347 : Bounds (77137877 / 1000000000) (38568939 / 500000000) (Real.log (1080191 / 1000000)) := by
  have h := reflection_log_1347_neg
  have he : Real.log (1080191 / 1000000) = -Real.log (1000000 / 1080191) := by
    rw [show ((1080191 / 1000000) : ℝ) = ((1000000 / 1080191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1348_neg : (83589239 / 1000000000) ≤ -Real.log (919809 / 1000000) ∧
    -Real.log (919809 / 1000000) ≤ (2089731 / 25000000) := by
  have h := checkLog_sound (w := (80191 / 1919809)) (n := 12)
    (lo := (83589239 / 1000000000)) (hi := (2089731 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919809) = 1/(919809 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1348 : Bounds (-2089731 / 25000000) (-83589239 / 1000000000) (Real.log (919809 / 1000000)) := by
  have h := reflection_log_1348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1349_neg : (19333067 / 250000000) ≤ -Real.log (1000000 / 1080401) ∧
    -Real.log (1000000 / 1080401) ≤ (77332269 / 1000000000) := by
  have h := checkLog_sound (w := (80401 / 2080401)) (n := 12)
    (lo := (19333067 / 250000000)) (hi := (77332269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080401 / 1000000) = 1/(1000000 / 1080401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1349 : Bounds (19333067 / 250000000) (77332269 / 1000000000) (Real.log (1080401 / 1000000)) := by
  have h := reflection_log_1349_neg
  have he : Real.log (1080401 / 1000000) = -Real.log (1000000 / 1080401) := by
    rw [show ((1080401 / 1000000) : ℝ) = ((1000000 / 1080401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1350_neg : (83817573 / 1000000000) ≤ -Real.log (919599 / 1000000) ∧
    -Real.log (919599 / 1000000) ≤ (41908787 / 500000000) := by
  have h := checkLog_sound (w := (80401 / 1919599)) (n := 12)
    (lo := (83817573 / 1000000000)) (hi := (41908787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919599) = 1/(919599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1350 : Bounds (-41908787 / 500000000) (-83817573 / 1000000000) (Real.log (919599 / 1000000)) := by
  have h := reflection_log_1350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1351_neg : (1297061 / 200000000) ≤ -Real.log (993535679199 / 1000000000000) ∧
    -Real.log (993535679199 / 1000000000000) ≤ (3242653 / 500000000) := by
  have h := checkLog_sound (w := (6464320801 / 1993535679199)) (n := 12)
    (lo := (1297061 / 200000000)) (hi := (3242653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993535679199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993535679199) = 1/(993535679199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1351 : Bounds (-3242653 / 500000000) (-1297061 / 200000000) (Real.log (993535679199 / 1000000000000)) := by
  have h := reflection_log_1351_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1352_neg : (6451361 / 1000000000) ≤ -Real.log (993569403519 / 1000000000000) ∧
    -Real.log (993569403519 / 1000000000000) ≤ (3225681 / 500000000) := by
  have h := checkLog_sound (w := (6430596481 / 1993569403519)) (n := 12)
    (lo := (6451361 / 1000000000)) (hi := (3225681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993569403519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993569403519) = 1/(993569403519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1352 : Bounds (-3225681 / 500000000) (-6451361 / 1000000000) (Real.log (993569403519 / 1000000000000)) := by
  have h := reflection_log_1352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1353_neg : (40181779 / 250000000) ≤ -Real.log (500000000000 / 587182230223) ∧
    -Real.log (500000000000 / 587182230223) ≤ (160727117 / 1000000000) := by
  have h := checkLog_sound (w := (87182230223 / 1087182230223)) (n := 12)
    (lo := (40181779 / 250000000)) (hi := (160727117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587182230223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587182230223 / 500000000000) = 1/(500000000000 / 587182230223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1353 : Bounds (40181779 / 250000000) (160727117 / 1000000000) (Real.log (587182230223 / 500000000000)) := by
  have h := reflection_log_1353_neg
  have he : Real.log (587182230223 / 500000000000) = -Real.log (500000000000 / 587182230223) := by
    rw [show ((587182230223 / 500000000000) : ℝ) = ((500000000000 / 587182230223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1354_neg : (80574921 / 500000000) ≤ -Real.log (500000000000 / 587430499599) ∧
    -Real.log (500000000000 / 587430499599) ≤ (161149843 / 1000000000) := by
  have h := checkLog_sound (w := (87430499599 / 1087430499599)) (n := 12)
    (lo := (80574921 / 500000000)) (hi := (161149843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587430499599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587430499599 / 500000000000) = 1/(500000000000 / 587430499599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1354 : Bounds (80574921 / 500000000) (161149843 / 1000000000) (Real.log (587430499599 / 500000000000)) := by
  have h := reflection_log_1354_neg
  have he : Real.log (587430499599 / 500000000000) = -Real.log (500000000000 / 587430499599) := by
    rw [show ((587430499599 / 500000000000) : ℝ) = ((500000000000 / 587430499599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1355_neg : (20147681 / 62500000) ≤ -Real.log (100000000000 / 138038562247) ∧
    -Real.log (100000000000 / 138038562247) ≤ (322362897 / 1000000000) := by
  have h := checkLog_sound (w := (38038562247 / 238038562247)) (n := 12)
    (lo := (20147681 / 62500000)) (hi := (322362897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138038562247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138038562247 / 100000000000) = 1/(100000000000 / 138038562247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1355 : Bounds (20147681 / 62500000) (322362897 / 1000000000) (Real.log (138038562247 / 100000000000)) := by
  have h := reflection_log_1355_neg
  have he : Real.log (138038562247 / 100000000000) = -Real.log (100000000000 / 138038562247) := by
    rw [show ((138038562247 / 100000000000) : ℝ) = ((100000000000 / 138038562247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1356_neg : (322568141 / 1000000000) ≤ -Real.log (500000000000 / 690334483991) ∧
    -Real.log (500000000000 / 690334483991) ≤ (161284071 / 500000000) := by
  have h := checkLog_sound (w := (190334483991 / 1190334483991)) (n := 12)
    (lo := (322568141 / 1000000000)) (hi := (161284071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690334483991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690334483991 / 500000000000) = 1/(500000000000 / 690334483991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1356 : Bounds (322568141 / 1000000000) (161284071 / 500000000) (Real.log (690334483991 / 500000000000)) := by
  have h := reflection_log_1356_neg
  have he : Real.log (690334483991 / 500000000000) = -Real.log (500000000000 / 690334483991) := by
    rw [show ((690334483991 / 500000000000) : ℝ) = ((500000000000 / 690334483991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1357_neg : (29684001 / 200000000) ≤ -Real.log (25 / 29) ∧
    -Real.log (25 / 29) ≤ (74210003 / 500000000) := by
  have h := checkLog_sound (w := (2 / 27)) (n := 12)
    (lo := (29684001 / 200000000)) (hi := (74210003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29 / 25) = 1/(25 / 29) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1357 : Bounds (29684001 / 200000000) (74210003 / 500000000) (Real.log (29 / 25)) := by
  have h := reflection_log_1357_neg
  have he : Real.log (29 / 25) = -Real.log (25 / 29) := by
    rw [show ((29 / 25) : ℝ) = ((25 / 29) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1358_neg : (174353387 / 1000000000) ≤ -Real.log (21 / 25) ∧
    -Real.log (21 / 25) ≤ (43588347 / 250000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 21) = 1/(21 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1358 : Bounds (-43588347 / 250000000) (-174353387 / 1000000000) (Real.log (21 / 25)) := by
  have h := reflection_log_1358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1359_neg : (159987 / 1000000000) ≤ -Real.log (6250 / 6251) ∧
    -Real.log (6250 / 6251) ≤ (39997 / 250000000) := by
  have h := checkLog_sound (w := (1 / 12501)) (n := 12)
    (lo := (159987 / 1000000000)) (hi := (39997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6251 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6251 / 6250) = 1/(6250 / 6251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1359 : Bounds (159987 / 1000000000) (39997 / 250000000) (Real.log (6251 / 6250)) := by
  have h := reflection_log_1359_neg
  have he : Real.log (6251 / 6250) = -Real.log (6250 / 6251) := by
    rw [show ((6251 / 6250) : ℝ) = ((6250 / 6251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1360_neg : (40003 / 250000000) ≤ -Real.log (6249 / 6250) ∧
    -Real.log (6249 / 6250) ≤ (160013 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 12499)) (n := 12)
    (lo := (40003 / 250000000)) (hi := (160013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 6249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 6249) = 1/(6249 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1360 : Bounds (-160013 / 1000000000) (-40003 / 250000000) (Real.log (6249 / 6250)) := by
  have h := reflection_log_1360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1361_neg : (19296041 / 250000000) ≤ -Real.log (1000000 / 1080241) ∧
    -Real.log (1000000 / 1080241) ≤ (15436833 / 200000000) := by
  have h := checkLog_sound (w := (80241 / 2080241)) (n := 12)
    (lo := (19296041 / 250000000)) (hi := (15436833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080241 / 1000000) = 1/(1000000 / 1080241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1361 : Bounds (19296041 / 250000000) (15436833 / 200000000) (Real.log (1080241 / 1000000)) := by
  have h := reflection_log_1361_neg
  have he : Real.log (1080241 / 1000000) = -Real.log (1000000 / 1080241) := by
    rw [show ((1080241 / 1000000) : ℝ) = ((1000000 / 1080241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1362_neg : (83643599 / 1000000000) ≤ -Real.log (919759 / 1000000) ∧
    -Real.log (919759 / 1000000) ≤ (209109 / 2500000) := by
  have h := checkLog_sound (w := (80241 / 1919759)) (n := 12)
    (lo := (83643599 / 1000000000)) (hi := (209109 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919759) = 1/(919759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1362 : Bounds (-209109 / 2500000) (-83643599 / 1000000000) (Real.log (919759 / 1000000)) := by
  have h := reflection_log_1362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1363_neg : (4836217 / 62500000) ≤ -Real.log (250000 / 270113) ∧
    -Real.log (250000 / 270113) ≤ (77379473 / 1000000000) := by
  have h := checkLog_sound (w := (20113 / 520113)) (n := 12)
    (lo := (4836217 / 62500000)) (hi := (77379473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270113 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270113 / 250000) = 1/(250000 / 270113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1363 : Bounds (4836217 / 62500000) (77379473 / 1000000000) (Real.log (270113 / 250000)) := by
  have h := reflection_log_1363_neg
  have he : Real.log (270113 / 250000) = -Real.log (250000 / 270113) := by
    rw [show ((270113 / 250000) : ℝ) = ((250000 / 270113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1364_neg : (41936517 / 500000000) ≤ -Real.log (229887 / 250000) ∧
    -Real.log (229887 / 250000) ≤ (16774607 / 200000000) := by
  have h := checkLog_sound (w := (20113 / 479887)) (n := 12)
    (lo := (41936517 / 500000000)) (hi := (16774607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229887) = 1/(229887 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1364 : Bounds (-16774607 / 200000000) (-41936517 / 500000000) (Real.log (229887 / 250000)) := by
  have h := reflection_log_1364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1365_neg : (6493561 / 1000000000) ≤ -Real.log (62095467231 / 62500000000) ∧
    -Real.log (62095467231 / 62500000000) ≤ (3246781 / 500000000) := by
  have h := checkLog_sound (w := (404532769 / 124595467231)) (n := 12)
    (lo := (6493561 / 1000000000)) (hi := (3246781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62095467231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62095467231) = 1/(62095467231 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1365 : Bounds (-3246781 / 500000000) (-6493561 / 1000000000) (Real.log (62095467231 / 62500000000)) := by
  have h := reflection_log_1365_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1366_neg : (1291887 / 200000000) ≤ -Real.log (993561381919 / 1000000000000) ∧
    -Real.log (993561381919 / 1000000000000) ≤ (1614859 / 250000000) := by
  have h := checkLog_sound (w := (6438618081 / 1993561381919)) (n := 12)
    (lo := (1291887 / 200000000)) (hi := (1614859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993561381919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993561381919) = 1/(993561381919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1366 : Bounds (-1614859 / 250000000) (-1291887 / 200000000) (Real.log (993561381919 / 1000000000000)) := by
  have h := reflection_log_1366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1367_neg : (40206941 / 250000000) ≤ -Real.log (31250000000 / 36702583231) ∧
    -Real.log (31250000000 / 36702583231) ≤ (32165553 / 200000000) := by
  have h := checkLog_sound (w := (5452583231 / 67952583231)) (n := 12)
    (lo := (40206941 / 250000000)) (hi := (32165553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36702583231 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36702583231 / 31250000000) = 1/(31250000000 / 36702583231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1367 : Bounds (40206941 / 250000000) (32165553 / 200000000) (Real.log (36702583231 / 31250000000)) := by
  have h := reflection_log_1367_neg
  have he : Real.log (36702583231 / 31250000000) = -Real.log (31250000000 / 36702583231) := by
    rw [show ((36702583231 / 31250000000) : ℝ) = ((31250000000 / 36702583231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1368_neg : (80626253 / 500000000) ≤ -Real.log (500000000000 / 587490810703) ∧
    -Real.log (500000000000 / 587490810703) ≤ (161252507 / 1000000000) := by
  have h := checkLog_sound (w := (87490810703 / 1087490810703)) (n := 12)
    (lo := (80626253 / 500000000)) (hi := (161252507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587490810703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587490810703 / 500000000000) = 1/(500000000000 / 587490810703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1368 : Bounds (80626253 / 500000000) (161252507 / 1000000000) (Real.log (587490810703 / 500000000000)) := by
  have h := reflection_log_1368_neg
  have he : Real.log (587490810703 / 500000000000) = -Real.log (500000000000 / 587490810703) := by
    rw [show ((587490810703 / 500000000000) : ℝ) = ((500000000000 / 587490810703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1369_neg : (322568141 / 1000000000) ≤ -Real.log (50000000000 / 69033448399) ∧
    -Real.log (50000000000 / 69033448399) ≤ (161284071 / 500000000) := by
  have h := checkLog_sound (w := (19033448399 / 119033448399)) (n := 12)
    (lo := (322568141 / 1000000000)) (hi := (161284071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69033448399 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69033448399 / 50000000000) = 1/(50000000000 / 69033448399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1369 : Bounds (322568141 / 1000000000) (161284071 / 500000000) (Real.log (69033448399 / 50000000000)) := by
  have h := reflection_log_1369_neg
  have he : Real.log (69033448399 / 50000000000) = -Real.log (50000000000 / 69033448399) := by
    rw [show ((69033448399 / 50000000000) : ℝ) = ((50000000000 / 69033448399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1370_neg : (20173337 / 62500000) ≤ -Real.log (500000000000 / 690476190477) ∧
    -Real.log (500000000000 / 690476190477) ≤ (322773393 / 1000000000) := by
  have h := checkLog_sound (w := (190476190477 / 1190476190477)) (n := 12)
    (lo := (20173337 / 62500000)) (hi := (322773393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690476190477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690476190477 / 500000000000) = 1/(500000000000 / 690476190477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1370 : Bounds (20173337 / 62500000) (322773393 / 1000000000) (Real.log (690476190477 / 500000000000)) := by
  have h := reflection_log_1370_neg
  have he : Real.log (690476190477 / 500000000000) = -Real.log (500000000000 / 690476190477) := by
    rw [show ((690476190477 / 500000000000) : ℝ) = ((500000000000 / 690476190477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1371_neg : (4640819 / 31250000) ≤ -Real.log (10000 / 11601) ∧
    -Real.log (10000 / 11601) ≤ (148506209 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 21601)) (n := 12)
    (lo := (4640819 / 31250000)) (hi := (148506209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11601 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11601 / 10000) = 1/(10000 / 11601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1371 : Bounds (4640819 / 31250000) (148506209 / 1000000000) (Real.log (11601 / 10000)) := by
  have h := reflection_log_1371_neg
  have he : Real.log (11601 / 10000) = -Real.log (10000 / 11601) := by
    rw [show ((11601 / 10000) : ℝ) = ((10000 / 11601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1372_neg : (174472441 / 1000000000) ≤ -Real.log (8399 / 10000) ∧
    -Real.log (8399 / 10000) ≤ (87236221 / 500000000) := by
  have h := checkLog_sound (w := (1601 / 18399)) (n := 12)
    (lo := (174472441 / 1000000000)) (hi := (87236221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8399) = 1/(8399 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1372 : Bounds (-87236221 / 500000000) (-174472441 / 1000000000) (Real.log (8399 / 10000)) := by
  have h := reflection_log_1372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1373_neg : (160087 / 1000000000) ≤ -Real.log (10000000 / 10001601) ∧
    -Real.log (10000000 / 10001601) ≤ (20011 / 125000000) := by
  have h := checkLog_sound (w := (1601 / 20001601)) (n := 12)
    (lo := (160087 / 1000000000)) (hi := (20011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001601 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001601 / 10000000) = 1/(10000000 / 10001601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1373 : Bounds (160087 / 1000000000) (20011 / 125000000) (Real.log (10001601 / 10000000)) := by
  have h := reflection_log_1373_neg
  have he : Real.log (10001601 / 10000000) = -Real.log (10000000 / 10001601) := by
    rw [show ((10001601 / 10000000) : ℝ) = ((10000000 / 10001601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1374_neg : (10007 / 62500000) ≤ -Real.log (9998399 / 10000000) ∧
    -Real.log (9998399 / 10000000) ≤ (160113 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 19998399)) (n := 12)
    (lo := (10007 / 62500000)) (hi := (160113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998399) = 1/(9998399 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1374 : Bounds (-160113 / 1000000000) (-10007 / 62500000) (Real.log (9998399 / 10000000)) := by
  have h := reflection_log_1374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1375_neg : (38615687 / 500000000) ≤ -Real.log (250000 / 270073) ∧
    -Real.log (250000 / 270073) ≤ (617851 / 8000000) := by
  have h := checkLog_sound (w := (20073 / 520073)) (n := 12)
    (lo := (38615687 / 500000000)) (hi := (617851 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270073 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270073 / 250000) = 1/(250000 / 270073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1375 : Bounds (38615687 / 500000000) (617851 / 8000000) (Real.log (270073 / 250000)) := by
  have h := reflection_log_1375_neg
  have he : Real.log (270073 / 250000) = -Real.log (250000 / 270073) := by
    rw [show ((270073 / 250000) : ℝ) = ((250000 / 270073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1376_neg : (1673981 / 20000000) ≤ -Real.log (229927 / 250000) ∧
    -Real.log (229927 / 250000) ≤ (83699051 / 1000000000) := by
  have h := checkLog_sound (w := (20073 / 479927)) (n := 12)
    (lo := (1673981 / 20000000)) (hi := (83699051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229927) = 1/(229927 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1376 : Bounds (-83699051 / 1000000000) (-1673981 / 20000000) (Real.log (229927 / 250000)) := by
  have h := reflection_log_1376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1377_neg : (77426673 / 1000000000) ≤ -Real.log (1000000 / 1080503) ∧
    -Real.log (1000000 / 1080503) ≤ (38713337 / 500000000) := by
  have h := checkLog_sound (w := (80503 / 2080503)) (n := 12)
    (lo := (77426673 / 1000000000)) (hi := (38713337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080503 / 1000000) = 1/(1000000 / 1080503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1377 : Bounds (77426673 / 1000000000) (38713337 / 500000000) (Real.log (1080503 / 1000000)) := by
  have h := reflection_log_1377_neg
  have he : Real.log (1080503 / 1000000) = -Real.log (1000000 / 1080503) := by
    rw [show ((1080503 / 1000000) : ℝ) = ((1000000 / 1080503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1378_neg : (83928497 / 1000000000) ≤ -Real.log (919497 / 1000000) ∧
    -Real.log (919497 / 1000000) ≤ (41964249 / 500000000) := by
  have h := checkLog_sound (w := (80503 / 1919497)) (n := 12)
    (lo := (83928497 / 1000000000)) (hi := (41964249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919497) = 1/(919497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1378 : Bounds (-41964249 / 500000000) (-83928497 / 1000000000) (Real.log (919497 / 1000000)) := by
  have h := reflection_log_1378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1379_neg : (101591 / 15625000) ≤ -Real.log (993519266991 / 1000000000000) ∧
    -Real.log (993519266991 / 1000000000000) ≤ (260073 / 40000000) := by
  have h := checkLog_sound (w := (6480733009 / 1993519266991)) (n := 12)
    (lo := (101591 / 15625000)) (hi := (260073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993519266991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993519266991) = 1/(993519266991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1379 : Bounds (-260073 / 40000000) (-101591 / 15625000) (Real.log (993519266991 / 1000000000000)) := by
  have h := reflection_log_1379_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1380_neg : (258707 / 40000000) ≤ -Real.log (62097074671 / 62500000000) ∧
    -Real.log (62097074671 / 62500000000) ≤ (1616919 / 250000000) := by
  have h := checkLog_sound (w := (402925329 / 124597074671)) (n := 12)
    (lo := (258707 / 40000000)) (hi := (1616919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62097074671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62097074671) = 1/(62097074671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1380 : Bounds (-1616919 / 250000000) (-258707 / 40000000) (Real.log (62097074671 / 62500000000)) := by
  have h := reflection_log_1380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1381_neg : (6437217 / 40000000) ≤ -Real.log (500000000000 / 587301621819) ∧
    -Real.log (500000000000 / 587301621819) ≤ (80465213 / 500000000) := by
  have h := checkLog_sound (w := (87301621819 / 1087301621819)) (n := 12)
    (lo := (6437217 / 40000000)) (hi := (80465213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587301621819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587301621819 / 500000000000) = 1/(500000000000 / 587301621819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1381 : Bounds (6437217 / 40000000) (80465213 / 500000000) (Real.log (587301621819 / 500000000000)) := by
  have h := reflection_log_1381_neg
  have he : Real.log (587301621819 / 500000000000) = -Real.log (500000000000 / 587301621819) := by
    rw [show ((587301621819 / 500000000000) : ℝ) = ((500000000000 / 587301621819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1382_neg : (161355171 / 1000000000) ≤ -Real.log (250000000000 / 293775564249) ∧
    -Real.log (250000000000 / 293775564249) ≤ (40338793 / 250000000) := by
  have h := checkLog_sound (w := (43775564249 / 543775564249)) (n := 12)
    (lo := (161355171 / 1000000000)) (hi := (40338793 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293775564249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293775564249 / 250000000000) = 1/(250000000000 / 293775564249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1382 : Bounds (161355171 / 1000000000) (40338793 / 250000000) (Real.log (293775564249 / 250000000000)) := by
  have h := reflection_log_1382_neg
  have he : Real.log (293775564249 / 250000000000) = -Real.log (250000000000 / 293775564249) := by
    rw [show ((293775564249 / 250000000000) : ℝ) = ((250000000000 / 293775564249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1383_neg : (20173337 / 62500000) ≤ -Real.log (125000000000 / 172619047619) ∧
    -Real.log (125000000000 / 172619047619) ≤ (322773393 / 1000000000) := by
  have h := checkLog_sound (w := (47619047619 / 297619047619)) (n := 12)
    (lo := (20173337 / 62500000)) (hi := (322773393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172619047619 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172619047619 / 125000000000) = 1/(125000000000 / 172619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1383 : Bounds (20173337 / 62500000) (322773393 / 1000000000) (Real.log (172619047619 / 125000000000)) := by
  have h := reflection_log_1383_neg
  have he : Real.log (172619047619 / 125000000000) = -Real.log (125000000000 / 172619047619) := by
    rw [show ((172619047619 / 125000000000) : ℝ) = ((125000000000 / 172619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1384_neg : (6459573 / 20000000) ≤ -Real.log (500000000000 / 690617930707) ∧
    -Real.log (500000000000 / 690617930707) ≤ (322978651 / 1000000000) := by
  have h := checkLog_sound (w := (190617930707 / 1190617930707)) (n := 12)
    (lo := (6459573 / 20000000)) (hi := (322978651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690617930707 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690617930707 / 500000000000) = 1/(500000000000 / 690617930707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1384 : Bounds (6459573 / 20000000) (322978651 / 1000000000) (Real.log (690617930707 / 500000000000)) := by
  have h := reflection_log_1384_neg
  have he : Real.log (690617930707 / 500000000000) = -Real.log (500000000000 / 690617930707) := by
    rw [show ((690617930707 / 500000000000) : ℝ) = ((500000000000 / 690617930707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1385_neg : (37148101 / 250000000) ≤ -Real.log (5000 / 5801) ∧
    -Real.log (5000 / 5801) ≤ (29718481 / 200000000) := by
  have h := checkLog_sound (w := (801 / 10801)) (n := 12)
    (lo := (37148101 / 250000000)) (hi := (29718481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5801 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5801 / 5000) = 1/(5000 / 5801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1385 : Bounds (37148101 / 250000000) (29718481 / 200000000) (Real.log (5801 / 5000)) := by
  have h := reflection_log_1385_neg
  have he : Real.log (5801 / 5000) = -Real.log (5000 / 5801) := by
    rw [show ((5801 / 5000) : ℝ) = ((5000 / 5801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1386_neg : (17459151 / 100000000) ≤ -Real.log (4199 / 5000) ∧
    -Real.log (4199 / 5000) ≤ (174591511 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 9199)) (n := 12)
    (lo := (17459151 / 100000000)) (hi := (174591511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4199) = 1/(4199 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1386 : Bounds (-174591511 / 1000000000) (-17459151 / 100000000) (Real.log (4199 / 5000)) := by
  have h := reflection_log_1386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1387_neg : (160187 / 1000000000) ≤ -Real.log (5000000 / 5000801) ∧
    -Real.log (5000000 / 5000801) ≤ (40047 / 250000000) := by
  have h := checkLog_sound (w := (801 / 10000801)) (n := 12)
    (lo := (160187 / 1000000000)) (hi := (40047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000801 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000801 / 5000000) = 1/(5000000 / 5000801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1387 : Bounds (160187 / 1000000000) (40047 / 250000000) (Real.log (5000801 / 5000000)) := by
  have h := reflection_log_1387_neg
  have he : Real.log (5000801 / 5000000) = -Real.log (5000000 / 5000801) := by
    rw [show ((5000801 / 5000000) : ℝ) = ((5000000 / 5000801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1388_neg : (40053 / 250000000) ≤ -Real.log (4999199 / 5000000) ∧
    -Real.log (4999199 / 5000000) ≤ (160213 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 9999199)) (n := 12)
    (lo := (40053 / 250000000)) (hi := (160213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999199) = 1/(4999199 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1388 : Bounds (-160213 / 1000000000) (-40053 / 250000000) (Real.log (4999199 / 5000000)) := by
  have h := reflection_log_1388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1389_neg : (77278583 / 1000000000) ≤ -Real.log (1000000 / 1080343) ∧
    -Real.log (1000000 / 1080343) ≤ (9659823 / 125000000) := by
  have h := checkLog_sound (w := (80343 / 2080343)) (n := 12)
    (lo := (77278583 / 1000000000)) (hi := (9659823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080343 / 1000000) = 1/(1000000 / 1080343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1389 : Bounds (77278583 / 1000000000) (9659823 / 125000000) (Real.log (1080343 / 1000000)) := by
  have h := reflection_log_1389_neg
  have he : Real.log (1080343 / 1000000) = -Real.log (1000000 / 1080343) := by
    rw [show ((1080343 / 1000000) : ℝ) = ((1000000 / 1080343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1390_neg : (10469313 / 125000000) ≤ -Real.log (919657 / 1000000) ∧
    -Real.log (919657 / 1000000) ≤ (16750901 / 200000000) := by
  have h := checkLog_sound (w := (80343 / 1919657)) (n := 12)
    (lo := (10469313 / 125000000)) (hi := (16750901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919657) = 1/(919657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1390 : Bounds (-16750901 / 200000000) (-10469313 / 125000000) (Real.log (919657 / 1000000)) := by
  have h := reflection_log_1390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1391_neg : (4842117 / 62500000) ≤ -Real.log (500000 / 540277) ∧
    -Real.log (500000 / 540277) ≤ (77473873 / 1000000000) := by
  have h := checkLog_sound (w := (40277 / 1040277)) (n := 12)
    (lo := (4842117 / 62500000)) (hi := (77473873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540277 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540277 / 500000) = 1/(500000 / 540277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1391 : Bounds (4842117 / 62500000) (77473873 / 1000000000) (Real.log (540277 / 500000)) := by
  have h := reflection_log_1391_neg
  have he : Real.log (540277 / 500000) = -Real.log (500000 / 540277) := by
    rw [show ((540277 / 500000) : ℝ) = ((500000 / 540277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1392_neg : (20995991 / 250000000) ≤ -Real.log (459723 / 500000) ∧
    -Real.log (459723 / 500000) ≤ (16796793 / 200000000) := by
  have h := checkLog_sound (w := (40277 / 959723)) (n := 12)
    (lo := (20995991 / 250000000)) (hi := (16796793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459723) = 1/(459723 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1392 : Bounds (-16796793 / 200000000) (-20995991 / 250000000) (Real.log (459723 / 500000)) := by
  have h := reflection_log_1392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1393_neg : (6510091 / 1000000000) ≤ -Real.log (248377763271 / 250000000000) ∧
    -Real.log (248377763271 / 250000000000) ≤ (1627523 / 250000000) := by
  have h := checkLog_sound (w := (1622236729 / 498377763271)) (n := 12)
    (lo := (6510091 / 1000000000)) (hi := (1627523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248377763271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248377763271) = 1/(248377763271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1393 : Bounds (-1627523 / 250000000) (-6510091 / 1000000000) (Real.log (248377763271 / 250000000000)) := by
  have h := reflection_log_1393_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1394_neg : (6475921 / 1000000000) ≤ -Real.log (993545002351 / 1000000000000) ∧
    -Real.log (993545002351 / 1000000000000) ≤ (3237961 / 500000000) := by
  have h := checkLog_sound (w := (6454997649 / 1993545002351)) (n := 12)
    (lo := (6475921 / 1000000000)) (hi := (3237961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993545002351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993545002351) = 1/(993545002351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1394 : Bounds (-3237961 / 500000000) (-6475921 / 1000000000) (Real.log (993545002351 / 1000000000000)) := by
  have h := reflection_log_1394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1395_neg : (161033087 / 1000000000) ≤ -Real.log (125000000000 / 146840479657) ∧
    -Real.log (125000000000 / 146840479657) ≤ (1258071 / 7812500) := by
  have h := checkLog_sound (w := (21840479657 / 271840479657)) (n := 12)
    (lo := (161033087 / 1000000000)) (hi := (1258071 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146840479657 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146840479657 / 125000000000) = 1/(125000000000 / 146840479657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1395 : Bounds (161033087 / 1000000000) (1258071 / 7812500) (Real.log (146840479657 / 125000000000)) := by
  have h := reflection_log_1395_neg
  have he : Real.log (146840479657 / 125000000000) = -Real.log (125000000000 / 146840479657) := by
    rw [show ((146840479657 / 125000000000) : ℝ) = ((125000000000 / 146840479657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1396_neg : (40364459 / 250000000) ≤ -Real.log (62500000000 / 73451431623) ∧
    -Real.log (62500000000 / 73451431623) ≤ (161457837 / 1000000000) := by
  have h := checkLog_sound (w := (10951431623 / 135951431623)) (n := 12)
    (lo := (40364459 / 250000000)) (hi := (161457837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73451431623 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73451431623 / 62500000000) = 1/(62500000000 / 73451431623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1396 : Bounds (40364459 / 250000000) (161457837 / 1000000000) (Real.log (73451431623 / 62500000000)) := by
  have h := reflection_log_1396_neg
  have he : Real.log (73451431623 / 62500000000) = -Real.log (62500000000 / 73451431623) := by
    rw [show ((73451431623 / 62500000000) : ℝ) = ((62500000000 / 73451431623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1397_neg : (6459573 / 20000000) ≤ -Real.log (250000000000 / 345308965353) ∧
    -Real.log (250000000000 / 345308965353) ≤ (322978651 / 1000000000) := by
  have h := checkLog_sound (w := (95308965353 / 595308965353)) (n := 12)
    (lo := (6459573 / 20000000)) (hi := (322978651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345308965353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345308965353 / 250000000000) = 1/(250000000000 / 345308965353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1397 : Bounds (6459573 / 20000000) (322978651 / 1000000000) (Real.log (345308965353 / 250000000000)) := by
  have h := reflection_log_1397_neg
  have he : Real.log (345308965353 / 250000000000) = -Real.log (250000000000 / 345308965353) := by
    rw [show ((345308965353 / 250000000000) : ℝ) = ((250000000000 / 345308965353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1398_neg : (161591957 / 500000000) ≤ -Real.log (125000000000 / 172689926173) ∧
    -Real.log (125000000000 / 172689926173) ≤ (64636783 / 200000000) := by
  have h := checkLog_sound (w := (47689926173 / 297689926173)) (n := 12)
    (lo := (161591957 / 500000000)) (hi := (64636783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172689926173 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172689926173 / 125000000000) = 1/(125000000000 / 172689926173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1398 : Bounds (161591957 / 500000000) (64636783 / 200000000) (Real.log (172689926173 / 125000000000)) := by
  have h := reflection_log_1398_neg
  have he : Real.log (172689926173 / 125000000000) = -Real.log (125000000000 / 172689926173) := by
    rw [show ((172689926173 / 125000000000) : ℝ) = ((125000000000 / 172689926173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1399_neg : (2323103 / 15625000) ≤ -Real.log (10000 / 11603) ∧
    -Real.log (10000 / 11603) ≤ (148678593 / 1000000000) := by
  have h := checkLog_sound (w := (1603 / 21603)) (n := 12)
    (lo := (2323103 / 15625000)) (hi := (148678593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11603 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11603 / 10000) = 1/(10000 / 11603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1399 : Bounds (2323103 / 15625000) (148678593 / 1000000000) (Real.log (11603 / 10000)) := by
  have h := reflection_log_1399_neg
  have he : Real.log (11603 / 10000) = -Real.log (10000 / 11603) := by
    rw [show ((11603 / 10000) : ℝ) = ((10000 / 11603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1400_neg : (174710593 / 1000000000) ≤ -Real.log (8397 / 10000) ∧
    -Real.log (8397 / 10000) ≤ (87355297 / 500000000) := by
  have h := checkLog_sound (w := (1603 / 18397)) (n := 12)
    (lo := (174710593 / 1000000000)) (hi := (87355297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8397) = 1/(8397 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1400 : Bounds (-87355297 / 500000000) (-174710593 / 1000000000) (Real.log (8397 / 10000)) := by
  have h := reflection_log_1400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1401_neg : (160287 / 1000000000) ≤ -Real.log (10000000 / 10001603) ∧
    -Real.log (10000000 / 10001603) ≤ (5009 / 31250000) := by
  have h := checkLog_sound (w := (1603 / 20001603)) (n := 12)
    (lo := (160287 / 1000000000)) (hi := (5009 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001603 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001603 / 10000000) = 1/(10000000 / 10001603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1401 : Bounds (160287 / 1000000000) (5009 / 31250000) (Real.log (10001603 / 10000000)) := by
  have h := reflection_log_1401_neg
  have he : Real.log (10001603 / 10000000) = -Real.log (10000000 / 10001603) := by
    rw [show ((10001603 / 10000000) : ℝ) = ((10000000 / 10001603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1402_neg : (20039 / 125000000) ≤ -Real.log (9998397 / 10000000) ∧
    -Real.log (9998397 / 10000000) ≤ (160313 / 1000000000) := by
  have h := checkLog_sound (w := (1603 / 19998397)) (n := 12)
    (lo := (20039 / 125000000)) (hi := (160313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998397) = 1/(9998397 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1402 : Bounds (-160313 / 1000000000) (-20039 / 125000000) (Real.log (9998397 / 10000000)) := by
  have h := reflection_log_1402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1403_neg : (77324863 / 1000000000) ≤ -Real.log (1000000 / 1080393) ∧
    -Real.log (1000000 / 1080393) ≤ (1208201 / 15625000) := by
  have h := checkLog_sound (w := (80393 / 2080393)) (n := 12)
    (lo := (77324863 / 1000000000)) (hi := (1208201 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080393 / 1000000) = 1/(1000000 / 1080393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1403 : Bounds (77324863 / 1000000000) (1208201 / 15625000) (Real.log (1080393 / 1000000)) := by
  have h := reflection_log_1403_neg
  have he : Real.log (1080393 / 1000000) = -Real.log (1000000 / 1080393) := by
    rw [show ((1080393 / 1000000) : ℝ) = ((1000000 / 1080393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1404_neg : (41904437 / 500000000) ≤ -Real.log (919607 / 1000000) ∧
    -Real.log (919607 / 1000000) ≤ (670471 / 8000000) := by
  have h := checkLog_sound (w := (80393 / 1919607)) (n := 12)
    (lo := (41904437 / 500000000)) (hi := (670471 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919607) = 1/(919607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1404 : Bounds (-670471 / 8000000) (-41904437 / 500000000) (Real.log (919607 / 1000000)) := by
  have h := reflection_log_1404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1405_neg : (77521069 / 1000000000) ≤ -Real.log (200000 / 216121) ∧
    -Real.log (200000 / 216121) ≤ (7752107 / 100000000) := by
  have h := checkLog_sound (w := (16121 / 416121)) (n := 12)
    (lo := (77521069 / 1000000000)) (hi := (7752107 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216121 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216121 / 200000) = 1/(200000 / 216121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1405 : Bounds (77521069 / 1000000000) (7752107 / 100000000) (Real.log (216121 / 200000)) := by
  have h := reflection_log_1405_neg
  have he : Real.log (216121 / 200000) = -Real.log (200000 / 216121) := by
    rw [show ((216121 / 200000) : ℝ) = ((200000 / 216121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1406_neg : (84039433 / 1000000000) ≤ -Real.log (183879 / 200000) ∧
    -Real.log (183879 / 200000) ≤ (42019717 / 500000000) := by
  have h := checkLog_sound (w := (16121 / 383879)) (n := 12)
    (lo := (84039433 / 1000000000)) (hi := (42019717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183879) = 1/(183879 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1406 : Bounds (-42019717 / 500000000) (-84039433 / 1000000000) (Real.log (183879 / 200000)) := by
  have h := reflection_log_1406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1407_neg : (1629591 / 250000000) ≤ -Real.log (39740113359 / 40000000000) ∧
    -Real.log (39740113359 / 40000000000) ≤ (1303673 / 200000000) := by
  have h := checkLog_sound (w := (259886641 / 79740113359)) (n := 12)
    (lo := (1629591 / 250000000)) (hi := (1303673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39740113359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39740113359) = 1/(39740113359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1407 : Bounds (-1303673 / 200000000) (-1629591 / 250000000) (Real.log (39740113359 / 40000000000)) := by
  have h := reflection_log_1407_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
