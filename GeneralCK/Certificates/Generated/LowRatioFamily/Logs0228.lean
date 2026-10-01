import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14592_neg : (353777229 / 125000000) ≤ -Real.log (59 / 1000) ∧
    -Real.log (59 / 1000) ≤ (2830217837 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 243)) (n := 12)
    (lo := (7203639 / 125000000)) (hi := (57629113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 118) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 118) = 1/(59 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14592 : Bounds (-2830217837 / 1000000000) (-353777229 / 125000000) (Real.log (59 / 1000)) := by
  have h := reflection_log_14592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14593_neg : (940557 / 1000000000) ≤ -Real.log (1000000 / 1000941) ∧
    -Real.log (1000000 / 1000941) ≤ (470279 / 500000000) := by
  have h := checkLog_sound (w := (941 / 2000941)) (n := 12)
    (lo := (940557 / 1000000000)) (hi := (470279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000941 / 1000000) = 1/(1000000 / 1000941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14593 : Bounds (940557 / 1000000000) (470279 / 500000000) (Real.log (1000941 / 1000000)) := by
  have h := reflection_log_14593_neg
  have he : Real.log (1000941 / 1000000) = -Real.log (1000000 / 1000941) := by
    rw [show ((1000941 / 1000000) : ℝ) = ((1000000 / 1000941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14594_neg : (941443 / 1000000000) ≤ -Real.log (999059 / 1000000) ∧
    -Real.log (999059 / 1000000) ≤ (235361 / 250000000) := by
  have h := checkLog_sound (w := (941 / 1999059)) (n := 12)
    (lo := (941443 / 1000000000)) (hi := (235361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999059) = 1/(999059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14594 : Bounds (-235361 / 250000000) (-941443 / 1000000000) (Real.log (999059 / 1000000)) := by
  have h := reflection_log_14594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14595_neg : (91434963 / 200000000) ≤ -Real.log (200000 / 315921) ∧
    -Real.log (200000 / 315921) ≤ (14286713 / 31250000) := by
  have h := checkLog_sound (w := (115921 / 515921)) (n := 12)
    (lo := (91434963 / 200000000)) (hi := (14286713 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315921 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315921 / 200000) = 1/(200000 / 315921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14595 : Bounds (91434963 / 200000000) (14286713 / 31250000) (Real.log (315921 / 200000)) := by
  have h := reflection_log_14595_neg
  have he : Real.log (315921 / 200000) = -Real.log (200000 / 315921) := by
    rw [show ((315921 / 200000) : ℝ) = ((200000 / 315921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14596_neg : (216640133 / 250000000) ≤ -Real.log (84079 / 200000) ∧
    -Real.log (84079 / 200000) ≤ (433280267 / 500000000) := by
  have h := checkLog_sound (w := (15921 / 184079)) (n := 12)
    (lo := (21676669 / 125000000)) (hi := (173413353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84079) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 84079) = 1/(84079 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14596 : Bounds (-433280267 / 500000000) (-216640133 / 250000000) (Real.log (84079 / 200000)) := by
  have h := reflection_log_14596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14597_neg : (459580749 / 1000000000) ≤ -Real.log (100000 / 158341) ∧
    -Real.log (100000 / 158341) ≤ (1838323 / 4000000) := by
  have h := checkLog_sound (w := (58341 / 258341)) (n := 12)
    (lo := (459580749 / 1000000000)) (hi := (1838323 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158341 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158341 / 100000) = 1/(100000 / 158341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14597 : Bounds (459580749 / 1000000000) (1838323 / 4000000) (Real.log (158341 / 100000)) := by
  have h := reflection_log_14597_neg
  have he : Real.log (158341 / 100000) = -Real.log (100000 / 158341) := by
    rw [show ((158341 / 100000) : ℝ) = ((100000 / 158341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14598_neg : (875652753 / 1000000000) ≤ -Real.log (41659 / 100000) ∧
    -Real.log (41659 / 100000) ≤ (175130551 / 200000000) := by
  have h := checkLog_sound (w := (8341 / 91659)) (n := 12)
    (lo := (182505573 / 1000000000)) (hi := (91252787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 41659) = 1/(41659 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14598 : Bounds (-175130551 / 200000000) (-875652753 / 1000000000) (Real.log (41659 / 100000)) := by
  have h := reflection_log_14598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14599_neg : (83214401 / 200000000) ≤ -Real.log (6596327719 / 10000000000) ∧
    -Real.log (6596327719 / 10000000000) ≤ (208036003 / 500000000) := by
  have h := checkLog_sound (w := (3403672281 / 16596327719)) (n := 12)
    (lo := (83214401 / 200000000)) (hi := (208036003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6596327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6596327719) = 1/(6596327719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14599 : Bounds (-208036003 / 500000000) (-83214401 / 200000000) (Real.log (6596327719 / 10000000000)) := by
  have h := reflection_log_14599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14600_neg : (409385717 / 1000000000) ≤ -Real.log (26562321759 / 40000000000) ∧
    -Real.log (26562321759 / 40000000000) ≤ (204692859 / 500000000) := by
  have h := checkLog_sound (w := (13437678241 / 66562321759)) (n := 12)
    (lo := (409385717 / 1000000000)) (hi := (204692859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 26562321759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 26562321759) = 1/(26562321759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14600 : Bounds (-204692859 / 500000000) (-409385717 / 1000000000) (Real.log (26562321759 / 40000000000)) := by
  have h := reflection_log_14600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14601_neg : (330933837 / 250000000) ≤ -Real.log (50000000000 / 187871525589) ∧
    -Real.log (50000000000 / 187871525589) ≤ (26474707 / 20000000) := by
  have h := checkLog_sound (w := (87871525589 / 287871525589)) (n := 12)
    (lo := (78823521 / 125000000)) (hi := (630588169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187871525589 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(187871525589 / 100000000000) = 1/(50000000000 / 187871525589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14601 : Bounds (330933837 / 250000000) (26474707 / 20000000) (Real.log (187871525589 / 50000000000)) := by
  have h := reflection_log_14601_neg
  have he : Real.log (187871525589 / 50000000000) = -Real.log (50000000000 / 187871525589) := by
    rw [show ((187871525589 / 50000000000) : ℝ) = ((50000000000 / 187871525589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14602_neg : (667616751 / 500000000) ≤ -Real.log (50000000000 / 190044168127) ∧
    -Real.log (50000000000 / 190044168127) ≤ (41726047 / 31250000) := by
  have h := checkLog_sound (w := (90044168127 / 290044168127)) (n := 12)
    (lo := (321043161 / 500000000)) (hi := (642086323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190044168127 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(190044168127 / 100000000000) = 1/(50000000000 / 190044168127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14602 : Bounds (667616751 / 500000000) (41726047 / 31250000) (Real.log (190044168127 / 50000000000)) := by
  have h := reflection_log_14602_neg
  have he : Real.log (190044168127 / 50000000000) = -Real.log (50000000000 / 190044168127) := by
    rw [show ((190044168127 / 50000000000) : ℝ) = ((50000000000 / 190044168127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14603_neg : (688455481 / 200000000) ≤ -Real.log (31250000000 / 976814516129) ∧
    -Real.log (31250000000 / 976814516129) ≤ (344227741 / 100000000) := by
  have h := checkLog_sound (w := (476814516129 / 1476814516129)) (n := 12)
    (lo := (133937737 / 200000000)) (hi := (334844343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976814516129 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(976814516129 / 500000000000) = 1/(31250000000 / 976814516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14603 : Bounds (688455481 / 200000000) (344227741 / 100000000) (Real.log (976814516129 / 31250000000)) := by
  have h := reflection_log_14603_neg
  have he : Real.log (976814516129 / 31250000000) = -Real.log (31250000000 / 976814516129) := by
    rw [show ((976814516129 / 31250000000) : ℝ) = ((31250000000 / 976814516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14604_neg : (218338821 / 62500000) ≤ -Real.log (500000000000 / 16449152542373) ∧
    -Real.log (500000000000 / 16449152542373) ≤ (1746710571 / 500000000) := by
  have h := checkLog_sound (w := (449152542373 / 32449152542373)) (n := 12)
    (lo := (6921309 / 250000000)) (hi := (27685237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16449152542373 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16449152542373 / 16000000000000) = 1/(500000000000 / 16449152542373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14604 : Bounds (218338821 / 62500000) (1746710571 / 500000000) (Real.log (16449152542373 / 500000000000)) := by
  have h := reflection_log_14604_neg
  have he : Real.log (16449152542373 / 500000000000) = -Real.log (500000000000 / 16449152542373) := by
    rw [show ((16449152542373 / 500000000000) : ℝ) = ((500000000000 / 16449152542373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14605_neg : (332373853 / 500000000) ≤ -Real.log (125 / 243) ∧
    -Real.log (125 / 243) ≤ (664747707 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 184)) (n := 12)
    (lo := (332373853 / 500000000)) (hi := (664747707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 125) = 1/(125 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14605 : Bounds (332373853 / 500000000) (664747707 / 1000000000) (Real.log (243 / 125)) := by
  have h := reflection_log_14605_neg
  have he : Real.log (243 / 125) = -Real.log (125 / 243) := by
    rw [show ((243 / 125) : ℝ) = ((125 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14606_neg : (1441201793 / 500000000) ≤ -Real.log (7 / 125) ∧
    -Real.log (7 / 125) ≤ (2882403591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 112) = 1/(7 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14606 : Bounds (-2882403591 / 1000000000) (-1441201793 / 500000000) (Real.log (7 / 125)) := by
  have h := reflection_log_14606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14607_neg : (471777 / 500000000) ≤ -Real.log (62500 / 62559) ∧
    -Real.log (62500 / 62559) ≤ (188711 / 200000000) := by
  have h := checkLog_sound (w := (59 / 125059)) (n := 12)
    (lo := (471777 / 500000000)) (hi := (188711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62559 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62559 / 62500) = 1/(62500 / 62559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14607 : Bounds (471777 / 500000000) (188711 / 200000000) (Real.log (62559 / 62500)) := by
  have h := reflection_log_14607_neg
  have he : Real.log (62559 / 62500) = -Real.log (62500 / 62559) := by
    rw [show ((62559 / 62500) : ℝ) = ((62500 / 62559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14608_neg : (188889 / 200000000) ≤ -Real.log (62441 / 62500) ∧
    -Real.log (62441 / 62500) ≤ (472223 / 500000000) := by
  have h := checkLog_sound (w := (59 / 124941)) (n := 12)
    (lo := (188889 / 200000000)) (hi := (472223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62441) = 1/(62441 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14608 : Bounds (-472223 / 500000000) (-188889 / 200000000) (Real.log (62441 / 62500)) := by
  have h := reflection_log_14608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14609_neg : (459161313 / 1000000000) ≤ -Real.log (500000 / 791373) ∧
    -Real.log (500000 / 791373) ≤ (229580657 / 500000000) := by
  have h := checkLog_sound (w := (291373 / 1291373)) (n := 12)
    (lo := (459161313 / 1000000000)) (hi := (229580657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791373 / 500000) = 1/(500000 / 791373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14609 : Bounds (459161313 / 1000000000) (229580657 / 500000000) (Real.log (791373 / 500000)) := by
  have h := reflection_log_14609_neg
  have he : Real.log (791373 / 500000) = -Real.log (500000 / 791373) := by
    rw [show ((791373 / 500000) : ℝ) = ((500000 / 791373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14610_neg : (874060129 / 1000000000) ≤ -Real.log (208627 / 500000) ∧
    -Real.log (208627 / 500000) ≤ (874060131 / 1000000000) := by
  have h := checkLog_sound (w := (41373 / 458627)) (n := 12)
    (lo := (180912949 / 1000000000)) (hi := (3618259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208627) = 1/(208627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14610 : Bounds (-874060131 / 1000000000) (-874060129 / 1000000000) (Real.log (208627 / 500000)) := by
  have h := reflection_log_14610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14611_neg : (461583907 / 1000000000) ≤ -Real.log (200000 / 317317) ∧
    -Real.log (200000 / 317317) ≤ (115395977 / 250000000) := by
  have h := checkLog_sound (w := (117317 / 517317)) (n := 12)
    (lo := (461583907 / 1000000000)) (hi := (115395977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317317 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317317 / 200000) = 1/(200000 / 317317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14611 : Bounds (461583907 / 1000000000) (115395977 / 250000000) (Real.log (317317 / 200000)) := by
  have h := reflection_log_14611_neg
  have he : Real.log (317317 / 200000) = -Real.log (200000 / 317317) := by
    rw [show ((317317 / 200000) : ℝ) = ((200000 / 317317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14612_neg : (883303347 / 1000000000) ≤ -Real.log (82683 / 200000) ∧
    -Real.log (82683 / 200000) ≤ (883303349 / 1000000000) := by
  have h := checkLog_sound (w := (17317 / 182683)) (n := 12)
    (lo := (190156167 / 1000000000)) (hi := (23769521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82683) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 82683) = 1/(82683 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14612 : Bounds (-883303349 / 1000000000) (-883303347 / 1000000000) (Real.log (82683 / 200000)) := by
  have h := reflection_log_14612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14613_neg : (5271493 / 12500000) ≤ -Real.log (26236721511 / 40000000000) ∧
    -Real.log (26236721511 / 40000000000) ≤ (421719441 / 1000000000) := by
  have h := checkLog_sound (w := (13763278489 / 66236721511)) (n := 12)
    (lo := (5271493 / 12500000)) (hi := (421719441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 26236721511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 26236721511) = 1/(26236721511 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14613 : Bounds (-421719441 / 1000000000) (-5271493 / 12500000) (Real.log (26236721511 / 40000000000)) := by
  have h := reflection_log_14613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14614_neg : (3241397 / 7812500) ≤ -Real.log (165101774871 / 250000000000) ∧
    -Real.log (165101774871 / 250000000000) ≤ (414898817 / 1000000000) := by
  have h := checkLog_sound (w := (84898225129 / 415101774871)) (n := 12)
    (lo := (3241397 / 7812500)) (hi := (414898817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 165101774871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 165101774871) = 1/(165101774871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14614 : Bounds (-414898817 / 1000000000) (-3241397 / 7812500) (Real.log (165101774871 / 250000000000)) := by
  have h := reflection_log_14614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14615_neg : (666610721 / 500000000) ≤ -Real.log (25000000000 / 94831086101) ∧
    -Real.log (25000000000 / 94831086101) ≤ (333305361 / 250000000) := by
  have h := checkLog_sound (w := (44831086101 / 144831086101)) (n := 12)
    (lo := (320037131 / 500000000)) (hi := (640074263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94831086101 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94831086101 / 50000000000) = 1/(25000000000 / 94831086101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14615 : Bounds (666610721 / 500000000) (333305361 / 250000000) (Real.log (94831086101 / 25000000000)) := by
  have h := reflection_log_14615_neg
  have he : Real.log (94831086101 / 25000000000) = -Real.log (25000000000 / 94831086101) := by
    rw [show ((94831086101 / 25000000000) : ℝ) = ((25000000000 / 94831086101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14616_neg : (268977451 / 200000000) ≤ -Real.log (500000000000 / 1918876915449) ∧
    -Real.log (500000000000 / 1918876915449) ≤ (1344887257 / 1000000000) := by
  have h := checkLog_sound (w := (918876915449 / 2918876915449)) (n := 12)
    (lo := (26069603 / 40000000)) (hi := (162935019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918876915449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1918876915449 / 1000000000000) = 1/(500000000000 / 1918876915449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14616 : Bounds (268977451 / 200000000) (1344887257 / 1000000000) (Real.log (1918876915449 / 500000000000)) := by
  have h := reflection_log_14616_neg
  have he : Real.log (1918876915449 / 500000000000) = -Real.log (500000000000 / 1918876915449) := by
    rw [show ((1918876915449 / 500000000000) : ℝ) = ((500000000000 / 1918876915449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14617_neg : (218338821 / 62500000) ≤ -Real.log (125000000000 / 4112288135593) ∧
    -Real.log (125000000000 / 4112288135593) ≤ (1746710571 / 500000000) := by
  have h := checkLog_sound (w := (112288135593 / 8112288135593)) (n := 12)
    (lo := (6921309 / 250000000)) (hi := (27685237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4112288135593 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4112288135593 / 4000000000000) = 1/(125000000000 / 4112288135593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14617 : Bounds (218338821 / 62500000) (1746710571 / 500000000) (Real.log (4112288135593 / 125000000000)) := by
  have h := reflection_log_14617_neg
  have he : Real.log (4112288135593 / 125000000000) = -Real.log (125000000000 / 4112288135593) := by
    rw [show ((4112288135593 / 125000000000) : ℝ) = ((125000000000 / 4112288135593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14618_neg : (3547151291 / 1000000000) ≤ -Real.log (500000000000 / 17357142857143) ∧
    -Real.log (500000000000 / 17357142857143) ≤ (3547151297 / 1000000000) := by
  have h := checkLog_sound (w := (1357142857143 / 33357142857143)) (n := 12)
    (lo := (81415391 / 1000000000)) (hi := (2544231 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17357142857143 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17357142857143 / 16000000000000) = 1/(500000000000 / 17357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14618 : Bounds (3547151291 / 1000000000) (3547151297 / 1000000000) (Real.log (17357142857143 / 500000000000)) := by
  have h := reflection_log_14618_neg
  have he : Real.log (17357142857143 / 500000000000) = -Real.log (500000000000 / 17357142857143) := by
    rw [show ((17357142857143 / 500000000000) : ℝ) = ((500000000000 / 17357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14619_neg : (333144863 / 500000000) ≤ -Real.log (1000 / 1947) ∧
    -Real.log (1000 / 1947) ≤ (666289727 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 2947)) (n := 12)
    (lo := (333144863 / 500000000)) (hi := (666289727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947 / 1000) = 1/(1000 / 1947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14619 : Bounds (333144863 / 500000000) (666289727 / 1000000000) (Real.log (1947 / 1000)) := by
  have h := reflection_log_14619_neg
  have he : Real.log (1947 / 1000) = -Real.log (1000 / 1947) := by
    rw [show ((1947 / 1000) : ℝ) = ((1000 / 1947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14620_neg : (2937463363 / 1000000000) ≤ -Real.log (53 / 1000) ∧
    -Real.log (53 / 1000) ≤ (367182921 / 125000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 106) = 1/(53 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14620 : Bounds (-367182921 / 125000000) (-2937463363 / 1000000000) (Real.log (53 / 1000)) := by
  have h := reflection_log_14620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14621_neg : (946551 / 1000000000) ≤ -Real.log (1000000 / 1000947) ∧
    -Real.log (1000000 / 1000947) ≤ (118319 / 125000000) := by
  have h := checkLog_sound (w := (947 / 2000947)) (n := 12)
    (lo := (946551 / 1000000000)) (hi := (118319 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000947 / 1000000) = 1/(1000000 / 1000947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14621 : Bounds (946551 / 1000000000) (118319 / 125000000) (Real.log (1000947 / 1000000)) := by
  have h := reflection_log_14621_neg
  have he : Real.log (1000947 / 1000000) = -Real.log (1000000 / 1000947) := by
    rw [show ((1000947 / 1000000) : ℝ) = ((1000000 / 1000947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14622_neg : (118431 / 125000000) ≤ -Real.log (999053 / 1000000) ∧
    -Real.log (999053 / 1000000) ≤ (947449 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 1999053)) (n := 12)
    (lo := (118431 / 125000000)) (hi := (947449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999053) = 1/(999053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14622 : Bounds (-947449 / 1000000000) (-118431 / 125000000) (Real.log (999053 / 1000000)) := by
  have h := reflection_log_14622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14623_neg : (461165941 / 1000000000) ≤ -Real.log (500000 / 792961) ∧
    -Real.log (500000 / 792961) ≤ (230582971 / 500000000) := by
  have h := checkLog_sound (w := (292961 / 1292961)) (n := 12)
    (lo := (461165941 / 1000000000)) (hi := (230582971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792961 / 500000) = 1/(500000 / 792961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14623 : Bounds (461165941 / 1000000000) (230582971 / 500000000) (Real.log (792961 / 500000)) := by
  have h := reflection_log_14623_neg
  have he : Real.log (792961 / 500000) = -Real.log (500000 / 792961) := by
    rw [show ((792961 / 500000) : ℝ) = ((500000 / 792961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14624_neg : (220425229 / 250000000) ≤ -Real.log (207039 / 500000) ∧
    -Real.log (207039 / 500000) ≤ (440850459 / 500000000) := by
  have h := checkLog_sound (w := (42961 / 457039)) (n := 12)
    (lo := (23569217 / 125000000)) (hi := (188553737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207039) = 1/(207039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14624 : Bounds (-440850459 / 500000000) (-220425229 / 250000000) (Real.log (207039 / 500000)) := by
  have h := reflection_log_14624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14625_neg : (115901741 / 250000000) ≤ -Real.log (500000 / 794899) ∧
    -Real.log (500000 / 794899) ≤ (92721393 / 200000000) := by
  have h := checkLog_sound (w := (294899 / 1294899)) (n := 12)
    (lo := (115901741 / 250000000)) (hi := (92721393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794899 / 500000) = 1/(500000 / 794899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14625 : Bounds (115901741 / 250000000) (92721393 / 200000000) (Real.log (794899 / 500000)) := by
  have h := reflection_log_14625_neg
  have he : Real.log (794899 / 500000) = -Real.log (500000 / 794899) := by
    rw [show ((794899 / 500000) : ℝ) = ((500000 / 794899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14626_neg : (891105557 / 1000000000) ≤ -Real.log (205101 / 500000) ∧
    -Real.log (205101 / 500000) ≤ (891105559 / 1000000000) := by
  have h := checkLog_sound (w := (44899 / 455101)) (n := 12)
    (lo := (197958377 / 1000000000)) (hi := (98979189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 205101) = 1/(205101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14626 : Bounds (-891105559 / 1000000000) (-891105557 / 1000000000) (Real.log (205101 / 500000)) := by
  have h := reflection_log_14626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14627_neg : (427498593 / 1000000000) ≤ -Real.log (163034579799 / 250000000000) ∧
    -Real.log (163034579799 / 250000000000) ≤ (213749297 / 500000000) := by
  have h := checkLog_sound (w := (86965420201 / 413034579799)) (n := 12)
    (lo := (427498593 / 1000000000)) (hi := (213749297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 163034579799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 163034579799) = 1/(163034579799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14627 : Bounds (-213749297 / 500000000) (-427498593 / 1000000000) (Real.log (163034579799 / 250000000000)) := by
  have h := reflection_log_14627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14628_neg : (16821399 / 40000000) ≤ -Real.log (164173852479 / 250000000000) ∧
    -Real.log (164173852479 / 250000000000) ≤ (6570859 / 15625000) := by
  have h := checkLog_sound (w := (85826147521 / 414173852479)) (n := 12)
    (lo := (16821399 / 40000000)) (hi := (6570859 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 164173852479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 164173852479) = 1/(164173852479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14628 : Bounds (-6570859 / 15625000) (-16821399 / 40000000) (Real.log (164173852479 / 250000000000)) := by
  have h := reflection_log_14628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14629_neg : (671433429 / 500000000) ≤ -Real.log (62500000000 / 239375492057) ∧
    -Real.log (62500000000 / 239375492057) ≤ (67143343 / 50000000) := by
  have h := checkLog_sound (w := (114375492057 / 364375492057)) (n := 12)
    (lo := (324859839 / 500000000)) (hi := (649719679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239375492057 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239375492057 / 125000000000) = 1/(62500000000 / 239375492057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14629 : Bounds (671433429 / 500000000) (67143343 / 50000000) (Real.log (239375492057 / 62500000000)) := by
  have h := reflection_log_14629_neg
  have he : Real.log (239375492057 / 62500000000) = -Real.log (62500000000 / 239375492057) := by
    rw [show ((239375492057 / 62500000000) : ℝ) = ((62500000000 / 239375492057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14630_neg : (1354712521 / 1000000000) ≤ -Real.log (250000000000 / 968911658159) ∧
    -Real.log (250000000000 / 968911658159) ≤ (1354712523 / 1000000000) := by
  have h := checkLog_sound (w := (468911658159 / 1468911658159)) (n := 12)
    (lo := (661565341 / 1000000000)) (hi := (330782671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968911658159 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(968911658159 / 500000000000) = 1/(250000000000 / 968911658159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14630 : Bounds (1354712521 / 1000000000) (1354712523 / 1000000000) (Real.log (968911658159 / 250000000000)) := by
  have h := reflection_log_14630_neg
  have he : Real.log (968911658159 / 250000000000) = -Real.log (250000000000 / 968911658159) := by
    rw [show ((968911658159 / 250000000000) : ℝ) = ((250000000000 / 968911658159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14631_neg : (3547151291 / 1000000000) ≤ -Real.log (250000000000 / 8678571428571) ∧
    -Real.log (250000000000 / 8678571428571) ≤ (3547151297 / 1000000000) := by
  have h := checkLog_sound (w := (678571428571 / 16678571428571)) (n := 12)
    (lo := (81415391 / 1000000000)) (hi := (2544231 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8678571428571 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8678571428571 / 8000000000000) = 1/(250000000000 / 8678571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14631 : Bounds (3547151291 / 1000000000) (3547151297 / 1000000000) (Real.log (8678571428571 / 250000000000)) := by
  have h := reflection_log_14631_neg
  have he : Real.log (8678571428571 / 250000000000) = -Real.log (250000000000 / 8678571428571) := by
    rw [show ((8678571428571 / 250000000000) : ℝ) = ((250000000000 / 8678571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14632_neg : (3603753089 / 1000000000) ≤ -Real.log (250000000000 / 9183962264151) ∧
    -Real.log (250000000000 / 9183962264151) ≤ (720750619 / 200000000) := by
  have h := checkLog_sound (w := (1183962264151 / 17183962264151)) (n := 12)
    (lo := (138017189 / 1000000000)) (hi := (13801719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9183962264151 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9183962264151 / 8000000000000) = 1/(250000000000 / 9183962264151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14632 : Bounds (3603753089 / 1000000000) (720750619 / 200000000) (Real.log (9183962264151 / 250000000000)) := by
  have h := reflection_log_14632_neg
  have he : Real.log (9183962264151 / 250000000000) = -Real.log (250000000000 / 9183962264151) := by
    rw [show ((9183962264151 / 250000000000) : ℝ) = ((250000000000 / 9183962264151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14633_neg : (166957343 / 250000000) ≤ -Real.log (20 / 39) ∧
    -Real.log (20 / 39) ≤ (667829373 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 59)) (n := 12)
    (lo := (166957343 / 250000000)) (hi := (667829373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39 / 20) = 1/(20 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14633 : Bounds (166957343 / 250000000) (667829373 / 1000000000) (Real.log (39 / 20)) := by
  have h := reflection_log_14633_neg
  have he : Real.log (39 / 20) = -Real.log (20 / 39) := by
    rw [show ((39 / 20) : ℝ) = ((20 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14634_neg : (2995732271 / 1000000000) ≤ -Real.log (1 / 20) ∧
    -Real.log (1 / 20) ≤ (748933069 / 250000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 4) = 1/(1 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14634 : Bounds (-748933069 / 250000000) (-2995732271 / 1000000000) (Real.log (1 / 20)) := by
  have h := reflection_log_14634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14635_neg : (949549 / 1000000000) ≤ -Real.log (20000 / 20019) ∧
    -Real.log (20000 / 20019) ≤ (18991 / 20000000) := by
  have h := checkLog_sound (w := (19 / 40019)) (n := 12)
    (lo := (949549 / 1000000000)) (hi := (18991 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20019 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20019 / 20000) = 1/(20000 / 20019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14635 : Bounds (949549 / 1000000000) (18991 / 20000000) (Real.log (20019 / 20000)) := by
  have h := reflection_log_14635_neg
  have he : Real.log (20019 / 20000) = -Real.log (20000 / 20019) := by
    rw [show ((20019 / 20000) : ℝ) = ((20000 / 20019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14636_neg : (950451 / 1000000000) ≤ -Real.log (19981 / 20000) ∧
    -Real.log (19981 / 20000) ≤ (237613 / 250000000) := by
  have h := checkLog_sound (w := (19 / 39981)) (n := 12)
    (lo := (950451 / 1000000000)) (hi := (237613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19981) = 1/(19981 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14636 : Bounds (-237613 / 250000000) (-950451 / 1000000000) (Real.log (19981 / 20000)) := by
  have h := reflection_log_14636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14637_neg : (463191101 / 1000000000) ≤ -Real.log (1000000 / 1589137) ∧
    -Real.log (1000000 / 1589137) ≤ (231595551 / 500000000) := by
  have h := checkLog_sound (w := (589137 / 2589137)) (n := 12)
    (lo := (463191101 / 1000000000)) (hi := (231595551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1589137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1589137 / 1000000) = 1/(1000000 / 1589137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14637 : Bounds (463191101 / 1000000000) (231595551 / 500000000) (Real.log (1589137 / 1000000)) := by
  have h := reflection_log_14637_neg
  have he : Real.log (1589137 / 1000000) = -Real.log (1000000 / 1589137) := by
    rw [show ((1589137 / 1000000) : ℝ) = ((1000000 / 1589137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14638_neg : (222373863 / 250000000) ≤ -Real.log (410863 / 1000000) ∧
    -Real.log (410863 / 1000000) ≤ (444747727 / 500000000) := by
  have h := checkLog_sound (w := (89137 / 910863)) (n := 12)
    (lo := (12271767 / 62500000)) (hi := (196348273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410863) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 410863) = 1/(410863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14638 : Bounds (-444747727 / 500000000) (-222373863 / 250000000) (Real.log (410863 / 1000000)) := by
  have h := reflection_log_14638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14639_neg : (93130209 / 200000000) ≤ -Real.log (1000000 / 1593051) ∧
    -Real.log (1000000 / 1593051) ≤ (232825523 / 500000000) := by
  have h := checkLog_sound (w := (593051 / 2593051)) (n := 12)
    (lo := (93130209 / 200000000)) (hi := (232825523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593051 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593051 / 1000000) = 1/(1000000 / 1593051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14639 : Bounds (93130209 / 200000000) (232825523 / 500000000) (Real.log (1593051 / 1000000)) := by
  have h := reflection_log_14639_neg
  have he : Real.log (1593051 / 1000000) = -Real.log (1000000 / 1593051) := by
    rw [show ((1593051 / 1000000) : ℝ) = ((1000000 / 1593051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14640_neg : (899067407 / 1000000000) ≤ -Real.log (406949 / 1000000) ∧
    -Real.log (406949 / 1000000) ≤ (899067409 / 1000000000) := by
  have h := checkLog_sound (w := (93051 / 906949)) (n := 12)
    (lo := (205920227 / 1000000000)) (hi := (51480057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406949) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 406949) = 1/(406949 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14640 : Bounds (-899067409 / 1000000000) (-899067407 / 1000000000) (Real.log (406949 / 1000000)) := by
  have h := reflection_log_14640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14641_neg : (433416363 / 1000000000) ≤ -Real.log (648290511399 / 1000000000000) ∧
    -Real.log (648290511399 / 1000000000000) ≤ (108354091 / 250000000) := by
  have h := checkLog_sound (w := (351709488601 / 1648290511399)) (n := 12)
    (lo := (433416363 / 1000000000)) (hi := (108354091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 648290511399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 648290511399) = 1/(648290511399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14641 : Bounds (-108354091 / 250000000) (-433416363 / 1000000000) (Real.log (648290511399 / 1000000000000)) := by
  have h := reflection_log_14641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14642_neg : (426304351 / 1000000000) ≤ -Real.log (652917595231 / 1000000000000) ∧
    -Real.log (652917595231 / 1000000000000) ≤ (13322011 / 31250000) := by
  have h := checkLog_sound (w := (347082404769 / 1652917595231)) (n := 12)
    (lo := (426304351 / 1000000000)) (hi := (13322011 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 652917595231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 652917595231) = 1/(652917595231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14642 : Bounds (-13322011 / 31250000) (-426304351 / 1000000000) (Real.log (652917595231 / 1000000000000)) := by
  have h := reflection_log_14642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14643_neg : (676343277 / 500000000) ≤ -Real.log (125000000000 / 483475331193) ∧
    -Real.log (125000000000 / 483475331193) ≤ (338171639 / 250000000) := by
  have h := checkLog_sound (w := (233475331193 / 733475331193)) (n := 12)
    (lo := (329769687 / 500000000)) (hi := (1055263 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483475331193 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(483475331193 / 250000000000) = 1/(125000000000 / 483475331193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14643 : Bounds (676343277 / 500000000) (338171639 / 250000000) (Real.log (483475331193 / 125000000000)) := by
  have h := reflection_log_14643_neg
  have he : Real.log (483475331193 / 125000000000) = -Real.log (125000000000 / 483475331193) := by
    rw [show ((483475331193 / 125000000000) : ℝ) = ((125000000000 / 483475331193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14644_neg : (1364718453 / 1000000000) ≤ -Real.log (250000000000 / 978655187751) ∧
    -Real.log (250000000000 / 978655187751) ≤ (272943691 / 200000000) := by
  have h := checkLog_sound (w := (478655187751 / 1478655187751)) (n := 12)
    (lo := (671571273 / 1000000000)) (hi := (335785637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978655187751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(978655187751 / 500000000000) = 1/(250000000000 / 978655187751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14644 : Bounds (1364718453 / 1000000000) (272943691 / 200000000) (Real.log (978655187751 / 250000000000)) := by
  have h := reflection_log_14644_neg
  have he : Real.log (978655187751 / 250000000000) = -Real.log (250000000000 / 978655187751) := by
    rw [show ((978655187751 / 250000000000) : ℝ) = ((250000000000 / 978655187751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14645_neg : (3603753089 / 1000000000) ≤ -Real.log (500000000000 / 18367924528301) ∧
    -Real.log (500000000000 / 18367924528301) ≤ (720750619 / 200000000) := by
  have h := checkLog_sound (w := (2367924528301 / 34367924528301)) (n := 12)
    (lo := (138017189 / 1000000000)) (hi := (13801719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18367924528301 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18367924528301 / 16000000000000) = 1/(500000000000 / 18367924528301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14645 : Bounds (3603753089 / 1000000000) (720750619 / 200000000) (Real.log (18367924528301 / 500000000000)) := by
  have h := reflection_log_14645_neg
  have he : Real.log (18367924528301 / 500000000000) = -Real.log (500000000000 / 18367924528301) := by
    rw [show ((18367924528301 / 500000000000) : ℝ) = ((500000000000 / 18367924528301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14646_neg : (3663561643 / 1000000000) ≤ -Real.log (1 / 39) ∧
    -Real.log (1 / 39) ≤ (3663561649 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(39 / 32) = 1/(1 / 39) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14646 : Bounds (3663561643 / 1000000000) (3663561649 / 1000000000) (Real.log (39 / 1)) := by
  have h := reflection_log_14646_neg
  have he : Real.log (39 / 1) = -Real.log (1 / 39) := by
    rw [show ((39 / 1) : ℝ) = ((1 / 39) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14647_neg : (668342061 / 1000000000) ≤ -Real.log (1000 / 1951) ∧
    -Real.log (1000 / 1951) ≤ (334171031 / 500000000) := by
  have h := checkLog_sound (w := (951 / 2951)) (n := 12)
    (lo := (668342061 / 1000000000)) (hi := (334171031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1951 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1951 / 1000) = 1/(1000 / 1951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14647 : Bounds (668342061 / 1000000000) (334171031 / 500000000) (Real.log (1951 / 1000)) := by
  have h := reflection_log_14647_neg
  have he : Real.log (1951 / 1000) = -Real.log (1000 / 1951) := by
    rw [show ((1951 / 1000) : ℝ) = ((1000 / 1951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14648_neg : (1507967489 / 500000000) ≤ -Real.log (49 / 1000) ∧
    -Real.log (49 / 1000) ≤ (3015934983 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 223)) (n := 12)
    (lo := (121673129 / 500000000)) (hi := (243346259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 98) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 98) = 1/(49 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14648 : Bounds (-3015934983 / 1000000000) (-1507967489 / 500000000) (Real.log (49 / 1000)) := by
  have h := reflection_log_14648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14649_neg : (237637 / 250000000) ≤ -Real.log (1000000 / 1000951) ∧
    -Real.log (1000000 / 1000951) ≤ (950549 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 2000951)) (n := 12)
    (lo := (237637 / 250000000)) (hi := (950549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000951 / 1000000) = 1/(1000000 / 1000951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14649 : Bounds (237637 / 250000000) (950549 / 1000000000) (Real.log (1000951 / 1000000)) := by
  have h := reflection_log_14649_neg
  have he : Real.log (1000951 / 1000000) = -Real.log (1000000 / 1000951) := by
    rw [show ((1000951 / 1000000) : ℝ) = ((1000000 / 1000951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14650_neg : (237863 / 250000000) ≤ -Real.log (999049 / 1000000) ∧
    -Real.log (999049 / 1000000) ≤ (951453 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 1999049)) (n := 12)
    (lo := (237863 / 250000000)) (hi := (951453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999049) = 1/(999049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14650 : Bounds (-951453 / 1000000000) (-237863 / 250000000) (Real.log (999049 / 1000000)) := by
  have h := reflection_log_14650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14651_neg : (23261833 / 50000000) ≤ -Real.log (1000000 / 1592391) ∧
    -Real.log (1000000 / 1592391) ≤ (465236661 / 1000000000) := by
  have h := checkLog_sound (w := (592391 / 2592391)) (n := 12)
    (lo := (23261833 / 50000000)) (hi := (465236661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1592391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1592391 / 1000000) = 1/(1000000 / 1592391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14651 : Bounds (23261833 / 50000000) (465236661 / 1000000000) (Real.log (1592391 / 1000000)) := by
  have h := reflection_log_14651_neg
  have he : Real.log (1592391 / 1000000) = -Real.log (1000000 / 1592391) := by
    rw [show ((1592391 / 1000000) : ℝ) = ((1000000 / 1592391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14652_neg : (56090431 / 62500000) ≤ -Real.log (407609 / 1000000) ∧
    -Real.log (407609 / 1000000) ≤ (448723449 / 500000000) := by
  have h := checkLog_sound (w := (92391 / 907609)) (n := 12)
    (lo := (51074929 / 250000000)) (hi := (204299717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 407609) = 1/(407609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14652 : Bounds (-448723449 / 500000000) (-56090431 / 62500000) (Real.log (407609 / 1000000)) := by
  have h := reflection_log_14652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14653_neg : (233168771 / 500000000) ≤ -Real.log (200000 / 318829) ∧
    -Real.log (200000 / 318829) ≤ (466337543 / 1000000000) := by
  have h := checkLog_sound (w := (118829 / 518829)) (n := 12)
    (lo := (233168771 / 500000000)) (hi := (466337543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318829 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318829 / 200000) = 1/(200000 / 318829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14653 : Bounds (233168771 / 500000000) (466337543 / 1000000000) (Real.log (318829 / 200000)) := by
  have h := reflection_log_14653_neg
  have he : Real.log (318829 / 200000) = -Real.log (200000 / 318829) := by
    rw [show ((318829 / 200000) : ℝ) = ((200000 / 318829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14654_neg : (36070373 / 40000000) ≤ -Real.log (81171 / 200000) ∧
    -Real.log (81171 / 200000) ≤ (901759327 / 1000000000) := by
  have h := checkLog_sound (w := (18829 / 181171)) (n := 12)
    (lo := (41722429 / 200000000)) (hi := (104306073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 81171) = 1/(81171 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14654 : Bounds (-901759327 / 1000000000) (-36070373 / 40000000) (Real.log (81171 / 200000)) := by
  have h := reflection_log_14654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14655_neg : (435421783 / 1000000000) ≤ -Real.log (25879668759 / 40000000000) ∧
    -Real.log (25879668759 / 40000000000) ≤ (54427723 / 125000000) := by
  have h := checkLog_sound (w := (14120331241 / 65879668759)) (n := 12)
    (lo := (435421783 / 1000000000)) (hi := (54427723 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25879668759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25879668759) = 1/(25879668759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14655 : Bounds (-54427723 / 125000000) (-435421783 / 1000000000) (Real.log (25879668759 / 40000000000)) := by
  have h := reflection_log_14655_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
