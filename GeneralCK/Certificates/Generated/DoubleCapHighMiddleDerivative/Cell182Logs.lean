import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell182
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

theorem reflection_log_1_neg : (12217733 / 40000000) ≤ -Real.log (5120 / 6949) ∧
    -Real.log (5120 / 6949) ≤ (152721663 / 500000000) := by
  have h := checkLog_sound (w := (1829 / 12069)) (n := 12)
    (lo := (12217733 / 40000000)) (hi := (152721663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6949 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6949 / 5120) = 1/(5120 / 6949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12217733 / 40000000) (152721663 / 500000000) (Real.log (6949 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6949 / 5120) = -Real.log (5120 / 6949) := by
    rw [show ((6949 / 5120) : ℝ) = ((5120 / 6949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (441962969 / 1000000000) ≤ -Real.log (3291 / 5120) ∧
    -Real.log (3291 / 5120) ≤ (44196297 / 100000000) := by
  have h := checkLog_sound (w := (1829 / 8411)) (n := 12)
    (lo := (441962969 / 1000000000)) (hi := (44196297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3291) = 1/(3291 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44196297 / 100000000) (-441962969 / 1000000000) (Real.log (3291 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61002303 / 200000000) ≤ -Real.log (2560 / 3473) ∧
    -Real.log (2560 / 3473) ≤ (76252879 / 250000000) := by
  have h := checkLog_sound (w := (913 / 6033)) (n := 12)
    (lo := (61002303 / 200000000)) (hi := (76252879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3473 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3473 / 2560) = 1/(2560 / 3473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61002303 / 200000000) (76252879 / 250000000) (Real.log (3473 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3473 / 2560) = -Real.log (2560 / 3473) := by
    rw [show ((3473 / 2560) : ℝ) = ((2560 / 3473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (441051807 / 1000000000) ≤ -Real.log (1647 / 2560) ∧
    -Real.log (1647 / 2560) ≤ (13782869 / 31250000) := by
  have h := checkLog_sound (w := (913 / 4207)) (n := 12)
    (lo := (441051807 / 1000000000)) (hi := (13782869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1647) = 1/(1647 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-13782869 / 31250000) (-441051807 / 1000000000) (Real.log (1647 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1808117 / 8000000) ≤ -Real.log (500000 / 626797) ∧
    -Real.log (500000 / 626797) ≤ (113007313 / 500000000) := by
  have h := checkLog_sound (w := (126797 / 1126797)) (n := 12)
    (lo := (1808117 / 8000000)) (hi := (113007313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626797 / 500000) = 1/(500000 / 626797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1808117 / 8000000) (113007313 / 500000000) (Real.log (626797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (626797 / 500000) = -Real.log (500000 / 626797) := by
    rw [show ((626797 / 500000) : ℝ) = ((500000 / 626797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (29248559 / 100000000) ≤ -Real.log (373203 / 500000) ∧
    -Real.log (373203 / 500000) ≤ (292485591 / 1000000000) := by
  have h := checkLog_sound (w := (126797 / 873203)) (n := 12)
    (lo := (29248559 / 100000000)) (hi := (292485591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373203) = 1/(373203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-292485591 / 1000000000) (-29248559 / 100000000) (Real.log (373203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113175999 / 500000000) ≤ -Real.log (1000000 / 1254017) ∧
    -Real.log (1000000 / 1254017) ≤ (226351999 / 1000000000) := by
  have h := checkLog_sound (w := (254017 / 2254017)) (n := 12)
    (lo := (113175999 / 500000000)) (hi := (226351999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254017 / 1000000) = 1/(1000000 / 1254017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113175999 / 500000000) (226351999 / 1000000000) (Real.log (1254017 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1254017 / 1000000) = -Real.log (1000000 / 1254017) := by
    rw [show ((1254017 / 1000000) : ℝ) = ((1000000 / 1254017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (293052467 / 1000000000) ≤ -Real.log (745983 / 1000000) ∧
    -Real.log (745983 / 1000000) ≤ (73263117 / 250000000) := by
  have h := checkLog_sound (w := (254017 / 1745983)) (n := 12)
    (lo := (293052467 / 1000000000)) (hi := (73263117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745983) = 1/(745983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73263117 / 250000000) (-293052467 / 1000000000) (Real.log (745983 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167690881 / 1000000000) ≤ -Real.log (1000000 / 1182571) ∧
    -Real.log (1000000 / 1182571) ≤ (83845441 / 500000000) := by
  have h := checkLog_sound (w := (182571 / 2182571)) (n := 12)
    (lo := (167690881 / 1000000000)) (hi := (83845441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182571 / 1000000) = 1/(1000000 / 1182571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167690881 / 1000000000) (83845441 / 500000000) (Real.log (1182571 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1182571 / 1000000) = -Real.log (1000000 / 1182571) := by
    rw [show ((1182571 / 1000000) : ℝ) = ((1000000 / 1182571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20159123 / 100000000) ≤ -Real.log (817429 / 1000000) ∧
    -Real.log (817429 / 1000000) ≤ (201591231 / 1000000000) := by
  have h := checkLog_sound (w := (182571 / 1817429)) (n := 12)
    (lo := (20159123 / 100000000)) (hi := (201591231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817429) = 1/(817429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-201591231 / 1000000000) (-20159123 / 100000000) (Real.log (817429 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33591443 / 200000000) ≤ -Real.log (500000 / 591443) ∧
    -Real.log (500000 / 591443) ≤ (5248663 / 31250000) := by
  have h := checkLog_sound (w := (91443 / 1091443)) (n := 12)
    (lo := (33591443 / 200000000)) (hi := (5248663 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591443 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591443 / 500000) = 1/(500000 / 591443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33591443 / 200000000) (5248663 / 31250000) (Real.log (591443 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (591443 / 500000) = -Real.log (500000 / 591443) := by
    rw [show ((591443 / 500000) : ℝ) = ((500000 / 591443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100988329 / 500000000) ≤ -Real.log (408557 / 500000) ∧
    -Real.log (408557 / 500000) ≤ (201976659 / 1000000000) := by
  have h := checkLog_sound (w := (91443 / 908557)) (n := 12)
    (lo := (100988329 / 500000000)) (hi := (201976659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408557) = 1/(408557 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201976659 / 1000000000) (-100988329 / 500000000) (Real.log (408557 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (373031661 / 500000000) ≤ -Real.log (62500000000 / 131792653309) ∧
    -Real.log (62500000000 / 131792653309) ≤ (186515831 / 250000000) := by
  have h := checkLog_sound (w := (6792653309 / 256792653309)) (n := 12)
    (lo := (26458071 / 500000000)) (hi := (52916143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131792653309 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(131792653309 / 125000000000) = 1/(62500000000 / 131792653309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (373031661 / 500000000) (186515831 / 250000000) (Real.log (131792653309 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (131792653309 / 62500000000) = -Real.log (62500000000 / 131792653309) := by
    rw [show ((131792653309 / 62500000000) : ℝ) = ((62500000000 / 131792653309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (747406293 / 1000000000) ≤ -Real.log (500000000000 / 1055758128229) ∧
    -Real.log (500000000000 / 1055758128229) ≤ (149481259 / 200000000) := by
  have h := checkLog_sound (w := (55758128229 / 2055758128229)) (n := 12)
    (lo := (54259113 / 1000000000)) (hi := (27129557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055758128229 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055758128229 / 1000000000000) = 1/(500000000000 / 1055758128229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (747406293 / 1000000000) (149481259 / 200000000) (Real.log (1055758128229 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1055758128229 / 500000000000) = -Real.log (500000000000 / 1055758128229) := by
    rw [show ((1055758128229 / 500000000000) : ℝ) = ((500000000000 / 1055758128229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (64812527 / 125000000) ≤ -Real.log (250000000000 / 419876715889) ∧
    -Real.log (250000000000 / 419876715889) ≤ (518500217 / 1000000000) := by
  have h := checkLog_sound (w := (169876715889 / 669876715889)) (n := 12)
    (lo := (64812527 / 125000000)) (hi := (518500217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419876715889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419876715889 / 250000000000) = 1/(250000000000 / 419876715889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (64812527 / 125000000) (518500217 / 1000000000) (Real.log (419876715889 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (419876715889 / 250000000000) = -Real.log (250000000000 / 419876715889) := by
    rw [show ((419876715889 / 250000000000) : ℝ) = ((250000000000 / 419876715889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103880893 / 200000000) ≤ -Real.log (500000000000 / 840513121613) ∧
    -Real.log (500000000000 / 840513121613) ≤ (259702233 / 500000000) := by
  have h := checkLog_sound (w := (340513121613 / 1340513121613)) (n := 12)
    (lo := (103880893 / 200000000)) (hi := (259702233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840513121613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840513121613 / 500000000000) = 1/(500000000000 / 840513121613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103880893 / 200000000) (259702233 / 500000000) (Real.log (840513121613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (840513121613 / 500000000000) = -Real.log (500000000000 / 840513121613) := by
    rw [show ((840513121613 / 500000000000) : ℝ) = ((500000000000 / 840513121613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (369282111 / 1000000000) ≤ -Real.log (6250000000 / 9041847977) ∧
    -Real.log (6250000000 / 9041847977) ≤ (5770033 / 15625000) := by
  have h := checkLog_sound (w := (2791847977 / 15291847977)) (n := 12)
    (lo := (369282111 / 1000000000)) (hi := (5770033 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9041847977 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9041847977 / 6250000000) = 1/(6250000000 / 9041847977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (369282111 / 1000000000) (5770033 / 15625000) (Real.log (9041847977 / 6250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9041847977 / 6250000000) = -Real.log (6250000000 / 9041847977) := by
    rw [show ((9041847977 / 6250000000) : ℝ) = ((6250000000 / 9041847977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (184966937 / 500000000) ≤ -Real.log (20000000000 / 28952777703) ∧
    -Real.log (20000000000 / 28952777703) ≤ (2959471 / 8000000) := by
  have h := checkLog_sound (w := (8952777703 / 48952777703)) (n := 12)
    (lo := (184966937 / 500000000)) (hi := (2959471 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28952777703 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28952777703 / 20000000000) = 1/(20000000000 / 28952777703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (184966937 / 500000000) (2959471 / 8000000) (Real.log (28952777703 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28952777703 / 20000000000) = -Real.log (20000000000 / 28952777703) := by
    rw [show ((28952777703 / 20000000000) : ℝ) = ((20000000000 / 28952777703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34019443 / 1000000000) ≤ -Real.log (241638177751 / 250000000000) ∧
    -Real.log (241638177751 / 250000000000) ≤ (8504861 / 250000000) := by
  have h := checkLog_sound (w := (8361822249 / 491638177751)) (n := 12)
    (lo := (34019443 / 1000000000)) (hi := (8504861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241638177751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241638177751) = 1/(241638177751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8504861 / 250000000) (-34019443 / 1000000000) (Real.log (241638177751 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8475087 / 250000000) ≤ -Real.log (966667829959 / 1000000000000) ∧
    -Real.log (966667829959 / 1000000000000) ≤ (33900349 / 1000000000) := by
  have h := checkLog_sound (w := (33332170041 / 1966667829959)) (n := 12)
    (lo := (8475087 / 250000000)) (hi := (33900349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966667829959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966667829959) = 1/(966667829959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-33900349 / 1000000000) (-8475087 / 250000000) (Real.log (966667829959 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell182
