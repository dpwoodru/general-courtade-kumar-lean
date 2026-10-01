import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216
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

theorem reflection_log_1_neg : (320015011 / 1000000000) ≤ -Real.log (5120 / 7051) ∧
    -Real.log (5120 / 7051) ≤ (80003753 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 12171)) (n := 12)
    (lo := (320015011 / 1000000000)) (hi := (80003753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7051 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7051 / 5120) = 1/(5120 / 7051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320015011 / 1000000000) (80003753 / 250000000) (Real.log (7051 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7051 / 5120) = -Real.log (5120 / 7051) := by
    rw [show ((7051 / 5120) : ℝ) = ((5120 / 7051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (473447051 / 1000000000) ≤ -Real.log (3189 / 5120) ∧
    -Real.log (3189 / 5120) ≤ (118361763 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 8309)) (n := 12)
    (lo := (473447051 / 1000000000)) (hi := (118361763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3189) = 1/(3189 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118361763 / 250000000) (-473447051 / 1000000000) (Real.log (3189 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319589449 / 1000000000) ≤ -Real.log (640 / 881) ∧
    -Real.log (640 / 881) ≤ (6391789 / 20000000) := by
  have h := checkLog_sound (w := (241 / 1521)) (n := 12)
    (lo := (319589449 / 1000000000)) (hi := (6391789 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881 / 640) = 1/(640 / 881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319589449 / 1000000000) (6391789 / 20000000) (Real.log (881 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (881 / 640) = -Real.log (640 / 881) := by
    rw [show ((881 / 640) : ℝ) = ((640 / 881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (472506759 / 1000000000) ≤ -Real.log (399 / 640) ∧
    -Real.log (399 / 640) ≤ (11812669 / 25000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 399) = 1/(399 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11812669 / 25000000) (-472506759 / 1000000000) (Real.log (399 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118697951 / 500000000) ≤ -Real.log (1000000 / 1267943) ∧
    -Real.log (1000000 / 1267943) ≤ (237395903 / 1000000000) := by
  have h := checkLog_sound (w := (267943 / 2267943)) (n := 12)
    (lo := (118697951 / 500000000)) (hi := (237395903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267943 / 1000000) = 1/(1000000 / 1267943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118697951 / 500000000) (237395903 / 1000000000) (Real.log (1267943 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1267943 / 1000000) = -Real.log (1000000 / 1267943) := by
    rw [show ((1267943 / 1000000) : ℝ) = ((1000000 / 1267943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (311896899 / 1000000000) ≤ -Real.log (732057 / 1000000) ∧
    -Real.log (732057 / 1000000) ≤ (3118969 / 10000000) := by
  have h := checkLog_sound (w := (267943 / 1732057)) (n := 12)
    (lo := (311896899 / 1000000000)) (hi := (3118969 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732057) = 1/(732057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3118969 / 10000000) (-311896899 / 1000000000) (Real.log (732057 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (237729457 / 1000000000) ≤ -Real.log (500000 / 634183) ∧
    -Real.log (500000 / 634183) ≤ (118864729 / 500000000) := by
  have h := checkLog_sound (w := (134183 / 1134183)) (n := 12)
    (lo := (237729457 / 1000000000)) (hi := (118864729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634183 / 500000) = 1/(500000 / 634183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (237729457 / 1000000000) (118864729 / 500000000) (Real.log (634183 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (634183 / 500000) = -Real.log (500000 / 634183) := by
    rw [show ((634183 / 500000) : ℝ) = ((500000 / 634183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31247489 / 100000000) ≤ -Real.log (365817 / 500000) ∧
    -Real.log (365817 / 500000) ≤ (312474891 / 1000000000) := by
  have h := checkLog_sound (w := (134183 / 865817)) (n := 12)
    (lo := (31247489 / 100000000)) (hi := (312474891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365817) = 1/(365817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-312474891 / 1000000000) (-31247489 / 100000000) (Real.log (365817 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88364641 / 500000000) ≤ -Real.log (250000 / 298327) ∧
    -Real.log (250000 / 298327) ≤ (176729283 / 1000000000) := by
  have h := checkLog_sound (w := (48327 / 548327)) (n := 12)
    (lo := (88364641 / 500000000)) (hi := (176729283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298327 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298327 / 250000) = 1/(250000 / 298327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88364641 / 500000000) (176729283 / 1000000000) (Real.log (298327 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (298327 / 250000) = -Real.log (250000 / 298327) := by
    rw [show ((298327 / 250000) : ℝ) = ((250000 / 298327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6712917 / 31250000) ≤ -Real.log (201673 / 250000) ∧
    -Real.log (201673 / 250000) ≤ (42962669 / 200000000) := by
  have h := checkLog_sound (w := (48327 / 451673)) (n := 12)
    (lo := (6712917 / 31250000)) (hi := (42962669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201673) = 1/(201673 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-42962669 / 200000000) (-6712917 / 31250000) (Real.log (201673 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176995733 / 1000000000) ≤ -Real.log (500000 / 596813) ∧
    -Real.log (500000 / 596813) ≤ (88497867 / 500000000) := by
  have h := checkLog_sound (w := (96813 / 1096813)) (n := 12)
    (lo := (176995733 / 1000000000)) (hi := (88497867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596813 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596813 / 500000) = 1/(500000 / 596813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176995733 / 1000000000) (88497867 / 500000000) (Real.log (596813 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (596813 / 500000) = -Real.log (500000 / 596813) := by
    rw [show ((596813 / 500000) : ℝ) = ((500000 / 596813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (26900953 / 125000000) ≤ -Real.log (403187 / 500000) ∧
    -Real.log (403187 / 500000) ≤ (1721661 / 8000000) := by
  have h := checkLog_sound (w := (96813 / 903187)) (n := 12)
    (lo := (26900953 / 125000000)) (hi := (1721661 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403187) = 1/(403187 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1721661 / 8000000) (-26900953 / 125000000) (Real.log (403187 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (49506013 / 62500000) ≤ -Real.log (250000000000 / 552005012531) ∧
    -Real.log (250000000000 / 552005012531) ≤ (79209621 / 100000000) := by
  have h := checkLog_sound (w := (52005012531 / 1052005012531)) (n := 12)
    (lo := (24737257 / 250000000)) (hi := (98949029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552005012531 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(552005012531 / 500000000000) = 1/(250000000000 / 552005012531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (49506013 / 62500000) (79209621 / 100000000) (Real.log (552005012531 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (552005012531 / 250000000000) = -Real.log (250000000000 / 552005012531) := by
    rw [show ((552005012531 / 250000000000) : ℝ) = ((250000000000 / 552005012531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (396731031 / 500000000) ≤ -Real.log (100000000000 / 221103794293) ∧
    -Real.log (100000000000 / 221103794293) ≤ (49591379 / 62500000) := by
  have h := checkLog_sound (w := (21103794293 / 421103794293)) (n := 12)
    (lo := (50157441 / 500000000)) (hi := (100314883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221103794293 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221103794293 / 200000000000) = 1/(100000000000 / 221103794293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (396731031 / 500000000) (49591379 / 62500000) (Real.log (221103794293 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (221103794293 / 100000000000) = -Real.log (100000000000 / 221103794293) := by
    rw [show ((221103794293 / 100000000000) : ℝ) = ((100000000000 / 221103794293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (549292801 / 1000000000) ≤ -Real.log (62500000000 / 108251731081) ∧
    -Real.log (62500000000 / 108251731081) ≤ (274646401 / 500000000) := by
  have h := checkLog_sound (w := (45751731081 / 170751731081)) (n := 12)
    (lo := (549292801 / 1000000000)) (hi := (274646401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108251731081 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108251731081 / 62500000000) = 1/(62500000000 / 108251731081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (549292801 / 1000000000) (274646401 / 500000000) (Real.log (108251731081 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (108251731081 / 62500000000) = -Real.log (62500000000 / 108251731081) := by
    rw [show ((108251731081 / 62500000000) : ℝ) = ((62500000000 / 108251731081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (550204347 / 1000000000) ≤ -Real.log (50000000000 / 86680362039) ∧
    -Real.log (50000000000 / 86680362039) ≤ (137551087 / 250000000) := by
  have h := checkLog_sound (w := (36680362039 / 136680362039)) (n := 12)
    (lo := (550204347 / 1000000000)) (hi := (137551087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86680362039 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86680362039 / 50000000000) = 1/(50000000000 / 86680362039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (550204347 / 1000000000) (137551087 / 250000000) (Real.log (86680362039 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (86680362039 / 50000000000) = -Real.log (50000000000 / 86680362039) := by
    rw [show ((86680362039 / 50000000000) : ℝ) = ((50000000000 / 86680362039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (195771313 / 500000000) ≤ -Real.log (500000000000 / 739630490943) ∧
    -Real.log (500000000000 / 739630490943) ≤ (391542627 / 1000000000) := by
  have h := checkLog_sound (w := (239630490943 / 1239630490943)) (n := 12)
    (lo := (195771313 / 500000000)) (hi := (391542627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739630490943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739630490943 / 500000000000) = 1/(500000000000 / 739630490943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (195771313 / 500000000) (391542627 / 1000000000) (Real.log (739630490943 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (739630490943 / 500000000000) = -Real.log (500000000000 / 739630490943) := by
    rw [show ((739630490943 / 500000000000) : ℝ) = ((500000000000 / 739630490943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (392203357 / 1000000000) ≤ -Real.log (500000000000 / 740119349087) ∧
    -Real.log (500000000000 / 740119349087) ≤ (196101679 / 500000000) := by
  have h := checkLog_sound (w := (240119349087 / 1240119349087)) (n := 12)
    (lo := (392203357 / 1000000000)) (hi := (196101679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740119349087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(740119349087 / 500000000000) = 1/(500000000000 / 740119349087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (392203357 / 1000000000) (196101679 / 500000000) (Real.log (740119349087 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (740119349087 / 500000000000) = -Real.log (500000000000 / 740119349087) := by
    rw [show ((740119349087 / 500000000000) : ℝ) = ((500000000000 / 740119349087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (38211891 / 1000000000) ≤ -Real.log (240627243031 / 250000000000) ∧
    -Real.log (240627243031 / 250000000000) ≤ (9552973 / 250000000) := by
  have h := checkLog_sound (w := (9372756969 / 490627243031)) (n := 12)
    (lo := (38211891 / 1000000000)) (hi := (9552973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240627243031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240627243031) = 1/(240627243031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9552973 / 250000000) (-38211891 / 1000000000) (Real.log (240627243031 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38084061 / 1000000000) ≤ -Real.log (60164501071 / 62500000000) ∧
    -Real.log (60164501071 / 62500000000) ≤ (19042031 / 500000000) := by
  have h := checkLog_sound (w := (2335498929 / 122664501071)) (n := 12)
    (lo := (38084061 / 1000000000)) (hi := (19042031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60164501071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60164501071) = 1/(60164501071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19042031 / 500000000) (-38084061 / 1000000000) (Real.log (60164501071 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216
