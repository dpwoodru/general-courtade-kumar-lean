import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0007
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

theorem reflection_log_1_neg : (104471907 / 250000000) ≤ -Real.log (160 / 243) ∧
    -Real.log (160 / 243) ≤ (417887629 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 403)) (n := 12)
    (lo := (104471907 / 250000000)) (hi := (417887629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 160) = 1/(160 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104471907 / 250000000) (417887629 / 1000000000) (Real.log (243 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (243 / 160) = -Real.log (160 / 243) := by
    rw [show ((243 / 160) : ℝ) = ((160 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (91421049 / 125000000) ≤ -Real.log (77 / 160) ∧
    -Real.log (77 / 160) ≤ (365684197 / 500000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 77) = 1/(77 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-365684197 / 500000000) (-91421049 / 125000000) (Real.log (77 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (36813973 / 1000000000) ≤ -Real.log (80 / 83) ∧
    -Real.log (80 / 83) ≤ (18406987 / 500000000) := by
  have h := checkLog_sound (w := (3 / 163)) (n := 12)
    (lo := (36813973 / 1000000000)) (hi := (18406987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 80) = 1/(80 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (36813973 / 1000000000) (18406987 / 500000000) (Real.log (83 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (83 / 80) = -Real.log (80 / 83) := by
    rw [show ((83 / 80) : ℝ) = ((80 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9555303 / 250000000) ≤ -Real.log (77 / 80) ∧
    -Real.log (77 / 80) ≤ (38221213 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 77) = 1/(77 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38221213 / 1000000000) (-9555303 / 250000000) (Real.log (77 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6173153 / 250000000) ≤ -Real.log (40 / 41) ∧
    -Real.log (40 / 41) ≤ (24692613 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 81)) (n := 12)
    (lo := (6173153 / 250000000)) (hi := (24692613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41 / 40) = 1/(40 / 41) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6173153 / 250000000) (24692613 / 1000000000) (Real.log (41 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (41 / 40) = -Real.log (40 / 41) := by
    rw [show ((41 / 40) : ℝ) = ((40 / 41) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25317807 / 1000000000) ≤ -Real.log (39 / 40) ∧
    -Real.log (39 / 40) ≤ (1582363 / 62500000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 39) = 1/(39 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1582363 / 62500000) (-25317807 / 1000000000) (Real.log (39 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57666561 / 100000000) ≤ -Real.log (1000000 / 1780093) ∧
    -Real.log (1000000 / 1780093) ≤ (576665611 / 1000000000) := by
  have h := checkLog_sound (w := (780093 / 2780093)) (n := 12)
    (lo := (57666561 / 100000000)) (hi := (576665611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780093 / 1000000) = 1/(1000000 / 1780093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57666561 / 100000000) (576665611 / 1000000000) (Real.log (1780093 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1780093 / 1000000) = -Real.log (1000000 / 1780093) := by
    rw [show ((1780093 / 1000000) : ℝ) = ((1000000 / 1780093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (378637637 / 250000000) ≤ -Real.log (219907 / 1000000) ∧
    -Real.log (219907 / 1000000) ≤ (1514550551 / 1000000000) := by
  have h := checkLog_sound (w := (30093 / 469907)) (n := 12)
    (lo := (32064047 / 250000000)) (hi := (128256189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219907) = 1/(219907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1514550551 / 1000000000) (-378637637 / 250000000) (Real.log (219907 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576771217 / 1000000000) ≤ -Real.log (1000000 / 1780281) ∧
    -Real.log (1000000 / 1780281) ≤ (288385609 / 500000000) := by
  have h := checkLog_sound (w := (780281 / 2780281)) (n := 12)
    (lo := (576771217 / 1000000000)) (hi := (288385609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780281 / 1000000) = 1/(1000000 / 1780281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576771217 / 1000000000) (288385609 / 500000000) (Real.log (1780281 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1780281 / 1000000) = -Real.log (1000000 / 1780281) := by
    rw [show ((1780281 / 1000000) : ℝ) = ((1000000 / 1780281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75770291 / 50000000) ≤ -Real.log (219719 / 1000000) ∧
    -Real.log (219719 / 1000000) ≤ (1515405823 / 1000000000) := by
  have h := checkLog_sound (w := (30281 / 469719)) (n := 12)
    (lo := (6455573 / 50000000)) (hi := (129111461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219719) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219719) = 1/(219719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1515405823 / 1000000000) (-75770291 / 50000000) (Real.log (219719 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (510800023 / 1000000000) ≤ -Real.log (15625 / 26041) ∧
    -Real.log (15625 / 26041) ≤ (63850003 / 125000000) := by
  have h := checkLog_sound (w := (5208 / 20833)) (n := 12)
    (lo := (510800023 / 1000000000)) (hi := (63850003 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26041 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26041 / 15625) = 1/(15625 / 26041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (510800023 / 1000000000) (63850003 / 125000000) (Real.log (26041 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26041 / 15625) = -Real.log (15625 / 26041) := by
    rw [show ((26041 / 15625) : ℝ) = ((15625 / 26041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137310537 / 125000000) ≤ -Real.log (5209 / 15625) ∧
    -Real.log (5209 / 15625) ≤ (549242149 / 500000000) := by
  have h := checkLog_sound (w := (5207 / 26043)) (n := 12)
    (lo := (101334279 / 250000000)) (hi := (405337117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10418) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10418) = 1/(5209 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-549242149 / 500000000) (-137310537 / 125000000) (Real.log (5209 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (256553709 / 500000000) ≤ -Real.log (500000 / 835237) ∧
    -Real.log (500000 / 835237) ≤ (513107419 / 1000000000) := by
  have h := checkLog_sound (w := (335237 / 1335237)) (n := 12)
    (lo := (256553709 / 500000000)) (hi := (513107419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835237 / 500000) = 1/(500000 / 835237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (256553709 / 500000000) (513107419 / 1000000000) (Real.log (835237 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (835237 / 500000) = -Real.log (500000 / 835237) := by
    rw [show ((835237 / 500000) : ℝ) = ((500000 / 835237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55505001 / 50000000) ≤ -Real.log (164763 / 500000) ∧
    -Real.log (164763 / 500000) ≤ (555050011 / 500000000) := by
  have h := checkLog_sound (w := (85237 / 414763)) (n := 12)
    (lo := (10423821 / 25000000)) (hi := (416952841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164763) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 164763) = 1/(164763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-555050011 / 500000000) (-55505001 / 50000000) (Real.log (164763 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2091216157 / 1000000000) ≤ -Real.log (250000000000 / 2023688422833) ∧
    -Real.log (250000000000 / 2023688422833) ≤ (2091216161 / 1000000000) := by
  have h := checkLog_sound (w := (23688422833 / 4023688422833)) (n := 12)
    (lo := (11774617 / 1000000000)) (hi := (5887309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023688422833 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2023688422833 / 2000000000000) = 1/(250000000000 / 2023688422833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2091216157 / 1000000000) (2091216161 / 1000000000) (Real.log (2023688422833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2023688422833 / 250000000000) = -Real.log (250000000000 / 2023688422833) := by
    rw [show ((2023688422833 / 250000000000) : ℝ) = ((250000000000 / 2023688422833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2092177037 / 1000000000) ≤ -Real.log (250000000000 / 2025633877817) ∧
    -Real.log (250000000000 / 2025633877817) ≤ (2092177041 / 1000000000) := by
  have h := checkLog_sound (w := (25633877817 / 4025633877817)) (n := 12)
    (lo := (12735497 / 1000000000)) (hi := (6367749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2025633877817 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2025633877817 / 2000000000000) = 1/(250000000000 / 2025633877817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2092177037 / 1000000000) (2092177041 / 1000000000) (Real.log (2025633877817 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2025633877817 / 250000000000) = -Real.log (250000000000 / 2025633877817) := by
    rw [show ((2025633877817 / 250000000000) : ℝ) = ((250000000000 / 2025633877817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1609284319 / 1000000000) ≤ -Real.log (100000000000 / 499923209829) ∧
    -Real.log (100000000000 / 499923209829) ≤ (804642161 / 500000000) := by
  have h := checkLog_sound (w := (99923209829 / 899923209829)) (n := 12)
    (lo := (222989959 / 1000000000)) (hi := (5574749 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499923209829 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(499923209829 / 400000000000) = 1/(100000000000 / 499923209829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1609284319 / 1000000000) (804642161 / 500000000) (Real.log (499923209829 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (499923209829 / 100000000000) = -Real.log (100000000000 / 499923209829) := by
    rw [show ((499923209829 / 100000000000) : ℝ) = ((100000000000 / 499923209829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (811603719 / 500000000) ≤ -Real.log (500000000000 / 2534661908317) ∧
    -Real.log (500000000000 / 2534661908317) ≤ (1623207441 / 1000000000) := by
  have h := checkLog_sound (w := (534661908317 / 4534661908317)) (n := 12)
    (lo := (118456539 / 500000000)) (hi := (236913079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2534661908317 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2534661908317 / 2000000000000) = 1/(500000000000 / 2534661908317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (811603719 / 500000000) (1623207441 / 1000000000) (Real.log (2534661908317 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2534661908317 / 500000000000) = -Real.log (500000000000 / 2534661908317) := by
    rw [show ((2534661908317 / 500000000000) : ℝ) = ((500000000000 / 2534661908317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0007
