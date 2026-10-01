import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell142
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

theorem reflection_log_1_neg : (28802381 / 100000000) ≤ -Real.log (5120 / 6829) ∧
    -Real.log (5120 / 6829) ≤ (288023811 / 1000000000) := by
  have h := checkLog_sound (w := (1709 / 11949)) (n := 12)
    (lo := (28802381 / 100000000)) (hi := (288023811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6829 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6829 / 5120) = 1/(5120 / 6829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (28802381 / 100000000) (288023811 / 1000000000) (Real.log (6829 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6829 / 5120) = -Real.log (5120 / 6829) := by
    rw [show ((6829 / 5120) : ℝ) = ((5120 / 6829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (81229787 / 200000000) ≤ -Real.log (3411 / 5120) ∧
    -Real.log (3411 / 5120) ≤ (50768617 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 8531)) (n := 12)
    (lo := (81229787 / 200000000)) (hi := (50768617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3411) = 1/(3411 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-50768617 / 125000000) (-81229787 / 200000000) (Real.log (3411 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (287584411 / 1000000000) ≤ -Real.log (2560 / 3413) ∧
    -Real.log (2560 / 3413) ≤ (71896103 / 250000000) := by
  have h := checkLog_sound (w := (853 / 5973)) (n := 12)
    (lo := (287584411 / 1000000000)) (hi := (71896103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3413 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3413 / 2560) = 1/(2560 / 3413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (287584411 / 1000000000) (71896103 / 250000000) (Real.log (3413 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3413 / 2560) = -Real.log (2560 / 3413) := by
    rw [show ((3413 / 2560) : ℝ) = ((2560 / 3413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (202634907 / 500000000) ≤ -Real.log (1707 / 2560) ∧
    -Real.log (1707 / 2560) ≤ (81053963 / 200000000) := by
  have h := checkLog_sound (w := (853 / 4267)) (n := 12)
    (lo := (202634907 / 500000000)) (hi := (81053963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1707) = 1/(1707 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-81053963 / 200000000) (-202634907 / 500000000) (Real.log (1707 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (53122349 / 250000000) ≤ -Real.log (1000000 / 1236753) ∧
    -Real.log (1000000 / 1236753) ≤ (212489397 / 1000000000) := by
  have h := checkLog_sound (w := (236753 / 2236753)) (n := 12)
    (lo := (53122349 / 250000000)) (hi := (212489397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236753 / 1000000) = 1/(1000000 / 1236753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (53122349 / 250000000) (212489397 / 1000000000) (Real.log (1236753 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1236753 / 1000000) = -Real.log (1000000 / 1236753) := by
    rw [show ((1236753 / 1000000) : ℝ) = ((1000000 / 1236753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270173577 / 1000000000) ≤ -Real.log (763247 / 1000000) ∧
    -Real.log (763247 / 1000000) ≤ (135086789 / 500000000) := by
  have h := checkLog_sound (w := (236753 / 1763247)) (n := 12)
    (lo := (270173577 / 1000000000)) (hi := (135086789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763247) = 1/(763247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-135086789 / 500000000) (-270173577 / 1000000000) (Real.log (763247 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106415277 / 500000000) ≤ -Real.log (40000 / 49487) ∧
    -Real.log (40000 / 49487) ≤ (42566111 / 200000000) := by
  have h := checkLog_sound (w := (9487 / 89487)) (n := 12)
    (lo := (106415277 / 500000000)) (hi := (42566111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49487 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49487 / 40000) = 1/(40000 / 49487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106415277 / 500000000) (42566111 / 200000000) (Real.log (49487 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49487 / 40000) = -Real.log (40000 / 49487) := by
    rw [show ((49487 / 40000) : ℝ) = ((40000 / 49487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (270726631 / 1000000000) ≤ -Real.log (30513 / 40000) ∧
    -Real.log (30513 / 40000) ≤ (33840829 / 125000000) := by
  have h := checkLog_sound (w := (9487 / 70513)) (n := 12)
    (lo := (270726631 / 1000000000)) (hi := (33840829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30513) = 1/(30513 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-33840829 / 125000000) (-270726631 / 1000000000) (Real.log (30513 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78523241 / 500000000) ≤ -Real.log (20000 / 23401) ∧
    -Real.log (20000 / 23401) ≤ (157046483 / 1000000000) := by
  have h := checkLog_sound (w := (3401 / 43401)) (n := 12)
    (lo := (78523241 / 500000000)) (hi := (157046483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23401 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23401 / 20000) = 1/(20000 / 23401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78523241 / 500000000) (157046483 / 1000000000) (Real.log (23401 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23401 / 20000) = -Real.log (20000 / 23401) := by
    rw [show ((23401 / 20000) : ℝ) = ((20000 / 23401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9319491 / 50000000) ≤ -Real.log (16599 / 20000) ∧
    -Real.log (16599 / 20000) ≤ (186389821 / 1000000000) := by
  have h := checkLog_sound (w := (3401 / 36599)) (n := 12)
    (lo := (9319491 / 50000000)) (hi := (186389821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16599) = 1/(16599 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-186389821 / 1000000000) (-9319491 / 50000000) (Real.log (16599 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157313957 / 1000000000) ≤ -Real.log (1000000 / 1170363) ∧
    -Real.log (1000000 / 1170363) ≤ (78656979 / 500000000) := by
  have h := checkLog_sound (w := (170363 / 2170363)) (n := 12)
    (lo := (157313957 / 1000000000)) (hi := (78656979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170363 / 1000000) = 1/(1000000 / 1170363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157313957 / 1000000000) (78656979 / 500000000) (Real.log (1170363 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1170363 / 1000000) = -Real.log (1000000 / 1170363) := by
    rw [show ((1170363 / 1000000) : ℝ) = ((1000000 / 1170363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (186767023 / 1000000000) ≤ -Real.log (829637 / 1000000) ∧
    -Real.log (829637 / 1000000) ≤ (11672939 / 62500000) := by
  have h := checkLog_sound (w := (170363 / 1829637)) (n := 12)
    (lo := (186767023 / 1000000000)) (hi := (11672939 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829637) = 1/(829637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11672939 / 62500000) (-186767023 / 1000000000) (Real.log (829637 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (346427113 / 500000000) ≤ -Real.log (500000000000 / 999707088459) ∧
    -Real.log (500000000000 / 999707088459) ≤ (692854227 / 1000000000) := by
  have h := checkLog_sound (w := (499707088459 / 1499707088459)) (n := 12)
    (lo := (346427113 / 500000000)) (hi := (692854227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999707088459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999707088459 / 500000000000) = 1/(500000000000 / 999707088459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (346427113 / 500000000) (692854227 / 1000000000) (Real.log (999707088459 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (999707088459 / 500000000000) = -Real.log (500000000000 / 999707088459) := by
    rw [show ((999707088459 / 500000000000) : ℝ) = ((500000000000 / 999707088459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138834549 / 200000000) ≤ -Real.log (62500000000 / 125128261507) ∧
    -Real.log (62500000000 / 125128261507) ≤ (694172747 / 1000000000) := by
  have h := checkLog_sound (w := (128261507 / 250128261507)) (n := 12)
    (lo := (205113 / 200000000)) (hi := (512783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125128261507 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125128261507 / 125000000000) = 1/(62500000000 / 125128261507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (138834549 / 200000000) (694172747 / 1000000000) (Real.log (125128261507 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (125128261507 / 62500000000) = -Real.log (62500000000 / 125128261507) := by
    rw [show ((125128261507 / 62500000000) : ℝ) = ((62500000000 / 125128261507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (241331487 / 500000000) ≤ -Real.log (3906250000 / 6329623839) ∧
    -Real.log (3906250000 / 6329623839) ≤ (19306519 / 40000000) := by
  have h := checkLog_sound (w := (2423373839 / 10235873839)) (n := 12)
    (lo := (241331487 / 500000000)) (hi := (19306519 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6329623839 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6329623839 / 3906250000) = 1/(3906250000 / 6329623839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (241331487 / 500000000) (19306519 / 40000000) (Real.log (6329623839 / 3906250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6329623839 / 3906250000) = -Real.log (3906250000 / 6329623839) := by
    rw [show ((6329623839 / 3906250000) : ℝ) = ((3906250000 / 6329623839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (241778593 / 500000000) ≤ -Real.log (250000000000 / 405458329237) ∧
    -Real.log (250000000000 / 405458329237) ≤ (483557187 / 1000000000) := by
  have h := checkLog_sound (w := (155458329237 / 655458329237)) (n := 12)
    (lo := (241778593 / 500000000)) (hi := (483557187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405458329237 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405458329237 / 250000000000) = 1/(250000000000 / 405458329237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (241778593 / 500000000) (483557187 / 1000000000) (Real.log (405458329237 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (405458329237 / 250000000000) = -Real.log (250000000000 / 405458329237) := by
    rw [show ((405458329237 / 250000000000) : ℝ) = ((250000000000 / 405458329237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (343436303 / 1000000000) ≤ -Real.log (100000000000 / 140978372191) ∧
    -Real.log (100000000000 / 140978372191) ≤ (21464769 / 62500000) := by
  have h := checkLog_sound (w := (40978372191 / 240978372191)) (n := 12)
    (lo := (343436303 / 1000000000)) (hi := (21464769 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140978372191 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140978372191 / 100000000000) = 1/(100000000000 / 140978372191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (343436303 / 1000000000) (21464769 / 62500000) (Real.log (140978372191 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140978372191 / 100000000000) = -Real.log (100000000000 / 140978372191) := by
    rw [show ((140978372191 / 100000000000) : ℝ) = ((100000000000 / 140978372191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17204049 / 50000000) ≤ -Real.log (250000000000 / 352673217323) ∧
    -Real.log (250000000000 / 352673217323) ≤ (344080981 / 1000000000) := by
  have h := checkLog_sound (w := (102673217323 / 602673217323)) (n := 12)
    (lo := (17204049 / 50000000)) (hi := (344080981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352673217323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352673217323 / 250000000000) = 1/(250000000000 / 352673217323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17204049 / 50000000) (344080981 / 1000000000) (Real.log (352673217323 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (352673217323 / 250000000000) = -Real.log (250000000000 / 352673217323) := by
    rw [show ((352673217323 / 250000000000) : ℝ) = ((250000000000 / 352673217323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14726533 / 500000000) ≤ -Real.log (970976448231 / 1000000000000) ∧
    -Real.log (970976448231 / 1000000000000) ≤ (29453067 / 1000000000) := by
  have h := checkLog_sound (w := (29023551769 / 1970976448231)) (n := 12)
    (lo := (14726533 / 500000000)) (hi := (29453067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970976448231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970976448231) = 1/(970976448231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29453067 / 1000000000) (-14726533 / 500000000) (Real.log (970976448231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14671669 / 500000000) ≤ -Real.log (388433199 / 400000000) ∧
    -Real.log (388433199 / 400000000) ≤ (29343339 / 1000000000) := by
  have h := checkLog_sound (w := (11566801 / 788433199)) (n := 12)
    (lo := (14671669 / 500000000)) (hi := (29343339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 388433199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 388433199) = 1/(388433199 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29343339 / 1000000000) (-14671669 / 500000000) (Real.log (388433199 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell142
