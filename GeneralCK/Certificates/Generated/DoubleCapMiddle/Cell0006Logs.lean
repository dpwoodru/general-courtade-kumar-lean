import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0006
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

theorem reflection_log_1_neg : (42199441 / 100000000) ≤ -Real.log (40 / 61) ∧
    -Real.log (40 / 61) ≤ (421994411 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 101)) (n := 12)
    (lo := (42199441 / 100000000)) (hi := (421994411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 40) = 1/(40 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42199441 / 100000000) (421994411 / 1000000000) (Real.log (61 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (61 / 40) = -Real.log (40 / 61) := by
    rw [show ((61 / 40) : ℝ) = ((40 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (372220237 / 500000000) ≤ -Real.log (19 / 40) ∧
    -Real.log (19 / 40) ≤ (186110119 / 250000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 19) = 1/(19 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-186110119 / 250000000) (-372220237 / 500000000) (Real.log (19 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104471907 / 250000000) ≤ -Real.log (160 / 243) ∧
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


theorem reflection_log_3 : Bounds (104471907 / 250000000) (417887629 / 1000000000) (Real.log (243 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (243 / 160) = -Real.log (160 / 243) := by
    rw [show ((243 / 160) : ℝ) = ((160 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (91421049 / 125000000) ≤ -Real.log (77 / 160) ∧
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


theorem reflection_log_4 : Bounds (-365684197 / 500000000) (-91421049 / 125000000) (Real.log (77 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12197541 / 250000000) ≤ -Real.log (20 / 21) ∧
    -Real.log (20 / 21) ≤ (9758033 / 200000000) := by
  have h := checkLog_sound (w := (1 / 41)) (n := 12)
    (lo := (12197541 / 250000000)) (hi := (9758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 20) = 1/(20 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12197541 / 250000000) (9758033 / 200000000) (Real.log (21 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (21 / 20) = -Real.log (20 / 21) := by
    rw [show ((21 / 20) : ℝ) = ((20 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (25646647 / 500000000) ≤ -Real.log (19 / 20) ∧
    -Real.log (19 / 20) ≤ (10258659 / 200000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 19) = 1/(19 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-10258659 / 200000000) (-25646647 / 500000000) (Real.log (19 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (36813973 / 1000000000) ≤ -Real.log (80 / 83) ∧
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


theorem reflection_log_7 : Bounds (36813973 / 1000000000) (18406987 / 500000000) (Real.log (83 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (83 / 80) = -Real.log (80 / 83) := by
    rw [show ((83 / 80) : ℝ) = ((80 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9555303 / 250000000) ≤ -Real.log (77 / 80) ∧
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


theorem reflection_log_8 : Bounds (-38221213 / 1000000000) (-9555303 / 250000000) (Real.log (77 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (115354131 / 200000000) ≤ -Real.log (25000 / 44507) ∧
    -Real.log (25000 / 44507) ≤ (18024083 / 31250000) := by
  have h := checkLog_sound (w := (19507 / 69507)) (n := 12)
    (lo := (115354131 / 200000000)) (hi := (18024083 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44507 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44507 / 25000) = 1/(25000 / 44507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (115354131 / 200000000) (18024083 / 31250000) (Real.log (44507 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (44507 / 25000) = -Real.log (25000 / 44507) := by
    rw [show ((44507 / 25000) : ℝ) = ((25000 / 44507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1515401269 / 1000000000) ≤ -Real.log (5493 / 25000) ∧
    -Real.log (5493 / 25000) ≤ (189425159 / 125000000) := by
  have h := checkLog_sound (w := (757 / 11743)) (n := 12)
    (lo := (129106909 / 1000000000)) (hi := (12910691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5493) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 5493) = 1/(5493 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-189425159 / 125000000) (-1515401269 / 1000000000) (Real.log (5493 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576918373 / 1000000000) ≤ -Real.log (1000000 / 1780543) ∧
    -Real.log (1000000 / 1780543) ≤ (288459187 / 500000000) := by
  have h := checkLog_sound (w := (780543 / 2780543)) (n := 12)
    (lo := (576918373 / 1000000000)) (hi := (288459187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780543 / 1000000) = 1/(1000000 / 1780543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576918373 / 1000000000) (288459187 / 500000000) (Real.log (1780543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1780543 / 1000000) = -Real.log (1000000 / 1780543) := by
    rw [show ((1780543 / 1000000) : ℝ) = ((1000000 / 1780543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (379149741 / 250000000) ≤ -Real.log (219457 / 1000000) ∧
    -Real.log (219457 / 1000000) ≤ (1516598967 / 1000000000) := by
  have h := checkLog_sound (w := (30543 / 469457)) (n := 12)
    (lo := (32576151 / 250000000)) (hi := (26060921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219457) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219457) = 1/(219457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1516598967 / 1000000000) (-379149741 / 250000000) (Real.log (219457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (513106819 / 1000000000) ≤ -Real.log (1000000 / 1670473) ∧
    -Real.log (1000000 / 1670473) ≤ (25655341 / 50000000) := by
  have h := checkLog_sound (w := (670473 / 2670473)) (n := 12)
    (lo := (513106819 / 1000000000)) (hi := (25655341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1670473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1670473 / 1000000) = 1/(1000000 / 1670473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (513106819 / 1000000000) (25655341 / 50000000) (Real.log (1670473 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1670473 / 1000000) = -Real.log (1000000 / 1670473) := by
    rw [show ((1670473 / 1000000) : ℝ) = ((1000000 / 1670473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (222019397 / 200000000) ≤ -Real.log (329527 / 1000000) ∧
    -Real.log (329527 / 1000000) ≤ (1110096987 / 1000000000) := by
  have h := checkLog_sound (w := (170473 / 829527)) (n := 12)
    (lo := (83389961 / 200000000)) (hi := (208474903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329527) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 329527) = 1/(329527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1110096987 / 1000000000) (-222019397 / 200000000) (Real.log (329527 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (257705049 / 500000000) ≤ -Real.log (40000 / 66973) ∧
    -Real.log (40000 / 66973) ≤ (515410099 / 1000000000) := by
  have h := checkLog_sound (w := (26973 / 106973)) (n := 12)
    (lo := (257705049 / 500000000)) (hi := (515410099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66973 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66973 / 40000) = 1/(40000 / 66973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (257705049 / 500000000) (515410099 / 1000000000) (Real.log (66973 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66973 / 40000) = -Real.log (40000 / 66973) := by
    rw [show ((66973 / 40000) : ℝ) = ((40000 / 66973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (560927663 / 500000000) ≤ -Real.log (13027 / 40000) ∧
    -Real.log (13027 / 40000) ≤ (35057979 / 31250000) := by
  have h := checkLog_sound (w := (6973 / 33027)) (n := 12)
    (lo := (214354073 / 500000000)) (hi := (428708147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13027) = 1/(13027 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-35057979 / 31250000) (-560927663 / 500000000) (Real.log (13027 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (523042981 / 250000000) ≤ -Real.log (500000000000 / 4051247041689) ∧
    -Real.log (500000000000 / 4051247041689) ≤ (261521491 / 125000000) := by
  have h := checkLog_sound (w := (51247041689 / 8051247041689)) (n := 12)
    (lo := (795649 / 62500000)) (hi := (2546077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4051247041689 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4051247041689 / 4000000000000) = 1/(500000000000 / 4051247041689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (523042981 / 250000000) (261521491 / 125000000) (Real.log (4051247041689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4051247041689 / 500000000000) = -Real.log (500000000000 / 4051247041689) := by
    rw [show ((4051247041689 / 500000000000) : ℝ) = ((500000000000 / 4051247041689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2093517337 / 1000000000) ≤ -Real.log (250000000000 / 2028350656393) ∧
    -Real.log (250000000000 / 2028350656393) ≤ (2093517341 / 1000000000) := by
  have h := checkLog_sound (w := (28350656393 / 4028350656393)) (n := 12)
    (lo := (14075797 / 1000000000)) (hi := (7037899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2028350656393 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2028350656393 / 2000000000000) = 1/(250000000000 / 2028350656393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2093517337 / 1000000000) (2093517341 / 1000000000) (Real.log (2028350656393 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2028350656393 / 250000000000) = -Real.log (250000000000 / 2028350656393) := by
    rw [show ((2028350656393 / 250000000000) : ℝ) = ((250000000000 / 2028350656393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (405800951 / 250000000) ≤ -Real.log (500000000000 / 2534652699171) ∧
    -Real.log (500000000000 / 2534652699171) ≤ (1623203807 / 1000000000) := by
  have h := checkLog_sound (w := (534652699171 / 4534652699171)) (n := 12)
    (lo := (59227361 / 250000000)) (hi := (47381889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2534652699171 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2534652699171 / 2000000000000) = 1/(500000000000 / 2534652699171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (405800951 / 250000000) (1623203807 / 1000000000) (Real.log (2534652699171 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2534652699171 / 500000000000) = -Real.log (500000000000 / 2534652699171) := by
    rw [show ((2534652699171 / 500000000000) : ℝ) = ((500000000000 / 2534652699171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (65490617 / 40000000) ≤ -Real.log (100000000000 / 514109157903) ∧
    -Real.log (100000000000 / 514109157903) ≤ (409316357 / 250000000) := by
  have h := checkLog_sound (w := (114109157903 / 914109157903)) (n := 12)
    (lo := (50194213 / 200000000)) (hi := (125485533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514109157903 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(514109157903 / 400000000000) = 1/(100000000000 / 514109157903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (65490617 / 40000000) (409316357 / 250000000) (Real.log (514109157903 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (514109157903 / 100000000000) = -Real.log (100000000000 / 514109157903) := by
    rw [show ((514109157903 / 100000000000) : ℝ) = ((100000000000 / 514109157903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0006
