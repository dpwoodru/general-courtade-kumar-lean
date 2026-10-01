import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0015
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

theorem reflection_log_1_neg : (80467043 / 200000000) ≤ -Real.log (640 / 957) ∧
    -Real.log (640 / 957) ≤ (25145951 / 62500000) := by
  have h := checkLog_sound (w := (317 / 1597)) (n := 12)
    (lo := (80467043 / 200000000)) (hi := (25145951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 640) = 1/(640 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80467043 / 200000000) (25145951 / 62500000) (Real.log (957 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (957 / 640) = -Real.log (640 / 957) := by
    rw [show ((957 / 640) : ℝ) = ((640 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (683815853 / 1000000000) ≤ -Real.log (323 / 640) ∧
    -Real.log (323 / 640) ≤ (341907927 / 500000000) := by
  have h := checkLog_sound (w := (317 / 963)) (n := 12)
    (lo := (683815853 / 1000000000)) (hi := (341907927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 323) = 1/(323 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341907927 / 500000000) (-683815853 / 1000000000) (Real.log (323 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50193901 / 125000000) ≤ -Real.log (512 / 765) ∧
    -Real.log (512 / 765) ≤ (401551209 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 1277)) (n := 12)
    (lo := (50193901 / 125000000)) (hi := (401551209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765 / 512) = 1/(512 / 765) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50193901 / 125000000) (401551209 / 1000000000) (Real.log (765 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (765 / 512) = -Real.log (512 / 765) := by
    rw [show ((765 / 512) : ℝ) = ((512 / 765) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (681496563 / 1000000000) ≤ -Real.log (259 / 512) ∧
    -Real.log (259 / 512) ≤ (170374141 / 250000000) := by
  have h := checkLog_sound (w := (253 / 771)) (n := 12)
    (lo := (681496563 / 1000000000)) (hi := (170374141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 259) = 1/(259 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170374141 / 250000000) (-681496563 / 1000000000) (Real.log (259 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (688448659 / 1000000000) ≤ -Real.log (320 / 637) ∧
    -Real.log (320 / 637) ≤ (34422433 / 50000000) := by
  have h := checkLog_sound (w := (317 / 957)) (n := 12)
    (lo := (688448659 / 1000000000)) (hi := (34422433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 320) = 1/(320 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (688448659 / 1000000000) (34422433 / 50000000) (Real.log (637 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (637 / 320) = -Real.log (320 / 637) := by
    rw [show ((637 / 320) : ℝ) = ((320 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (4669708703 / 1000000000) ≤ -Real.log (3 / 320) ∧
    -Real.log (3 / 320) ≤ (466970871 / 100000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5 / 3) = 1/(3 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-466970871 / 100000000) (-4669708703 / 1000000000) (Real.log (3 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171817643 / 250000000) ≤ -Real.log (256 / 509) ∧
    -Real.log (256 / 509) ≤ (687270573 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 765)) (n := 12)
    (lo := (171817643 / 250000000)) (hi := (687270573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 256) = 1/(256 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171817643 / 250000000) (687270573 / 1000000000) (Real.log (509 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (509 / 256) = -Real.log (256 / 509) := by
    rw [show ((509 / 256) : ℝ) = ((256 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138955161 / 31250000) ≤ -Real.log (3 / 256) ∧
    -Real.log (3 / 256) ≤ (4446565159 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4 / 3) = 1/(3 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4446565159 / 1000000000) (-138955161 / 31250000) (Real.log (3 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (566661763 / 1000000000) ≤ -Real.log (500000 / 881187) ∧
    -Real.log (500000 / 881187) ≤ (141665441 / 250000000) := by
  have h := checkLog_sound (w := (381187 / 1381187)) (n := 12)
    (lo := (566661763 / 1000000000)) (hi := (141665441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881187 / 500000) = 1/(500000 / 881187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (566661763 / 1000000000) (141665441 / 250000000) (Real.log (881187 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (881187 / 500000) = -Real.log (500000 / 881187) := by
    rw [show ((881187 / 500000) : ℝ) = ((500000 / 881187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (359264317 / 250000000) ≤ -Real.log (118813 / 500000) ∧
    -Real.log (118813 / 500000) ≤ (1437057271 / 1000000000) := by
  have h := checkLog_sound (w := (6187 / 243813)) (n := 12)
    (lo := (12690727 / 250000000)) (hi := (50762909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 118813) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 118813) = 1/(118813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1437057271 / 1000000000) (-359264317 / 250000000) (Real.log (118813 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (284197143 / 500000000) ≤ -Real.log (100000 / 176543) ∧
    -Real.log (100000 / 176543) ≤ (568394287 / 1000000000) := by
  have h := checkLog_sound (w := (76543 / 276543)) (n := 12)
    (lo := (284197143 / 500000000)) (hi := (568394287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176543 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176543 / 100000) = 1/(100000 / 176543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (284197143 / 500000000) (568394287 / 1000000000) (Real.log (176543 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (176543 / 100000) = -Real.log (100000 / 176543) := by
    rw [show ((176543 / 100000) : ℝ) = ((100000 / 176543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1450001227 / 1000000000) ≤ -Real.log (23457 / 100000) ∧
    -Real.log (23457 / 100000) ≤ (145000123 / 100000000) := by
  have h := checkLog_sound (w := (1543 / 48457)) (n := 12)
    (lo := (63706867 / 1000000000)) (hi := (15926717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23457) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 23457) = 1/(23457 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-145000123 / 100000000) (-1450001227 / 1000000000) (Real.log (23457 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123595847 / 250000000) ≤ -Real.log (1000000 / 1639487) ∧
    -Real.log (1000000 / 1639487) ≤ (494383389 / 1000000000) := by
  have h := checkLog_sound (w := (639487 / 2639487)) (n := 12)
    (lo := (123595847 / 250000000)) (hi := (494383389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639487 / 1000000) = 1/(1000000 / 1639487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123595847 / 250000000) (494383389 / 1000000000) (Real.log (1639487 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1639487 / 1000000) = -Real.log (1000000 / 1639487) := by
    rw [show ((1639487 / 1000000) : ℝ) = ((1000000 / 1639487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1020227261 / 1000000000) ≤ -Real.log (360513 / 1000000) ∧
    -Real.log (360513 / 1000000) ≤ (1020227263 / 1000000000) := by
  have h := checkLog_sound (w := (139487 / 860513)) (n := 12)
    (lo := (327080081 / 1000000000)) (hi := (163540041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 360513) = 1/(360513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1020227263 / 1000000000) (-1020227261 / 1000000000) (Real.log (360513 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (99292351 / 200000000) ≤ -Real.log (500000 / 821449) ∧
    -Real.log (500000 / 821449) ≤ (124115439 / 250000000) := by
  have h := checkLog_sound (w := (321449 / 1321449)) (n := 12)
    (lo := (99292351 / 200000000)) (hi := (124115439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821449 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821449 / 500000) = 1/(500000 / 821449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99292351 / 200000000) (124115439 / 250000000) (Real.log (821449 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (821449 / 500000) = -Real.log (500000 / 821449) := by
    rw [show ((821449 / 500000) : ℝ) = ((500000 / 821449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1029733823 / 1000000000) ≤ -Real.log (178551 / 500000) ∧
    -Real.log (178551 / 500000) ≤ (41189353 / 40000000) := by
  have h := checkLog_sound (w := (71449 / 428551)) (n := 12)
    (lo := (336586643 / 1000000000)) (hi := (84146661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178551) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 178551) = 1/(178551 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-41189353 / 40000000) (-1029733823 / 1000000000) (Real.log (178551 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (250464879 / 125000000) ≤ -Real.log (250000000000 / 1854146852617) ∧
    -Real.log (250000000000 / 1854146852617) ≤ (400743807 / 200000000) := by
  have h := checkLog_sound (w := (854146852617 / 2854146852617)) (n := 12)
    (lo := (19294521 / 31250000)) (hi := (617424673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1854146852617 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1854146852617 / 1000000000000) = 1/(250000000000 / 1854146852617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (250464879 / 125000000) (400743807 / 200000000) (Real.log (1854146852617 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1854146852617 / 250000000000) = -Real.log (250000000000 / 1854146852617) := by
    rw [show ((1854146852617 / 250000000000) : ℝ) = ((250000000000 / 1854146852617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2018395513 / 1000000000) ≤ -Real.log (250000000000 / 1881559875517) ∧
    -Real.log (250000000000 / 1881559875517) ≤ (504598879 / 250000000) := by
  have h := checkLog_sound (w := (881559875517 / 2881559875517)) (n := 12)
    (lo := (632101153 / 1000000000)) (hi := (316050577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881559875517 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1881559875517 / 1000000000000) = 1/(250000000000 / 1881559875517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2018395513 / 1000000000) (504598879 / 250000000) (Real.log (1881559875517 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1881559875517 / 250000000000) = -Real.log (250000000000 / 1881559875517) := by
    rw [show ((1881559875517 / 250000000000) : ℝ) = ((250000000000 / 1881559875517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (189326331 / 125000000) ≤ -Real.log (250000000000 / 1136912538521) ∧
    -Real.log (250000000000 / 1136912538521) ≤ (1514610651 / 1000000000) := by
  have h := checkLog_sound (w := (136912538521 / 2136912538521)) (n := 12)
    (lo := (1002471 / 7812500)) (hi := (128316289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136912538521 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1136912538521 / 1000000000000) = 1/(250000000000 / 1136912538521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (189326331 / 125000000) (1514610651 / 1000000000) (Real.log (1136912538521 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1136912538521 / 250000000000) = -Real.log (250000000000 / 1136912538521) := by
    rw [show ((1136912538521 / 250000000000) : ℝ) = ((250000000000 / 1136912538521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (763097789 / 500000000) ≤ -Real.log (500000000000 / 2300320356649) ∧
    -Real.log (500000000000 / 2300320356649) ≤ (1526195581 / 1000000000) := by
  have h := checkLog_sound (w := (300320356649 / 4300320356649)) (n := 12)
    (lo := (69950609 / 500000000)) (hi := (139901219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2300320356649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2300320356649 / 2000000000000) = 1/(500000000000 / 2300320356649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (763097789 / 500000000) (1526195581 / 1000000000) (Real.log (2300320356649 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2300320356649 / 500000000000) = -Real.log (500000000000 / 2300320356649) := by
    rw [show ((2300320356649 / 500000000000) : ℝ) = ((500000000000 / 2300320356649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0015
