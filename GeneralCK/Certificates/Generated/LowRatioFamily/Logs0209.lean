import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13376_neg : (409018467 / 250000000) ≤ -Real.log (31250000000 / 160467791411) ∧
    -Real.log (31250000000 / 160467791411) ≤ (1636073871 / 1000000000) := by
  have h := checkLog_sound (w := (35467791411 / 285467791411)) (n := 12)
    (lo := (62444877 / 250000000)) (hi := (249779509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160467791411 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160467791411 / 125000000000) = 1/(31250000000 / 160467791411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13376 : Bounds (409018467 / 250000000) (1636073871 / 1000000000) (Real.log (160467791411 / 31250000000)) := by
  have h := reflection_log_13376_neg
  have he : Real.log (160467791411 / 31250000000) = -Real.log (31250000000 / 160467791411) := by
    rw [show ((160467791411 / 31250000000) : ℝ) = ((31250000000 / 160467791411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13377_neg : (1647109437 / 1000000000) ≤ -Real.log (500000000000 / 2595975232199) ∧
    -Real.log (500000000000 / 2595975232199) ≤ (5147217 / 3125000) := by
  have h := checkLog_sound (w := (595975232199 / 4595975232199)) (n := 12)
    (lo := (260815077 / 1000000000)) (hi := (130407539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2595975232199 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2595975232199 / 2000000000000) = 1/(500000000000 / 2595975232199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13377 : Bounds (1647109437 / 1000000000) (5147217 / 3125000) (Real.log (2595975232199 / 500000000000)) := by
  have h := reflection_log_13377_neg
  have he : Real.log (2595975232199 / 500000000000) = -Real.log (500000000000 / 2595975232199) := by
    rw [show ((2595975232199 / 500000000000) : ℝ) = ((500000000000 / 2595975232199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13378_neg : (518793793 / 1000000000) ≤ -Real.log (25 / 42) ∧
    -Real.log (25 / 42) ≤ (259396897 / 500000000) := by
  have h := checkLog_sound (w := (17 / 67)) (n := 12)
    (lo := (518793793 / 1000000000)) (hi := (259396897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42 / 25) = 1/(25 / 42) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13378 : Bounds (518793793 / 1000000000) (259396897 / 500000000) (Real.log (42 / 25)) := by
  have h := reflection_log_13378_neg
  have he : Real.log (42 / 25) = -Real.log (25 / 42) := by
    rw [show ((42 / 25) : ℝ) = ((25 / 42) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13379_neg : (569717141 / 500000000) ≤ -Real.log (8 / 25) ∧
    -Real.log (8 / 25) ≤ (284858571 / 250000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 16) = 1/(8 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13379 : Bounds (-284858571 / 250000000) (-569717141 / 500000000) (Real.log (8 / 25)) := by
  have h := reflection_log_13379_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13380_neg : (84971 / 125000000) ≤ -Real.log (25000 / 25017) ∧
    -Real.log (25000 / 25017) ≤ (679769 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 50017)) (n := 12)
    (lo := (84971 / 125000000)) (hi := (679769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25017 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25017 / 25000) = 1/(25000 / 25017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13380 : Bounds (84971 / 125000000) (679769 / 1000000000) (Real.log (25017 / 25000)) := by
  have h := reflection_log_13380_neg
  have he : Real.log (25017 / 25000) = -Real.log (25000 / 25017) := by
    rw [show ((25017 / 25000) : ℝ) = ((25000 / 25017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13381_neg : (680231 / 1000000000) ≤ -Real.log (24983 / 25000) ∧
    -Real.log (24983 / 25000) ≤ (85029 / 125000000) := by
  have h := checkLog_sound (w := (17 / 49983)) (n := 12)
    (lo := (680231 / 1000000000)) (hi := (85029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24983) = 1/(24983 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13381 : Bounds (-85029 / 125000000) (-680231 / 1000000000) (Real.log (24983 / 25000)) := by
  have h := reflection_log_13381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13382_neg : (39437353 / 125000000) ≤ -Real.log (1000000 / 1370943) ∧
    -Real.log (1000000 / 1370943) ≤ (12619953 / 40000000) := by
  have h := checkLog_sound (w := (370943 / 2370943)) (n := 12)
    (lo := (39437353 / 125000000)) (hi := (12619953 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1370943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1370943 / 1000000) = 1/(1000000 / 1370943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13382 : Bounds (39437353 / 125000000) (12619953 / 40000000) (Real.log (1370943 / 1000000)) := by
  have h := reflection_log_13382_neg
  have he : Real.log (1370943 / 1000000) = -Real.log (1000000 / 1370943) := by
    rw [show ((1370943 / 1000000) : ℝ) = ((1000000 / 1370943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13383_neg : (231766703 / 500000000) ≤ -Real.log (629057 / 1000000) ∧
    -Real.log (629057 / 1000000) ≤ (463533407 / 1000000000) := by
  have h := checkLog_sound (w := (370943 / 1629057)) (n := 12)
    (lo := (231766703 / 500000000)) (hi := (463533407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 629057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 629057) = 1/(629057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13383 : Bounds (-463533407 / 1000000000) (-231766703 / 500000000) (Real.log (629057 / 1000000)) := by
  have h := reflection_log_13383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13384_neg : (79347837 / 250000000) ≤ -Real.log (50000 / 68677) ∧
    -Real.log (50000 / 68677) ≤ (317391349 / 1000000000) := by
  have h := checkLog_sound (w := (18677 / 118677)) (n := 12)
    (lo := (79347837 / 250000000)) (hi := (317391349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68677 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68677 / 50000) = 1/(50000 / 68677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13384 : Bounds (79347837 / 250000000) (317391349 / 1000000000) (Real.log (68677 / 50000)) := by
  have h := reflection_log_13384_neg
  have he : Real.log (68677 / 50000) = -Real.log (50000 / 68677) := by
    rw [show ((68677 / 50000) : ℝ) = ((50000 / 68677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13385_neg : (467670353 / 1000000000) ≤ -Real.log (31323 / 50000) ∧
    -Real.log (31323 / 50000) ≤ (233835177 / 500000000) := by
  have h := checkLog_sound (w := (18677 / 81323)) (n := 12)
    (lo := (467670353 / 1000000000)) (hi := (233835177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31323) = 1/(31323 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13385 : Bounds (-233835177 / 500000000) (-467670353 / 1000000000) (Real.log (31323 / 50000)) := by
  have h := reflection_log_13385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13386_neg : (37569751 / 250000000) ≤ -Real.log (2151169671 / 2500000000) ∧
    -Real.log (2151169671 / 2500000000) ≤ (30055801 / 200000000) := by
  have h := checkLog_sound (w := (348830329 / 4651169671)) (n := 12)
    (lo := (37569751 / 250000000)) (hi := (30055801 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2151169671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2151169671) = 1/(2151169671 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13386 : Bounds (-30055801 / 200000000) (-37569751 / 250000000) (Real.log (2151169671 / 2500000000)) := by
  have h := reflection_log_13386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13387_neg : (74017291 / 500000000) ≤ -Real.log (862401290751 / 1000000000000) ∧
    -Real.log (862401290751 / 1000000000000) ≤ (148034583 / 1000000000) := by
  have h := checkLog_sound (w := (137598709249 / 1862401290751)) (n := 12)
    (lo := (74017291 / 500000000)) (hi := (148034583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 862401290751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 862401290751) = 1/(862401290751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13387 : Bounds (-148034583 / 1000000000) (-74017291 / 500000000) (Real.log (862401290751 / 1000000000000)) := by
  have h := reflection_log_13387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13388_neg : (77903223 / 100000000) ≤ -Real.log (31250000000 / 68105066393) ∧
    -Real.log (31250000000 / 68105066393) ≤ (97379029 / 125000000) := by
  have h := checkLog_sound (w := (5605066393 / 130605066393)) (n := 12)
    (lo := (1717701 / 20000000)) (hi := (85885051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68105066393 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68105066393 / 62500000000) = 1/(31250000000 / 68105066393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13388 : Bounds (77903223 / 100000000) (97379029 / 125000000) (Real.log (68105066393 / 31250000000)) := by
  have h := reflection_log_13388_neg
  have he : Real.log (68105066393 / 31250000000) = -Real.log (31250000000 / 68105066393) := by
    rw [show ((68105066393 / 31250000000) : ℝ) = ((31250000000 / 68105066393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13389_neg : (785061701 / 1000000000) ≤ -Real.log (250000000000 / 548135555343) ∧
    -Real.log (250000000000 / 548135555343) ≤ (785061703 / 1000000000) := by
  have h := checkLog_sound (w := (48135555343 / 1048135555343)) (n := 12)
    (lo := (91914521 / 1000000000)) (hi := (45957261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548135555343 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(548135555343 / 500000000000) = 1/(250000000000 / 548135555343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13389 : Bounds (785061701 / 1000000000) (785061703 / 1000000000) (Real.log (548135555343 / 250000000000)) := by
  have h := reflection_log_13389_neg
  have he : Real.log (548135555343 / 250000000000) = -Real.log (250000000000 / 548135555343) := by
    rw [show ((548135555343 / 250000000000) : ℝ) = ((250000000000 / 548135555343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13390_neg : (1647109437 / 1000000000) ≤ -Real.log (250000000000 / 1297987616099) ∧
    -Real.log (250000000000 / 1297987616099) ≤ (5147217 / 3125000) := by
  have h := checkLog_sound (w := (297987616099 / 2297987616099)) (n := 12)
    (lo := (260815077 / 1000000000)) (hi := (130407539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297987616099 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1297987616099 / 1000000000000) = 1/(250000000000 / 1297987616099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13390 : Bounds (1647109437 / 1000000000) (5147217 / 3125000) (Real.log (1297987616099 / 250000000000)) := by
  have h := reflection_log_13390_neg
  have he : Real.log (1297987616099 / 250000000000) = -Real.log (250000000000 / 1297987616099) := by
    rw [show ((1297987616099 / 250000000000) : ℝ) = ((250000000000 / 1297987616099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13391_neg : (66329123 / 40000000) ≤ -Real.log (4 / 21) ∧
    -Real.log (4 / 21) ≤ (829114039 / 500000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21 / 16) = 1/(4 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13391 : Bounds (66329123 / 40000000) (829114039 / 500000000) (Real.log (21 / 4)) := by
  have h := reflection_log_13391_neg
  have he : Real.log (21 / 4) = -Real.log (4 / 21) := by
    rw [show ((21 / 4) : ℝ) = ((4 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13392_neg : (104115583 / 200000000) ≤ -Real.log (1000 / 1683) ∧
    -Real.log (1000 / 1683) ≤ (130144479 / 250000000) := by
  have h := checkLog_sound (w := (683 / 2683)) (n := 12)
    (lo := (104115583 / 200000000)) (hi := (130144479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1683 / 1000) = 1/(1000 / 1683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13392 : Bounds (104115583 / 200000000) (130144479 / 250000000) (Real.log (1683 / 1000)) := by
  have h := reflection_log_13392_neg
  have he : Real.log (1683 / 1000) = -Real.log (1000 / 1683) := by
    rw [show ((1683 / 1000) : ℝ) = ((1000 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13393_neg : (4487709 / 3906250) ≤ -Real.log (317 / 1000) ∧
    -Real.log (317 / 1000) ≤ (574426753 / 500000000) := by
  have h := checkLog_sound (w := (183 / 817)) (n := 12)
    (lo := (113926581 / 250000000)) (hi := (18228253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 317) = 1/(317 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13393 : Bounds (-574426753 / 500000000) (-4487709 / 3906250) (Real.log (317 / 1000)) := by
  have h := reflection_log_13393_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13394_neg : (341383 / 500000000) ≤ -Real.log (1000000 / 1000683) ∧
    -Real.log (1000000 / 1000683) ≤ (682767 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 2000683)) (n := 12)
    (lo := (341383 / 500000000)) (hi := (682767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000683 / 1000000) = 1/(1000000 / 1000683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13394 : Bounds (341383 / 500000000) (682767 / 1000000000) (Real.log (1000683 / 1000000)) := by
  have h := reflection_log_13394_neg
  have he : Real.log (1000683 / 1000000) = -Real.log (1000000 / 1000683) := by
    rw [show ((1000683 / 1000000) : ℝ) = ((1000000 / 1000683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13395_neg : (683233 / 1000000000) ≤ -Real.log (999317 / 1000000) ∧
    -Real.log (999317 / 1000000) ≤ (341617 / 500000000) := by
  have h := checkLog_sound (w := (683 / 1999317)) (n := 12)
    (lo := (683233 / 1000000000)) (hi := (341617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999317) = 1/(999317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13395 : Bounds (-341617 / 500000000) (-683233 / 1000000000) (Real.log (999317 / 1000000)) := by
  have h := reflection_log_13395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13396_neg : (1238089 / 3906250) ≤ -Real.log (200000 / 274587) ∧
    -Real.log (200000 / 274587) ≤ (63390157 / 200000000) := by
  have h := checkLog_sound (w := (74587 / 474587)) (n := 12)
    (lo := (1238089 / 3906250)) (hi := (63390157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274587 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274587 / 200000) = 1/(200000 / 274587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13396 : Bounds (1238089 / 3906250) (63390157 / 200000000) (Real.log (274587 / 200000)) := by
  have h := reflection_log_13396_neg
  have he : Real.log (274587 / 200000) = -Real.log (200000 / 274587) := by
    rw [show ((274587 / 200000) : ℝ) = ((200000 / 274587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13397_neg : (18668203 / 40000000) ≤ -Real.log (125413 / 200000) ∧
    -Real.log (125413 / 200000) ≤ (116676269 / 250000000) := by
  have h := checkLog_sound (w := (74587 / 325413)) (n := 12)
    (lo := (18668203 / 40000000)) (hi := (116676269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125413) = 1/(125413 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13397 : Bounds (-116676269 / 250000000) (-18668203 / 40000000) (Real.log (125413 / 200000)) := by
  have h := reflection_log_13397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13398_neg : (318846381 / 1000000000) ≤ -Real.log (50000 / 68777) ∧
    -Real.log (50000 / 68777) ≤ (159423191 / 500000000) := by
  have h := checkLog_sound (w := (18777 / 118777)) (n := 12)
    (lo := (318846381 / 1000000000)) (hi := (159423191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68777 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68777 / 50000) = 1/(50000 / 68777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13398 : Bounds (318846381 / 1000000000) (159423191 / 500000000) (Real.log (68777 / 50000)) := by
  have h := reflection_log_13398_neg
  have he : Real.log (68777 / 50000) = -Real.log (50000 / 68777) := by
    rw [show ((68777 / 50000) : ℝ) = ((50000 / 68777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13399_neg : (235434001 / 500000000) ≤ -Real.log (31223 / 50000) ∧
    -Real.log (31223 / 50000) ≤ (470868003 / 1000000000) := by
  have h := checkLog_sound (w := (18777 / 81223)) (n := 12)
    (lo := (235434001 / 500000000)) (hi := (470868003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31223) = 1/(31223 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13399 : Bounds (-470868003 / 1000000000) (-235434001 / 500000000) (Real.log (31223 / 50000)) := by
  have h := reflection_log_13399_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13400_neg : (152021621 / 1000000000) ≤ -Real.log (2147424271 / 2500000000) ∧
    -Real.log (2147424271 / 2500000000) ≤ (76010811 / 500000000) := by
  have h := checkLog_sound (w := (352575729 / 4647424271)) (n := 12)
    (lo := (152021621 / 1000000000)) (hi := (76010811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2147424271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2147424271) = 1/(2147424271 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13400 : Bounds (-76010811 / 500000000) (-152021621 / 1000000000) (Real.log (2147424271 / 2500000000)) := by
  have h := reflection_log_13400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13401_neg : (149754291 / 1000000000) ≤ -Real.log (34436779431 / 40000000000) ∧
    -Real.log (34436779431 / 40000000000) ≤ (37438573 / 250000000) := by
  have h := checkLog_sound (w := (5563220569 / 74436779431)) (n := 12)
    (lo := (149754291 / 1000000000)) (hi := (37438573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34436779431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34436779431) = 1/(34436779431 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13401 : Bounds (-37438573 / 250000000) (-149754291 / 1000000000) (Real.log (34436779431 / 40000000000)) := by
  have h := reflection_log_13401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13402_neg : (391827929 / 500000000) ≤ -Real.log (500000000000 / 1094731008747) ∧
    -Real.log (500000000000 / 1094731008747) ≤ (39182793 / 50000000) := by
  have h := checkLog_sound (w := (94731008747 / 2094731008747)) (n := 12)
    (lo := (45254339 / 500000000)) (hi := (90508679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094731008747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094731008747 / 1000000000000) = 1/(500000000000 / 1094731008747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13402 : Bounds (391827929 / 500000000) (39182793 / 50000000) (Real.log (1094731008747 / 500000000000)) := by
  have h := reflection_log_13402_neg
  have he : Real.log (1094731008747 / 500000000000) = -Real.log (500000000000 / 1094731008747) := by
    rw [show ((1094731008747 / 500000000000) : ℝ) = ((500000000000 / 1094731008747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13403_neg : (789714383 / 1000000000) ≤ -Real.log (500000000000 / 1101383595427) ∧
    -Real.log (500000000000 / 1101383595427) ≤ (157942877 / 200000000) := by
  have h := checkLog_sound (w := (101383595427 / 2101383595427)) (n := 12)
    (lo := (96567203 / 1000000000)) (hi := (24141801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101383595427 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1101383595427 / 1000000000000) = 1/(500000000000 / 1101383595427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13403 : Bounds (789714383 / 1000000000) (157942877 / 200000000) (Real.log (1101383595427 / 500000000000)) := by
  have h := reflection_log_13403_neg
  have he : Real.log (1101383595427 / 500000000000) = -Real.log (500000000000 / 1101383595427) := by
    rw [show ((1101383595427 / 500000000000) : ℝ) = ((500000000000 / 1101383595427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13404_neg : (1669431419 / 1000000000) ≤ -Real.log (500000000000 / 2654574132493) ∧
    -Real.log (500000000000 / 2654574132493) ≤ (834715711 / 500000000) := by
  have h := checkLog_sound (w := (654574132493 / 4654574132493)) (n := 12)
    (lo := (283137059 / 1000000000)) (hi := (14156853 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2654574132493 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2654574132493 / 2000000000000) = 1/(500000000000 / 2654574132493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13404 : Bounds (1669431419 / 1000000000) (834715711 / 500000000) (Real.log (2654574132493 / 500000000000)) := by
  have h := reflection_log_13404_neg
  have he : Real.log (2654574132493 / 500000000000) = -Real.log (500000000000 / 2654574132493) := by
    rw [show ((2654574132493 / 500000000000) : ℝ) = ((500000000000 / 2654574132493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13405_neg : (522358859 / 1000000000) ≤ -Real.log (500 / 843) ∧
    -Real.log (500 / 843) ≤ (26117943 / 50000000) := by
  have h := checkLog_sound (w := (343 / 1343)) (n := 12)
    (lo := (522358859 / 1000000000)) (hi := (26117943 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 500) = 1/(500 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13405 : Bounds (522358859 / 1000000000) (26117943 / 50000000) (Real.log (843 / 500)) := by
  have h := reflection_log_13405_neg
  have he : Real.log (843 / 500) = -Real.log (500 / 843) := by
    rw [show ((843 / 500) : ℝ) = ((500 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13406_neg : (289590573 / 250000000) ≤ -Real.log (157 / 500) ∧
    -Real.log (157 / 500) ≤ (579181147 / 500000000) := by
  have h := checkLog_sound (w := (93 / 407)) (n := 12)
    (lo := (58151889 / 125000000)) (hi := (465215113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 157) = 1/(157 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13406 : Bounds (-579181147 / 500000000) (-289590573 / 250000000) (Real.log (157 / 500)) := by
  have h := reflection_log_13406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13407_neg : (171441 / 250000000) ≤ -Real.log (500000 / 500343) ∧
    -Real.log (500000 / 500343) ≤ (137153 / 200000000) := by
  have h := checkLog_sound (w := (343 / 1000343)) (n := 12)
    (lo := (171441 / 250000000)) (hi := (137153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500343 / 500000) = 1/(500000 / 500343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13407 : Bounds (171441 / 250000000) (137153 / 200000000) (Real.log (500343 / 500000)) := by
  have h := reflection_log_13407_neg
  have he : Real.log (500343 / 500000) = -Real.log (500000 / 500343) := by
    rw [show ((500343 / 500000) : ℝ) = ((500000 / 500343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13408_neg : (137247 / 200000000) ≤ -Real.log (499657 / 500000) ∧
    -Real.log (499657 / 500000) ≤ (171559 / 250000000) := by
  have h := checkLog_sound (w := (343 / 999657)) (n := 12)
    (lo := (137247 / 200000000)) (hi := (171559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499657) = 1/(499657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13408 : Bounds (-171559 / 250000000) (-137247 / 200000000) (Real.log (499657 / 500000)) := by
  have h := reflection_log_13408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13409_neg : (159202501 / 500000000) ≤ -Real.log (1000000 / 1374933) ∧
    -Real.log (1000000 / 1374933) ≤ (318405003 / 1000000000) := by
  have h := checkLog_sound (w := (374933 / 2374933)) (n := 12)
    (lo := (159202501 / 500000000)) (hi := (318405003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374933 / 1000000) = 1/(1000000 / 1374933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13409 : Bounds (159202501 / 500000000) (318405003 / 1000000000) (Real.log (1374933 / 1000000)) := by
  have h := reflection_log_13409_neg
  have he : Real.log (1374933 / 1000000) = -Real.log (1000000 / 1374933) := by
    rw [show ((1374933 / 1000000) : ℝ) = ((1000000 / 1374933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13410_neg : (234948217 / 500000000) ≤ -Real.log (625067 / 1000000) ∧
    -Real.log (625067 / 1000000) ≤ (93979287 / 200000000) := by
  have h := checkLog_sound (w := (374933 / 1625067)) (n := 12)
    (lo := (234948217 / 500000000)) (hi := (93979287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625067) = 1/(625067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13410 : Bounds (-93979287 / 200000000) (-234948217 / 500000000) (Real.log (625067 / 1000000)) := by
  have h := reflection_log_13410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13411_neg : (64060731 / 200000000) ≤ -Real.log (500000 / 688773) ∧
    -Real.log (500000 / 688773) ≤ (40037957 / 125000000) := by
  have h := checkLog_sound (w := (188773 / 1188773)) (n := 12)
    (lo := (64060731 / 200000000)) (hi := (40037957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688773 / 500000) = 1/(500000 / 688773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13411 : Bounds (64060731 / 200000000) (40037957 / 125000000) (Real.log (688773 / 500000)) := by
  have h := reflection_log_13411_neg
  have he : Real.log (688773 / 500000) = -Real.log (500000 / 688773) := by
    rw [show ((688773 / 500000) : ℝ) = ((500000 / 688773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13412_neg : (118521387 / 250000000) ≤ -Real.log (311227 / 500000) ∧
    -Real.log (311227 / 500000) ≤ (474085549 / 1000000000) := by
  have h := checkLog_sound (w := (188773 / 811227)) (n := 12)
    (lo := (118521387 / 250000000)) (hi := (474085549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311227) = 1/(311227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13412 : Bounds (-474085549 / 1000000000) (-118521387 / 250000000) (Real.log (311227 / 500000)) := by
  have h := reflection_log_13412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13413_neg : (153781893 / 1000000000) ≤ -Real.log (214364754471 / 250000000000) ∧
    -Real.log (214364754471 / 250000000000) ≤ (76890947 / 500000000) := by
  have h := checkLog_sound (w := (35635245529 / 464364754471)) (n := 12)
    (lo := (153781893 / 1000000000)) (hi := (76890947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 214364754471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 214364754471) = 1/(214364754471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13413 : Bounds (-76890947 / 500000000) (-153781893 / 1000000000) (Real.log (214364754471 / 250000000000)) := by
  have h := reflection_log_13413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13414_neg : (18936429 / 125000000) ≤ -Real.log (859425245511 / 1000000000000) ∧
    -Real.log (859425245511 / 1000000000000) ≤ (151491433 / 1000000000) := by
  have h := checkLog_sound (w := (140574754489 / 1859425245511)) (n := 12)
    (lo := (18936429 / 125000000)) (hi := (151491433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 859425245511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 859425245511) = 1/(859425245511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13414 : Bounds (-151491433 / 1000000000) (-18936429 / 125000000) (Real.log (859425245511 / 1000000000000)) := by
  have h := reflection_log_13414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13415_neg : (788301437 / 1000000000) ≤ -Real.log (31250000000 / 68739281149) ∧
    -Real.log (31250000000 / 68739281149) ≤ (788301439 / 1000000000) := by
  have h := checkLog_sound (w := (6239281149 / 131239281149)) (n := 12)
    (lo := (95154257 / 1000000000)) (hi := (47577129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68739281149 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68739281149 / 62500000000) = 1/(31250000000 / 68739281149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13415 : Bounds (788301437 / 1000000000) (788301439 / 1000000000) (Real.log (68739281149 / 31250000000)) := by
  have h := reflection_log_13415_neg
  have he : Real.log (68739281149 / 31250000000) = -Real.log (31250000000 / 68739281149) := by
    rw [show ((68739281149 / 31250000000) : ℝ) = ((31250000000 / 68739281149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13416_neg : (794389203 / 1000000000) ≤ -Real.log (500000000000 / 1106544419347) ∧
    -Real.log (500000000000 / 1106544419347) ≤ (158877841 / 200000000) := by
  have h := checkLog_sound (w := (106544419347 / 2106544419347)) (n := 12)
    (lo := (101242023 / 1000000000)) (hi := (12655253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106544419347 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1106544419347 / 1000000000000) = 1/(500000000000 / 1106544419347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13416 : Bounds (794389203 / 1000000000) (158877841 / 200000000) (Real.log (1106544419347 / 500000000000)) := by
  have h := reflection_log_13416_neg
  have he : Real.log (1106544419347 / 500000000000) = -Real.log (500000000000 / 1106544419347) := by
    rw [show ((1106544419347 / 500000000000) : ℝ) = ((500000000000 / 1106544419347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13417_neg : (1669431419 / 1000000000) ≤ -Real.log (125000000000 / 663643533123) ∧
    -Real.log (125000000000 / 663643533123) ≤ (834715711 / 500000000) := by
  have h := checkLog_sound (w := (163643533123 / 1163643533123)) (n := 12)
    (lo := (283137059 / 1000000000)) (hi := (14156853 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663643533123 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(663643533123 / 500000000000) = 1/(125000000000 / 663643533123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13417 : Bounds (1669431419 / 1000000000) (834715711 / 500000000) (Real.log (663643533123 / 125000000000)) := by
  have h := reflection_log_13417_neg
  have he : Real.log (663643533123 / 125000000000) = -Real.log (125000000000 / 663643533123) := by
    rw [show ((663643533123 / 125000000000) : ℝ) = ((125000000000 / 663643533123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13418_neg : (1680721151 / 1000000000) ≤ -Real.log (500000000000 / 2684713375797) ∧
    -Real.log (500000000000 / 2684713375797) ≤ (840360577 / 500000000) := by
  have h := checkLog_sound (w := (684713375797 / 4684713375797)) (n := 12)
    (lo := (294426791 / 1000000000)) (hi := (36803349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2684713375797 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2684713375797 / 2000000000000) = 1/(500000000000 / 2684713375797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13418 : Bounds (1680721151 / 1000000000) (840360577 / 500000000) (Real.log (2684713375797 / 500000000000)) := by
  have h := reflection_log_13418_neg
  have he : Real.log (2684713375797 / 500000000000) = -Real.log (500000000000 / 2684713375797) := by
    rw [show ((2684713375797 / 500000000000) : ℝ) = ((500000000000 / 2684713375797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13419_neg : (524136637 / 1000000000) ≤ -Real.log (1000 / 1689) ∧
    -Real.log (1000 / 1689) ≤ (262068319 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2689)) (n := 12)
    (lo := (524136637 / 1000000000)) (hi := (262068319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689 / 1000) = 1/(1000 / 1689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13419 : Bounds (524136637 / 1000000000) (262068319 / 500000000) (Real.log (1689 / 1000)) := by
  have h := reflection_log_13419_neg
  have he : Real.log (1689 / 1000) = -Real.log (1000 / 1689) := by
    rw [show ((1689 / 1000) : ℝ) = ((1000 / 1689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13420_neg : (583981183 / 500000000) ≤ -Real.log (311 / 1000) ∧
    -Real.log (311 / 1000) ≤ (4562353 / 3906250) := by
  have h := checkLog_sound (w := (189 / 811)) (n := 12)
    (lo := (237407593 / 500000000)) (hi := (474815187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 311) = 1/(311 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13420 : Bounds (-4562353 / 3906250) (-583981183 / 500000000) (Real.log (311 / 1000)) := by
  have h := reflection_log_13420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13421_neg : (344381 / 500000000) ≤ -Real.log (1000000 / 1000689) ∧
    -Real.log (1000000 / 1000689) ≤ (688763 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 2000689)) (n := 12)
    (lo := (344381 / 500000000)) (hi := (688763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000689 / 1000000) = 1/(1000000 / 1000689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13421 : Bounds (344381 / 500000000) (688763 / 1000000000) (Real.log (1000689 / 1000000)) := by
  have h := reflection_log_13421_neg
  have he : Real.log (1000689 / 1000000) = -Real.log (1000000 / 1000689) := by
    rw [show ((1000689 / 1000000) : ℝ) = ((1000000 / 1000689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13422_neg : (689237 / 1000000000) ≤ -Real.log (999311 / 1000000) ∧
    -Real.log (999311 / 1000000) ≤ (344619 / 500000000) := by
  have h := checkLog_sound (w := (689 / 1999311)) (n := 12)
    (lo := (689237 / 1000000000)) (hi := (344619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999311) = 1/(999311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13422 : Bounds (-344619 / 500000000) (-689237 / 1000000000) (Real.log (999311 / 1000000)) := by
  have h := reflection_log_13422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13423_neg : (319862193 / 1000000000) ≤ -Real.log (500000 / 688469) ∧
    -Real.log (500000 / 688469) ≤ (159931097 / 500000000) := by
  have h := checkLog_sound (w := (188469 / 1188469)) (n := 12)
    (lo := (319862193 / 1000000000)) (hi := (159931097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688469 / 500000) = 1/(500000 / 688469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13423 : Bounds (319862193 / 1000000000) (159931097 / 500000000) (Real.log (688469 / 500000)) := by
  have h := reflection_log_13423_neg
  have he : Real.log (688469 / 500000) = -Real.log (500000 / 688469) := by
    rw [show ((688469 / 500000) : ℝ) = ((500000 / 688469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13424_neg : (236554623 / 500000000) ≤ -Real.log (311531 / 500000) ∧
    -Real.log (311531 / 500000) ≤ (473109247 / 1000000000) := by
  have h := checkLog_sound (w := (188469 / 811531)) (n := 12)
    (lo := (236554623 / 500000000)) (hi := (473109247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311531) = 1/(311531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13424 : Bounds (-473109247 / 1000000000) (-236554623 / 500000000) (Real.log (311531 / 500000)) := by
  have h := reflection_log_13424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13425_neg : (160881941 / 500000000) ≤ -Real.log (1000000 / 1379559) ∧
    -Real.log (1000000 / 1379559) ≤ (321763883 / 1000000000) := by
  have h := checkLog_sound (w := (379559 / 2379559)) (n := 12)
    (lo := (160881941 / 500000000)) (hi := (321763883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379559 / 1000000) = 1/(1000000 / 1379559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13425 : Bounds (160881941 / 500000000) (321763883 / 1000000000) (Real.log (1379559 / 1000000)) := by
  have h := reflection_log_13425_neg
  have he : Real.log (1379559 / 1000000) = -Real.log (1000000 / 1379559) := by
    rw [show ((1379559 / 1000000) : ℝ) = ((1000000 / 1379559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13426_neg : (477324763 / 1000000000) ≤ -Real.log (620441 / 1000000) ∧
    -Real.log (620441 / 1000000) ≤ (119331191 / 250000000) := by
  have h := checkLog_sound (w := (379559 / 1620441)) (n := 12)
    (lo := (477324763 / 1000000000)) (hi := (119331191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 620441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 620441) = 1/(620441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13426 : Bounds (-119331191 / 250000000) (-477324763 / 1000000000) (Real.log (620441 / 1000000)) := by
  have h := reflection_log_13426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13427_neg : (1944511 / 12500000) ≤ -Real.log (855934965519 / 1000000000000) ∧
    -Real.log (855934965519 / 1000000000000) ≤ (155560881 / 1000000000) := by
  have h := checkLog_sound (w := (144065034481 / 1855934965519)) (n := 12)
    (lo := (1944511 / 12500000)) (hi := (155560881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 855934965519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 855934965519) = 1/(855934965519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13427 : Bounds (-155560881 / 1000000000) (-1944511 / 12500000) (Real.log (855934965519 / 1000000000000)) := by
  have h := reflection_log_13427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13428_neg : (153247053 / 1000000000) ≤ -Real.log (214479436039 / 250000000000) ∧
    -Real.log (214479436039 / 250000000000) ≤ (76623527 / 500000000) := by
  have h := checkLog_sound (w := (35520563961 / 464479436039)) (n := 12)
    (lo := (153247053 / 1000000000)) (hi := (76623527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 214479436039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 214479436039) = 1/(214479436039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13428 : Bounds (-76623527 / 500000000) (-153247053 / 1000000000) (Real.log (214479436039 / 250000000000)) := by
  have h := reflection_log_13428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13429_neg : (792971439 / 1000000000) ≤ -Real.log (500000000000 / 1104976711787) ∧
    -Real.log (500000000000 / 1104976711787) ≤ (792971441 / 1000000000) := by
  have h := checkLog_sound (w := (104976711787 / 2104976711787)) (n := 12)
    (lo := (99824259 / 1000000000)) (hi := (4991213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104976711787 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1104976711787 / 1000000000000) = 1/(500000000000 / 1104976711787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13429 : Bounds (792971439 / 1000000000) (792971441 / 1000000000) (Real.log (1104976711787 / 500000000000)) := by
  have h := reflection_log_13429_neg
  have he : Real.log (1104976711787 / 500000000000) = -Real.log (500000000000 / 1104976711787) := by
    rw [show ((1104976711787 / 500000000000) : ℝ) = ((500000000000 / 1104976711787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13430_neg : (159817729 / 200000000) ≤ -Real.log (250000000000 / 555878399397) ∧
    -Real.log (250000000000 / 555878399397) ≤ (799088647 / 1000000000) := by
  have h := checkLog_sound (w := (55878399397 / 1055878399397)) (n := 12)
    (lo := (21188293 / 200000000)) (hi := (52970733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555878399397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555878399397 / 500000000000) = 1/(250000000000 / 555878399397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13430 : Bounds (159817729 / 200000000) (799088647 / 1000000000) (Real.log (555878399397 / 250000000000)) := by
  have h := reflection_log_13430_neg
  have he : Real.log (555878399397 / 250000000000) = -Real.log (250000000000 / 555878399397) := by
    rw [show ((555878399397 / 250000000000) : ℝ) = ((250000000000 / 555878399397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13431_neg : (1680721151 / 1000000000) ≤ -Real.log (125000000000 / 671178343949) ∧
    -Real.log (125000000000 / 671178343949) ≤ (840360577 / 500000000) := by
  have h := checkLog_sound (w := (171178343949 / 1171178343949)) (n := 12)
    (lo := (294426791 / 1000000000)) (hi := (36803349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671178343949 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(671178343949 / 500000000000) = 1/(125000000000 / 671178343949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13431 : Bounds (1680721151 / 1000000000) (840360577 / 500000000) (Real.log (671178343949 / 125000000000)) := by
  have h := reflection_log_13431_neg
  have he : Real.log (671178343949 / 125000000000) = -Real.log (125000000000 / 671178343949) := by
    rw [show ((671178343949 / 125000000000) : ℝ) = ((125000000000 / 671178343949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13432_neg : (1692099003 / 1000000000) ≤ -Real.log (250000000000 / 1357717041801) ∧
    -Real.log (250000000000 / 1357717041801) ≤ (846049503 / 500000000) := by
  have h := checkLog_sound (w := (357717041801 / 2357717041801)) (n := 12)
    (lo := (305804643 / 1000000000)) (hi := (76451161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357717041801 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1357717041801 / 1000000000000) = 1/(250000000000 / 1357717041801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13432 : Bounds (1692099003 / 1000000000) (846049503 / 500000000) (Real.log (1357717041801 / 250000000000)) := by
  have h := reflection_log_13432_neg
  have he : Real.log (1357717041801 / 250000000000) = -Real.log (250000000000 / 1357717041801) := by
    rw [show ((1357717041801 / 250000000000) : ℝ) = ((250000000000 / 1357717041801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13433_neg : (525911261 / 1000000000) ≤ -Real.log (250 / 423) ∧
    -Real.log (250 / 423) ≤ (262955631 / 500000000) := by
  have h := checkLog_sound (w := (173 / 673)) (n := 12)
    (lo := (525911261 / 1000000000)) (hi := (262955631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423 / 250) = 1/(250 / 423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13433 : Bounds (525911261 / 1000000000) (262955631 / 500000000) (Real.log (423 / 250)) := by
  have h := reflection_log_13433_neg
  have he : Real.log (423 / 250) = -Real.log (250 / 423) := by
    rw [show ((423 / 250) : ℝ) = ((250 / 423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13434_neg : (235531099 / 200000000) ≤ -Real.log (77 / 250) ∧
    -Real.log (77 / 250) ≤ (1177655497 / 1000000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 77) = 1/(77 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13434 : Bounds (-1177655497 / 1000000000) (-235531099 / 200000000) (Real.log (77 / 250)) := by
  have h := reflection_log_13434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13435_neg : (8647 / 12500000) ≤ -Real.log (250000 / 250173) ∧
    -Real.log (250000 / 250173) ≤ (691761 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 500173)) (n := 12)
    (lo := (8647 / 12500000)) (hi := (691761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250173 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250173 / 250000) = 1/(250000 / 250173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13435 : Bounds (8647 / 12500000) (691761 / 1000000000) (Real.log (250173 / 250000)) := by
  have h := reflection_log_13435_neg
  have he : Real.log (250173 / 250000) = -Real.log (250000 / 250173) := by
    rw [show ((250173 / 250000) : ℝ) = ((250000 / 250173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13436_neg : (692239 / 1000000000) ≤ -Real.log (249827 / 250000) ∧
    -Real.log (249827 / 250000) ≤ (8653 / 12500000) := by
  have h := checkLog_sound (w := (173 / 499827)) (n := 12)
    (lo := (692239 / 1000000000)) (hi := (8653 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249827) = 1/(249827 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13436 : Bounds (-8653 / 12500000) (-692239 / 1000000000) (Real.log (249827 / 250000)) := by
  have h := reflection_log_13436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13437_neg : (321320889 / 1000000000) ≤ -Real.log (250000 / 344737) ∧
    -Real.log (250000 / 344737) ≤ (32132089 / 100000000) := by
  have h := checkLog_sound (w := (94737 / 594737)) (n := 12)
    (lo := (321320889 / 1000000000)) (hi := (32132089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344737 / 250000) = 1/(250000 / 344737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13437 : Bounds (321320889 / 1000000000) (32132089 / 100000000) (Real.log (344737 / 250000)) := by
  have h := reflection_log_13437_neg
  have he : Real.log (344737 / 250000) = -Real.log (250000 / 344737) := by
    rw [show ((344737 / 250000) : ℝ) = ((250000 / 344737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13438_neg : (29771279 / 62500000) ≤ -Real.log (155263 / 250000) ∧
    -Real.log (155263 / 250000) ≤ (95268093 / 200000000) := by
  have h := checkLog_sound (w := (94737 / 405263)) (n := 12)
    (lo := (29771279 / 62500000)) (hi := (95268093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 155263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 155263) = 1/(155263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13438 : Bounds (-95268093 / 200000000) (-29771279 / 62500000) (Real.log (155263 / 250000)) := by
  have h := reflection_log_13438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13439_neg : (25252 / 78125) ≤ -Real.log (1000000 / 1381577) ∧
    -Real.log (1000000 / 1381577) ≤ (323225601 / 1000000000) := by
  have h := checkLog_sound (w := (381577 / 2381577)) (n := 12)
    (lo := (25252 / 78125)) (hi := (323225601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381577 / 1000000) = 1/(1000000 / 1381577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13439 : Bounds (25252 / 78125) (323225601 / 1000000000) (Real.log (1381577 / 1000000)) := by
  have h := reflection_log_13439_neg
  have he : Real.log (1381577 / 1000000) = -Real.log (1000000 / 1381577) := by
    rw [show ((1381577 / 1000000) : ℝ) = ((1000000 / 1381577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
