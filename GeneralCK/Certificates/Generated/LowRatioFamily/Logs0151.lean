import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9664_neg : (38209733 / 62500000) ≤ -Real.log (488281250 / 899867293) ∧
    -Real.log (488281250 / 899867293) ≤ (611355729 / 1000000000) := by
  have h := checkLog_sound (w := (411586043 / 1388148543)) (n := 12)
    (lo := (38209733 / 62500000)) (hi := (611355729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899867293 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899867293 / 488281250) = 1/(488281250 / 899867293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9664 : Bounds (38209733 / 62500000) (611355729 / 1000000000) (Real.log (899867293 / 488281250)) := by
  have h := reflection_log_9664_neg
  have he : Real.log (899867293 / 488281250) = -Real.log (488281250 / 899867293) := by
    rw [show ((899867293 / 488281250) : ℝ) = ((488281250 / 899867293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9665_neg : (52010781 / 200000000) ≤ -Real.log (1000 / 1297) ∧
    -Real.log (1000 / 1297) ≤ (130026953 / 500000000) := by
  have h := checkLog_sound (w := (297 / 2297)) (n := 12)
    (lo := (52010781 / 200000000)) (hi := (130026953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297 / 1000) = 1/(1000 / 1297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9665 : Bounds (52010781 / 200000000) (130026953 / 500000000) (Real.log (1297 / 1000)) := by
  have h := reflection_log_9665_neg
  have he : Real.log (1297 / 1000) = -Real.log (1000 / 1297) := by
    rw [show ((1297 / 1000) : ℝ) = ((1000 / 1297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9666_neg : (352398387 / 1000000000) ≤ -Real.log (703 / 1000) ∧
    -Real.log (703 / 1000) ≤ (88099597 / 250000000) := by
  have h := checkLog_sound (w := (297 / 1703)) (n := 12)
    (lo := (352398387 / 1000000000)) (hi := (88099597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 703) = 1/(703 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9666 : Bounds (-88099597 / 250000000) (-352398387 / 1000000000) (Real.log (703 / 1000)) := by
  have h := reflection_log_9666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9667_neg : (59391 / 200000000) ≤ -Real.log (1000000 / 1000297) ∧
    -Real.log (1000000 / 1000297) ≤ (74239 / 250000000) := by
  have h := checkLog_sound (w := (297 / 2000297)) (n := 12)
    (lo := (59391 / 200000000)) (hi := (74239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000297 / 1000000) = 1/(1000000 / 1000297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9667 : Bounds (59391 / 200000000) (74239 / 250000000) (Real.log (1000297 / 1000000)) := by
  have h := reflection_log_9667_neg
  have he : Real.log (1000297 / 1000000) = -Real.log (1000000 / 1000297) := by
    rw [show ((1000297 / 1000000) : ℝ) = ((1000000 / 1000297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9668_neg : (74261 / 250000000) ≤ -Real.log (999703 / 1000000) ∧
    -Real.log (999703 / 1000000) ≤ (59409 / 200000000) := by
  have h := checkLog_sound (w := (297 / 1999703)) (n := 12)
    (lo := (74261 / 250000000)) (hi := (59409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999703) = 1/(999703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9668 : Bounds (-59409 / 200000000) (-74261 / 250000000) (Real.log (999703 / 1000000)) := by
  have h := reflection_log_9668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9669_neg : (70105703 / 500000000) ≤ -Real.log (1000000 / 1150517) ∧
    -Real.log (1000000 / 1150517) ≤ (140211407 / 1000000000) := by
  have h := checkLog_sound (w := (150517 / 2150517)) (n := 12)
    (lo := (70105703 / 500000000)) (hi := (140211407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150517 / 1000000) = 1/(1000000 / 1150517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9669 : Bounds (70105703 / 500000000) (140211407 / 1000000000) (Real.log (1150517 / 1000000)) := by
  have h := reflection_log_9669_neg
  have he : Real.log (1150517 / 1000000) = -Real.log (1000000 / 1150517) := by
    rw [show ((1150517 / 1000000) : ℝ) = ((1000000 / 1150517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9670_neg : (163127349 / 1000000000) ≤ -Real.log (849483 / 1000000) ∧
    -Real.log (849483 / 1000000) ≤ (3262547 / 20000000) := by
  have h := checkLog_sound (w := (150517 / 1849483)) (n := 12)
    (lo := (163127349 / 1000000000)) (hi := (3262547 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849483) = 1/(849483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9670 : Bounds (-3262547 / 20000000) (-163127349 / 1000000000) (Real.log (849483 / 1000000)) := by
  have h := reflection_log_9670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9671_neg : (70346841 / 500000000) ≤ -Real.log (31250 / 35971) ∧
    -Real.log (31250 / 35971) ≤ (140693683 / 1000000000) := by
  have h := checkLog_sound (w := (4721 / 67221)) (n := 12)
    (lo := (70346841 / 500000000)) (hi := (140693683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35971 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35971 / 31250) = 1/(31250 / 35971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9671 : Bounds (70346841 / 500000000) (140693683 / 1000000000) (Real.log (35971 / 31250)) := by
  have h := reflection_log_9671_neg
  have he : Real.log (35971 / 31250) = -Real.log (31250 / 35971) := by
    rw [show ((35971 / 31250) : ℝ) = ((31250 / 35971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9672_neg : (163780901 / 1000000000) ≤ -Real.log (26529 / 31250) ∧
    -Real.log (26529 / 31250) ≤ (81890451 / 500000000) := by
  have h := checkLog_sound (w := (4721 / 57779)) (n := 12)
    (lo := (163780901 / 1000000000)) (hi := (81890451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26529) = 1/(26529 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9672 : Bounds (-81890451 / 500000000) (-163780901 / 1000000000) (Real.log (26529 / 31250)) := by
  have h := reflection_log_9672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9673_neg : (23087219 / 1000000000) ≤ -Real.log (954274659 / 976562500) ∧
    -Real.log (954274659 / 976562500) ≤ (1154361 / 50000000) := by
  have h := checkLog_sound (w := (22287841 / 1930837159)) (n := 12)
    (lo := (23087219 / 1000000000)) (hi := (1154361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 954274659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 954274659) = 1/(954274659 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9673 : Bounds (-1154361 / 50000000) (-23087219 / 1000000000) (Real.log (954274659 / 976562500)) := by
  have h := reflection_log_9673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9674_neg : (22915943 / 1000000000) ≤ -Real.log (977344632711 / 1000000000000) ∧
    -Real.log (977344632711 / 1000000000000) ≤ (2864493 / 125000000) := by
  have h := checkLog_sound (w := (22655367289 / 1977344632711)) (n := 12)
    (lo := (22915943 / 1000000000)) (hi := (2864493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977344632711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977344632711) = 1/(977344632711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9674 : Bounds (-2864493 / 125000000) (-22915943 / 1000000000) (Real.log (977344632711 / 1000000000000)) := by
  have h := reflection_log_9674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9675_neg : (75834689 / 250000000) ≤ -Real.log (500000000000 / 677186594669) ∧
    -Real.log (500000000000 / 677186594669) ≤ (303338757 / 1000000000) := by
  have h := checkLog_sound (w := (177186594669 / 1177186594669)) (n := 12)
    (lo := (75834689 / 250000000)) (hi := (303338757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677186594669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677186594669 / 500000000000) = 1/(500000000000 / 677186594669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9675 : Bounds (75834689 / 250000000) (303338757 / 1000000000) (Real.log (677186594669 / 500000000000)) := by
  have h := reflection_log_9675_neg
  have he : Real.log (677186594669 / 500000000000) = -Real.log (500000000000 / 677186594669) := by
    rw [show ((677186594669 / 500000000000) : ℝ) = ((500000000000 / 677186594669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9676_neg : (38059323 / 125000000) ≤ -Real.log (500000000000 / 677956198877) ∧
    -Real.log (500000000000 / 677956198877) ≤ (60894917 / 200000000) := by
  have h := checkLog_sound (w := (177956198877 / 1177956198877)) (n := 12)
    (lo := (38059323 / 125000000)) (hi := (60894917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677956198877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677956198877 / 500000000000) = 1/(500000000000 / 677956198877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9676 : Bounds (38059323 / 125000000) (60894917 / 200000000) (Real.log (677956198877 / 500000000000)) := by
  have h := reflection_log_9676_neg
  have he : Real.log (677956198877 / 500000000000) = -Real.log (500000000000 / 677956198877) := by
    rw [show ((677956198877 / 500000000000) : ℝ) = ((500000000000 / 677956198877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9677_neg : (38209733 / 62500000) ≤ -Real.log (500000000000 / 921464108031) ∧
    -Real.log (500000000000 / 921464108031) ≤ (611355729 / 1000000000) := by
  have h := checkLog_sound (w := (421464108031 / 1421464108031)) (n := 12)
    (lo := (38209733 / 62500000)) (hi := (611355729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921464108031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921464108031 / 500000000000) = 1/(500000000000 / 921464108031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9677 : Bounds (38209733 / 62500000) (611355729 / 1000000000) (Real.log (921464108031 / 500000000000)) := by
  have h := reflection_log_9677_neg
  have he : Real.log (921464108031 / 500000000000) = -Real.log (500000000000 / 921464108031) := by
    rw [show ((921464108031 / 500000000000) : ℝ) = ((500000000000 / 921464108031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9678_neg : (153113073 / 250000000) ≤ -Real.log (250000000000 / 461237553343) ∧
    -Real.log (250000000000 / 461237553343) ≤ (612452293 / 1000000000) := by
  have h := checkLog_sound (w := (211237553343 / 711237553343)) (n := 12)
    (lo := (153113073 / 250000000)) (hi := (612452293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461237553343 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461237553343 / 250000000000) = 1/(250000000000 / 461237553343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9678 : Bounds (153113073 / 250000000) (612452293 / 1000000000) (Real.log (461237553343 / 250000000000)) := by
  have h := reflection_log_9678_neg
  have he : Real.log (461237553343 / 250000000000) = -Real.log (250000000000 / 461237553343) := by
    rw [show ((461237553343 / 250000000000) : ℝ) = ((250000000000 / 461237553343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9679_neg : (32554917 / 125000000) ≤ -Real.log (400 / 519) ∧
    -Real.log (400 / 519) ≤ (260439337 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 919)) (n := 12)
    (lo := (32554917 / 125000000)) (hi := (260439337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(519 / 400) = 1/(400 / 519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9679 : Bounds (32554917 / 125000000) (260439337 / 1000000000) (Real.log (519 / 400)) := by
  have h := reflection_log_9679_neg
  have he : Real.log (519 / 400) = -Real.log (400 / 519) := by
    rw [show ((519 / 400) : ℝ) = ((400 / 519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9680_neg : (353109877 / 1000000000) ≤ -Real.log (281 / 400) ∧
    -Real.log (281 / 400) ≤ (176554939 / 500000000) := by
  have h := checkLog_sound (w := (119 / 681)) (n := 12)
    (lo := (353109877 / 1000000000)) (hi := (176554939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 281) = 1/(281 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9680 : Bounds (-176554939 / 500000000) (-353109877 / 1000000000) (Real.log (281 / 400)) := by
  have h := reflection_log_9680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9681_neg : (59491 / 200000000) ≤ -Real.log (400000 / 400119) ∧
    -Real.log (400000 / 400119) ≤ (18591 / 62500000) := by
  have h := checkLog_sound (w := (119 / 800119)) (n := 12)
    (lo := (59491 / 200000000)) (hi := (18591 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400119 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400119 / 400000) = 1/(400000 / 400119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9681 : Bounds (59491 / 200000000) (18591 / 62500000) (Real.log (400119 / 400000)) := by
  have h := reflection_log_9681_neg
  have he : Real.log (400119 / 400000) = -Real.log (400000 / 400119) := by
    rw [show ((400119 / 400000) : ℝ) = ((400000 / 400119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9682_neg : (37193 / 125000000) ≤ -Real.log (399881 / 400000) ∧
    -Real.log (399881 / 400000) ≤ (59509 / 200000000) := by
  have h := checkLog_sound (w := (119 / 799881)) (n := 12)
    (lo := (37193 / 125000000)) (hi := (59509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399881) = 1/(399881 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9682 : Bounds (-59509 / 200000000) (-37193 / 125000000) (Real.log (399881 / 400000)) := by
  have h := reflection_log_9682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9683_neg : (2194361 / 15625000) ≤ -Real.log (1000000 / 1150779) ∧
    -Real.log (1000000 / 1150779) ≤ (28087821 / 200000000) := by
  have h := checkLog_sound (w := (150779 / 2150779)) (n := 12)
    (lo := (2194361 / 15625000)) (hi := (28087821 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150779 / 1000000) = 1/(1000000 / 1150779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9683 : Bounds (2194361 / 15625000) (28087821 / 200000000) (Real.log (1150779 / 1000000)) := by
  have h := reflection_log_9683_neg
  have he : Real.log (1150779 / 1000000) = -Real.log (1000000 / 1150779) := by
    rw [show ((1150779 / 1000000) : ℝ) = ((1000000 / 1150779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9684_neg : (8171791 / 50000000) ≤ -Real.log (849221 / 1000000) ∧
    -Real.log (849221 / 1000000) ≤ (163435821 / 1000000000) := by
  have h := checkLog_sound (w := (150779 / 1849221)) (n := 12)
    (lo := (8171791 / 50000000)) (hi := (163435821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849221) = 1/(849221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9684 : Bounds (-163435821 / 1000000000) (-8171791 / 50000000) (Real.log (849221 / 1000000)) := by
  have h := reflection_log_9684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9685_neg : (70461069 / 500000000) ≤ -Real.log (200000 / 230267) ∧
    -Real.log (200000 / 230267) ≤ (140922139 / 1000000000) := by
  have h := checkLog_sound (w := (30267 / 430267)) (n := 12)
    (lo := (70461069 / 500000000)) (hi := (140922139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230267 / 200000) = 1/(200000 / 230267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9685 : Bounds (70461069 / 500000000) (140922139 / 1000000000) (Real.log (230267 / 200000)) := by
  have h := reflection_log_9685_neg
  have he : Real.log (230267 / 200000) = -Real.log (200000 / 230267) := by
    rw [show ((230267 / 200000) : ℝ) = ((200000 / 230267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9686_neg : (1281959 / 7812500) ≤ -Real.log (169733 / 200000) ∧
    -Real.log (169733 / 200000) ≤ (164090753 / 1000000000) := by
  have h := checkLog_sound (w := (30267 / 369733)) (n := 12)
    (lo := (1281959 / 7812500)) (hi := (164090753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169733) = 1/(169733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9686 : Bounds (-164090753 / 1000000000) (-1281959 / 7812500) (Real.log (169733 / 200000)) := by
  have h := reflection_log_9686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9687_neg : (23168613 / 1000000000) ≤ -Real.log (39083908711 / 40000000000) ∧
    -Real.log (39083908711 / 40000000000) ≤ (11584307 / 500000000) := by
  have h := checkLog_sound (w := (916091289 / 79083908711)) (n := 12)
    (lo := (23168613 / 1000000000)) (hi := (11584307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39083908711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39083908711) = 1/(39083908711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9687 : Bounds (-11584307 / 500000000) (-23168613 / 1000000000) (Real.log (39083908711 / 40000000000)) := by
  have h := reflection_log_9687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9688_neg : (4599343 / 200000000) ≤ -Real.log (977265693159 / 1000000000000) ∧
    -Real.log (977265693159 / 1000000000000) ≤ (5749179 / 250000000) := by
  have h := checkLog_sound (w := (22734306841 / 1977265693159)) (n := 12)
    (lo := (4599343 / 200000000)) (hi := (5749179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977265693159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977265693159) = 1/(977265693159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9688 : Bounds (-5749179 / 250000000) (-4599343 / 200000000) (Real.log (977265693159 / 1000000000000)) := by
  have h := reflection_log_9688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9689_neg : (75968731 / 250000000) ≤ -Real.log (125000000000 / 169387444493) ∧
    -Real.log (125000000000 / 169387444493) ≤ (12154997 / 40000000) := by
  have h := checkLog_sound (w := (44387444493 / 294387444493)) (n := 12)
    (lo := (75968731 / 250000000)) (hi := (12154997 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169387444493 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169387444493 / 125000000000) = 1/(125000000000 / 169387444493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9689 : Bounds (75968731 / 250000000) (12154997 / 40000000) (Real.log (169387444493 / 125000000000)) := by
  have h := reflection_log_9689_neg
  have he : Real.log (169387444493 / 125000000000) = -Real.log (125000000000 / 169387444493) := by
    rw [show ((169387444493 / 125000000000) : ℝ) = ((125000000000 / 169387444493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9690_neg : (305012891 / 1000000000) ≤ -Real.log (250000000000 / 339160622861) ∧
    -Real.log (250000000000 / 339160622861) ≤ (76253223 / 250000000) := by
  have h := checkLog_sound (w := (89160622861 / 589160622861)) (n := 12)
    (lo := (305012891 / 1000000000)) (hi := (76253223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339160622861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339160622861 / 250000000000) = 1/(250000000000 / 339160622861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9690 : Bounds (305012891 / 1000000000) (76253223 / 250000000) (Real.log (339160622861 / 250000000000)) := by
  have h := reflection_log_9690_neg
  have he : Real.log (339160622861 / 250000000000) = -Real.log (250000000000 / 339160622861) := by
    rw [show ((339160622861 / 250000000000) : ℝ) = ((250000000000 / 339160622861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9691_neg : (153113073 / 250000000) ≤ -Real.log (100000000000 / 184495021337) ∧
    -Real.log (100000000000 / 184495021337) ≤ (612452293 / 1000000000) := by
  have h := checkLog_sound (w := (84495021337 / 284495021337)) (n := 12)
    (lo := (153113073 / 250000000)) (hi := (612452293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184495021337 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184495021337 / 100000000000) = 1/(100000000000 / 184495021337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9691 : Bounds (153113073 / 250000000) (612452293 / 1000000000) (Real.log (184495021337 / 100000000000)) := by
  have h := reflection_log_9691_neg
  have he : Real.log (184495021337 / 100000000000) = -Real.log (100000000000 / 184495021337) := by
    rw [show ((184495021337 / 100000000000) : ℝ) = ((100000000000 / 184495021337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9692_neg : (613549213 / 1000000000) ≤ -Real.log (125000000000 / 230871886121) ∧
    -Real.log (125000000000 / 230871886121) ≤ (306774607 / 500000000) := by
  have h := checkLog_sound (w := (105871886121 / 355871886121)) (n := 12)
    (lo := (613549213 / 1000000000)) (hi := (306774607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230871886121 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230871886121 / 125000000000) = 1/(125000000000 / 230871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9692 : Bounds (613549213 / 1000000000) (306774607 / 500000000) (Real.log (230871886121 / 125000000000)) := by
  have h := reflection_log_9692_neg
  have he : Real.log (230871886121 / 125000000000) = -Real.log (125000000000 / 230871886121) := by
    rw [show ((230871886121 / 125000000000) : ℝ) = ((125000000000 / 230871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9693_neg : (130412309 / 500000000) ≤ -Real.log (500 / 649) ∧
    -Real.log (500 / 649) ≤ (260824619 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1149)) (n := 12)
    (lo := (130412309 / 500000000)) (hi := (260824619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 500) = 1/(500 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9693 : Bounds (130412309 / 500000000) (260824619 / 1000000000) (Real.log (649 / 500)) := by
  have h := reflection_log_9693_neg
  have he : Real.log (649 / 500) = -Real.log (500 / 649) := by
    rw [show ((649 / 500) : ℝ) = ((500 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9694_neg : (176910937 / 500000000) ≤ -Real.log (351 / 500) ∧
    -Real.log (351 / 500) ≤ (113223 / 320000) := by
  have h := checkLog_sound (w := (149 / 851)) (n := 12)
    (lo := (176910937 / 500000000)) (hi := (113223 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 351) = 1/(351 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9694 : Bounds (-113223 / 320000) (-176910937 / 500000000) (Real.log (351 / 500)) := by
  have h := reflection_log_9694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9695_neg : (59591 / 200000000) ≤ -Real.log (500000 / 500149) ∧
    -Real.log (500000 / 500149) ≤ (74489 / 250000000) := by
  have h := checkLog_sound (w := (149 / 1000149)) (n := 12)
    (lo := (59591 / 200000000)) (hi := (74489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500149 / 500000) = 1/(500000 / 500149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9695 : Bounds (59591 / 200000000) (74489 / 250000000) (Real.log (500149 / 500000)) := by
  have h := reflection_log_9695_neg
  have he : Real.log (500149 / 500000) = -Real.log (500000 / 500149) := by
    rw [show ((500149 / 500000) : ℝ) = ((500000 / 500149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9696_neg : (74511 / 250000000) ≤ -Real.log (499851 / 500000) ∧
    -Real.log (499851 / 500000) ≤ (59609 / 200000000) := by
  have h := checkLog_sound (w := (149 / 999851)) (n := 12)
    (lo := (74511 / 250000000)) (hi := (59609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499851) = 1/(499851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9696 : Bounds (-59609 / 200000000) (-74511 / 250000000) (Real.log (499851 / 500000)) := by
  have h := reflection_log_9696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9697_neg : (562667 / 4000000) ≤ -Real.log (1000000 / 1151041) ∧
    -Real.log (1000000 / 1151041) ≤ (140666751 / 1000000000) := by
  have h := checkLog_sound (w := (151041 / 2151041)) (n := 12)
    (lo := (562667 / 4000000)) (hi := (140666751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151041 / 1000000) = 1/(1000000 / 1151041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9697 : Bounds (562667 / 4000000) (140666751 / 1000000000) (Real.log (1151041 / 1000000)) := by
  have h := reflection_log_9697_neg
  have he : Real.log (1151041 / 1000000) = -Real.log (1000000 / 1151041) := by
    rw [show ((1151041 / 1000000) : ℝ) = ((1000000 / 1151041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9698_neg : (32748877 / 200000000) ≤ -Real.log (848959 / 1000000) ∧
    -Real.log (848959 / 1000000) ≤ (81872193 / 500000000) := by
  have h := checkLog_sound (w := (151041 / 1848959)) (n := 12)
    (lo := (32748877 / 200000000)) (hi := (81872193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848959) = 1/(848959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9698 : Bounds (-81872193 / 500000000) (-32748877 / 200000000) (Real.log (848959 / 1000000)) := by
  have h := reflection_log_9698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9699_neg : (70574837 / 500000000) ≤ -Real.log (1000000 / 1151597) ∧
    -Real.log (1000000 / 1151597) ≤ (5645987 / 40000000) := by
  have h := checkLog_sound (w := (151597 / 2151597)) (n := 12)
    (lo := (70574837 / 500000000)) (hi := (5645987 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151597 / 1000000) = 1/(1000000 / 1151597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9699 : Bounds (70574837 / 500000000) (5645987 / 40000000) (Real.log (1151597 / 1000000)) := by
  have h := reflection_log_9699_neg
  have he : Real.log (1151597 / 1000000) = -Real.log (1000000 / 1151597) := by
    rw [show ((1151597 / 1000000) : ℝ) = ((1000000 / 1151597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9700_neg : (1027497 / 6250000) ≤ -Real.log (848403 / 1000000) ∧
    -Real.log (848403 / 1000000) ≤ (164399521 / 1000000000) := by
  have h := checkLog_sound (w := (151597 / 1848403)) (n := 12)
    (lo := (1027497 / 6250000)) (hi := (164399521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848403) = 1/(848403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9700 : Bounds (-164399521 / 1000000000) (-1027497 / 6250000) (Real.log (848403 / 1000000)) := by
  have h := reflection_log_9700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9701_neg : (4649969 / 200000000) ≤ -Real.log (977018349591 / 1000000000000) ∧
    -Real.log (977018349591 / 1000000000000) ≤ (11624923 / 500000000) := by
  have h := checkLog_sound (w := (22981650409 / 1977018349591)) (n := 12)
    (lo := (4649969 / 200000000)) (hi := (11624923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977018349591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977018349591) = 1/(977018349591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9701 : Bounds (-11624923 / 500000000) (-4649969 / 200000000) (Real.log (977018349591 / 1000000000000)) := by
  have h := reflection_log_9701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9702_neg : (4615527 / 200000000) ≤ -Real.log (977186616319 / 1000000000000) ∧
    -Real.log (977186616319 / 1000000000000) ≤ (5769409 / 250000000) := by
  have h := checkLog_sound (w := (22813383681 / 1977186616319)) (n := 12)
    (lo := (4615527 / 200000000)) (hi := (5769409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977186616319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977186616319) = 1/(977186616319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9702 : Bounds (-5769409 / 250000000) (-4615527 / 200000000) (Real.log (977186616319 / 1000000000000)) := by
  have h := reflection_log_9702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9703_neg : (594553 / 1953125) ≤ -Real.log (250000000000 / 338956592721) ∧
    -Real.log (250000000000 / 338956592721) ≤ (304411137 / 1000000000) := by
  have h := checkLog_sound (w := (88956592721 / 588956592721)) (n := 12)
    (lo := (594553 / 1953125)) (hi := (304411137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338956592721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338956592721 / 250000000000) = 1/(250000000000 / 338956592721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9703 : Bounds (594553 / 1953125) (304411137 / 1000000000) (Real.log (338956592721 / 250000000000)) := by
  have h := reflection_log_9703_neg
  have he : Real.log (338956592721 / 250000000000) = -Real.log (250000000000 / 338956592721) := by
    rw [show ((338956592721 / 250000000000) : ℝ) = ((250000000000 / 338956592721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9704_neg : (152774597 / 500000000) ≤ -Real.log (500000000000 / 678685129591) ∧
    -Real.log (500000000000 / 678685129591) ≤ (61109839 / 200000000) := by
  have h := checkLog_sound (w := (178685129591 / 1178685129591)) (n := 12)
    (lo := (152774597 / 500000000)) (hi := (61109839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678685129591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678685129591 / 500000000000) = 1/(500000000000 / 678685129591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9704 : Bounds (152774597 / 500000000) (61109839 / 200000000) (Real.log (678685129591 / 500000000000)) := by
  have h := reflection_log_9704_neg
  have he : Real.log (678685129591 / 500000000000) = -Real.log (500000000000 / 678685129591) := by
    rw [show ((678685129591 / 500000000000) : ℝ) = ((500000000000 / 678685129591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9705_neg : (613549213 / 1000000000) ≤ -Real.log (500000000000 / 923487544483) ∧
    -Real.log (500000000000 / 923487544483) ≤ (306774607 / 500000000) := by
  have h := checkLog_sound (w := (423487544483 / 1423487544483)) (n := 12)
    (lo := (613549213 / 1000000000)) (hi := (306774607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923487544483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923487544483 / 500000000000) = 1/(500000000000 / 923487544483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9705 : Bounds (613549213 / 1000000000) (306774607 / 500000000) (Real.log (923487544483 / 500000000000)) := by
  have h := reflection_log_9705_neg
  have he : Real.log (923487544483 / 500000000000) = -Real.log (500000000000 / 923487544483) := by
    rw [show ((923487544483 / 500000000000) : ℝ) = ((500000000000 / 923487544483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9706_neg : (614646493 / 1000000000) ≤ -Real.log (250000000000 / 462250712251) ∧
    -Real.log (250000000000 / 462250712251) ≤ (307323247 / 500000000) := by
  have h := checkLog_sound (w := (212250712251 / 712250712251)) (n := 12)
    (lo := (614646493 / 1000000000)) (hi := (307323247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462250712251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462250712251 / 250000000000) = 1/(250000000000 / 462250712251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9706 : Bounds (614646493 / 1000000000) (307323247 / 500000000) (Real.log (462250712251 / 250000000000)) := by
  have h := reflection_log_9706_neg
  have he : Real.log (462250712251 / 250000000000) = -Real.log (250000000000 / 462250712251) := by
    rw [show ((462250712251 / 250000000000) : ℝ) = ((250000000000 / 462250712251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9707_neg : (32651219 / 125000000) ≤ -Real.log (2000 / 2597) ∧
    -Real.log (2000 / 2597) ≤ (261209753 / 1000000000) := by
  have h := checkLog_sound (w := (597 / 4597)) (n := 12)
    (lo := (32651219 / 125000000)) (hi := (261209753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2597 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2597 / 2000) = 1/(2000 / 2597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9707 : Bounds (32651219 / 125000000) (261209753 / 1000000000) (Real.log (2597 / 2000)) := by
  have h := reflection_log_9707_neg
  have he : Real.log (2597 / 2000) = -Real.log (2000 / 2597) := by
    rw [show ((2597 / 2000) : ℝ) = ((2000 / 2597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9708_neg : (354534379 / 1000000000) ≤ -Real.log (1403 / 2000) ∧
    -Real.log (1403 / 2000) ≤ (17726719 / 50000000) := by
  have h := checkLog_sound (w := (597 / 3403)) (n := 12)
    (lo := (354534379 / 1000000000)) (hi := (17726719 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1403) = 1/(1403 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9708 : Bounds (-17726719 / 50000000) (-354534379 / 1000000000) (Real.log (1403 / 2000)) := by
  have h := reflection_log_9708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9709_neg : (59691 / 200000000) ≤ -Real.log (2000000 / 2000597) ∧
    -Real.log (2000000 / 2000597) ≤ (37307 / 125000000) := by
  have h := checkLog_sound (w := (597 / 4000597)) (n := 12)
    (lo := (59691 / 200000000)) (hi := (37307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000597 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000597 / 2000000) = 1/(2000000 / 2000597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9709 : Bounds (59691 / 200000000) (37307 / 125000000) (Real.log (2000597 / 2000000)) := by
  have h := reflection_log_9709_neg
  have he : Real.log (2000597 / 2000000) = -Real.log (2000000 / 2000597) := by
    rw [show ((2000597 / 2000000) : ℝ) = ((2000000 / 2000597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9710_neg : (18659 / 62500000) ≤ -Real.log (1999403 / 2000000) ∧
    -Real.log (1999403 / 2000000) ≤ (59709 / 200000000) := by
  have h := checkLog_sound (w := (597 / 3999403)) (n := 12)
    (lo := (18659 / 62500000)) (hi := (59709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999403) = 1/(1999403 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9710 : Bounds (-59709 / 200000000) (-18659 / 62500000) (Real.log (1999403 / 2000000)) := by
  have h := reflection_log_9710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9711_neg : (140895213 / 1000000000) ≤ -Real.log (125000 / 143913) ∧
    -Real.log (125000 / 143913) ≤ (70447607 / 500000000) := by
  have h := checkLog_sound (w := (18913 / 268913)) (n := 12)
    (lo := (140895213 / 1000000000)) (hi := (70447607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143913 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143913 / 125000) = 1/(125000 / 143913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9711 : Bounds (140895213 / 1000000000) (70447607 / 500000000) (Real.log (143913 / 125000)) := by
  have h := reflection_log_9711_neg
  have he : Real.log (143913 / 125000) = -Real.log (125000 / 143913) := by
    rw [show ((143913 / 125000) : ℝ) = ((125000 / 143913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9712_neg : (6562169 / 40000000) ≤ -Real.log (106087 / 125000) ∧
    -Real.log (106087 / 125000) ≤ (82027113 / 500000000) := by
  have h := checkLog_sound (w := (18913 / 231087)) (n := 12)
    (lo := (6562169 / 40000000)) (hi := (82027113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106087) = 1/(106087 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9712 : Bounds (-82027113 / 500000000) (-6562169 / 40000000) (Real.log (106087 / 125000)) := by
  have h := reflection_log_9712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9713_neg : (141378027 / 1000000000) ≤ -Real.log (50000 / 57593) ∧
    -Real.log (50000 / 57593) ≤ (35344507 / 250000000) := by
  have h := checkLog_sound (w := (7593 / 107593)) (n := 12)
    (lo := (141378027 / 1000000000)) (hi := (35344507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57593 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57593 / 50000) = 1/(50000 / 57593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9713 : Bounds (141378027 / 1000000000) (35344507 / 250000000) (Real.log (57593 / 50000)) := by
  have h := reflection_log_9713_neg
  have he : Real.log (57593 / 50000) = -Real.log (50000 / 57593) := by
    rw [show ((57593 / 50000) : ℝ) = ((50000 / 57593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9714_neg : (82354781 / 500000000) ≤ -Real.log (42407 / 50000) ∧
    -Real.log (42407 / 50000) ≤ (164709563 / 1000000000) := by
  have h := checkLog_sound (w := (7593 / 92407)) (n := 12)
    (lo := (82354781 / 500000000)) (hi := (164709563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42407) = 1/(42407 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9714 : Bounds (-164709563 / 1000000000) (-82354781 / 500000000) (Real.log (42407 / 50000)) := by
  have h := reflection_log_9714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9715_neg : (4666307 / 200000000) ≤ -Real.log (2442346351 / 2500000000) ∧
    -Real.log (2442346351 / 2500000000) ≤ (1458221 / 62500000) := by
  have h := checkLog_sound (w := (57653649 / 4942346351)) (n := 12)
    (lo := (4666307 / 200000000)) (hi := (1458221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2442346351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2442346351) = 1/(2442346351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9715 : Bounds (-1458221 / 62500000) (-4666307 / 200000000) (Real.log (2442346351 / 2500000000)) := by
  have h := reflection_log_9715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9716_neg : (5789753 / 250000000) ≤ -Real.log (15267298431 / 15625000000) ∧
    -Real.log (15267298431 / 15625000000) ≤ (23159013 / 1000000000) := by
  have h := checkLog_sound (w := (357701569 / 30892298431)) (n := 12)
    (lo := (5789753 / 250000000)) (hi := (23159013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15267298431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15267298431) = 1/(15267298431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9716 : Bounds (-23159013 / 1000000000) (-5789753 / 250000000) (Real.log (15267298431 / 15625000000)) := by
  have h := reflection_log_9716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9717_neg : (152474719 / 500000000) ≤ -Real.log (500000000000 / 678278205623) ∧
    -Real.log (500000000000 / 678278205623) ≤ (304949439 / 1000000000) := by
  have h := checkLog_sound (w := (178278205623 / 1178278205623)) (n := 12)
    (lo := (152474719 / 500000000)) (hi := (304949439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678278205623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678278205623 / 500000000000) = 1/(500000000000 / 678278205623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9717 : Bounds (152474719 / 500000000) (304949439 / 1000000000) (Real.log (678278205623 / 500000000000)) := by
  have h := reflection_log_9717_neg
  have he : Real.log (678278205623 / 500000000000) = -Real.log (500000000000 / 678278205623) := by
    rw [show ((678278205623 / 500000000000) : ℝ) = ((500000000000 / 678278205623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9718_neg : (306087589 / 1000000000) ≤ -Real.log (250000000000 / 339525314217) ∧
    -Real.log (250000000000 / 339525314217) ≤ (30608759 / 100000000) := by
  have h := checkLog_sound (w := (89525314217 / 589525314217)) (n := 12)
    (lo := (306087589 / 1000000000)) (hi := (30608759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339525314217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339525314217 / 250000000000) = 1/(250000000000 / 339525314217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9718 : Bounds (306087589 / 1000000000) (30608759 / 100000000) (Real.log (339525314217 / 250000000000)) := by
  have h := reflection_log_9718_neg
  have he : Real.log (339525314217 / 250000000000) = -Real.log (250000000000 / 339525314217) := by
    rw [show ((339525314217 / 250000000000) : ℝ) = ((250000000000 / 339525314217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9719_neg : (614646493 / 1000000000) ≤ -Real.log (500000000000 / 924501424501) ∧
    -Real.log (500000000000 / 924501424501) ≤ (307323247 / 500000000) := by
  have h := checkLog_sound (w := (424501424501 / 1424501424501)) (n := 12)
    (lo := (614646493 / 1000000000)) (hi := (307323247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((924501424501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(924501424501 / 500000000000) = 1/(500000000000 / 924501424501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9719 : Bounds (614646493 / 1000000000) (307323247 / 500000000) (Real.log (924501424501 / 500000000000)) := by
  have h := reflection_log_9719_neg
  have he : Real.log (924501424501 / 500000000000) = -Real.log (500000000000 / 924501424501) := by
    rw [show ((924501424501 / 500000000000) : ℝ) = ((500000000000 / 924501424501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9720_neg : (615744131 / 1000000000) ≤ -Real.log (250000000000 / 462758374911) ∧
    -Real.log (250000000000 / 462758374911) ≤ (153936033 / 250000000) := by
  have h := checkLog_sound (w := (212758374911 / 712758374911)) (n := 12)
    (lo := (615744131 / 1000000000)) (hi := (153936033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462758374911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462758374911 / 250000000000) = 1/(250000000000 / 462758374911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9720 : Bounds (615744131 / 1000000000) (153936033 / 250000000) (Real.log (462758374911 / 250000000000)) := by
  have h := reflection_log_9720_neg
  have he : Real.log (462758374911 / 250000000000) = -Real.log (250000000000 / 462758374911) := by
    rw [show ((462758374911 / 250000000000) : ℝ) = ((250000000000 / 462758374911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9721_neg : (261594737 / 1000000000) ≤ -Real.log (1000 / 1299) ∧
    -Real.log (1000 / 1299) ≤ (130797369 / 500000000) := by
  have h := checkLog_sound (w := (299 / 2299)) (n := 12)
    (lo := (261594737 / 1000000000)) (hi := (130797369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1000) = 1/(1000 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9721 : Bounds (261594737 / 1000000000) (130797369 / 500000000) (Real.log (1299 / 1000)) := by
  have h := reflection_log_9721_neg
  have he : Real.log (1299 / 1000) = -Real.log (1000 / 1299) := by
    rw [show ((1299 / 1000) : ℝ) = ((1000 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9722_neg : (355247391 / 1000000000) ≤ -Real.log (701 / 1000) ∧
    -Real.log (701 / 1000) ≤ (11101481 / 31250000) := by
  have h := checkLog_sound (w := (299 / 1701)) (n := 12)
    (lo := (355247391 / 1000000000)) (hi := (11101481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 701) = 1/(701 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9722 : Bounds (-11101481 / 31250000) (-355247391 / 1000000000) (Real.log (701 / 1000)) := by
  have h := reflection_log_9722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9723_neg : (59791 / 200000000) ≤ -Real.log (1000000 / 1000299) ∧
    -Real.log (1000000 / 1000299) ≤ (74739 / 250000000) := by
  have h := checkLog_sound (w := (299 / 2000299)) (n := 12)
    (lo := (59791 / 200000000)) (hi := (74739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000299 / 1000000) = 1/(1000000 / 1000299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9723 : Bounds (59791 / 200000000) (74739 / 250000000) (Real.log (1000299 / 1000000)) := by
  have h := reflection_log_9723_neg
  have he : Real.log (1000299 / 1000000) = -Real.log (1000000 / 1000299) := by
    rw [show ((1000299 / 1000000) : ℝ) = ((1000000 / 1000299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9724_neg : (74761 / 250000000) ≤ -Real.log (999701 / 1000000) ∧
    -Real.log (999701 / 1000000) ≤ (59809 / 200000000) := by
  have h := checkLog_sound (w := (299 / 1999701)) (n := 12)
    (lo := (74761 / 250000000)) (hi := (59809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999701) = 1/(999701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9724 : Bounds (-59809 / 200000000) (-74761 / 250000000) (Real.log (999701 / 1000000)) := by
  have h := reflection_log_9724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9725_neg : (28224551 / 200000000) ≤ -Real.log (500000 / 575783) ∧
    -Real.log (500000 / 575783) ≤ (35280689 / 250000000) := by
  have h := checkLog_sound (w := (75783 / 1075783)) (n := 12)
    (lo := (28224551 / 200000000)) (hi := (35280689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575783 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(575783 / 500000) = 1/(500000 / 575783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9725 : Bounds (28224551 / 200000000) (35280689 / 250000000) (Real.log (575783 / 500000)) := by
  have h := reflection_log_9725_neg
  have he : Real.log (575783 / 500000) = -Real.log (500000 / 575783) := by
    rw [show ((575783 / 500000) : ℝ) = ((500000 / 575783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9726_neg : (164362981 / 1000000000) ≤ -Real.log (424217 / 500000) ∧
    -Real.log (424217 / 500000) ≤ (82181491 / 500000000) := by
  have h := checkLog_sound (w := (75783 / 924217)) (n := 12)
    (lo := (164362981 / 1000000000)) (hi := (82181491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 424217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 424217) = 1/(424217 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9726 : Bounds (-82181491 / 500000000) (-164362981 / 1000000000) (Real.log (424217 / 500000)) := by
  have h := reflection_log_9726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9727_neg : (141606327 / 1000000000) ≤ -Real.log (1000000 / 1152123) ∧
    -Real.log (1000000 / 1152123) ≤ (17700791 / 125000000) := by
  have h := checkLog_sound (w := (152123 / 2152123)) (n := 12)
    (lo := (141606327 / 1000000000)) (hi := (17700791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152123 / 1000000) = 1/(1000000 / 1152123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9727 : Bounds (141606327 / 1000000000) (17700791 / 125000000) (Real.log (1152123 / 1000000)) := by
  have h := reflection_log_9727_neg
  have he : Real.log (1152123 / 1000000) = -Real.log (1000000 / 1152123) := by
    rw [show ((1152123 / 1000000) : ℝ) = ((1000000 / 1152123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
