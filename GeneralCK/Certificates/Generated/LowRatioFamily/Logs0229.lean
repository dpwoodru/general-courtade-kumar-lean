import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14656_neg : (432210237 / 1000000000) ≤ -Real.log (649072903119 / 1000000000000) ∧
    -Real.log (649072903119 / 1000000000000) ≤ (216105119 / 500000000) := by
  have h := checkLog_sound (w := (350927096881 / 1649072903119)) (n := 12)
    (lo := (432210237 / 1000000000)) (hi := (216105119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 649072903119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 649072903119) = 1/(649072903119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14656 : Bounds (-216105119 / 500000000) (-432210237 / 1000000000) (Real.log (649072903119 / 1000000000000)) := by
  have h := reflection_log_14656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14657_neg : (1362683557 / 1000000000) ≤ -Real.log (62500000000 / 244166437689) ∧
    -Real.log (62500000000 / 244166437689) ≤ (1362683559 / 1000000000) := by
  have h := checkLog_sound (w := (119166437689 / 369166437689)) (n := 12)
    (lo := (669536377 / 1000000000)) (hi := (334768189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244166437689 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(244166437689 / 125000000000) = 1/(62500000000 / 244166437689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14657 : Bounds (1362683557 / 1000000000) (1362683559 / 1000000000) (Real.log (244166437689 / 62500000000)) := by
  have h := reflection_log_14657_neg
  have he : Real.log (244166437689 / 62500000000) = -Real.log (62500000000 / 244166437689) := by
    rw [show ((244166437689 / 62500000000) : ℝ) = ((62500000000 / 244166437689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14658_neg : (1368096867 / 1000000000) ≤ -Real.log (3125000000 / 12274588523) ∧
    -Real.log (3125000000 / 12274588523) ≤ (1368096869 / 1000000000) := by
  have h := checkLog_sound (w := (6024588523 / 18524588523)) (n := 12)
    (lo := (674949687 / 1000000000)) (hi := (84368711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12274588523 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12274588523 / 6250000000) = 1/(3125000000 / 12274588523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14658 : Bounds (1368096867 / 1000000000) (1368096869 / 1000000000) (Real.log (12274588523 / 3125000000)) := by
  have h := reflection_log_14658_neg
  have he : Real.log (12274588523 / 3125000000) = -Real.log (3125000000 / 12274588523) := by
    rw [show ((12274588523 / 3125000000) : ℝ) = ((3125000000 / 12274588523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14659_neg : (3684277039 / 1000000000) ≤ -Real.log (500000000000 / 19908163265307) ∧
    -Real.log (500000000000 / 19908163265307) ≤ (736855409 / 200000000) := by
  have h := checkLog_sound (w := (3908163265307 / 35908163265307)) (n := 12)
    (lo := (218541139 / 1000000000)) (hi := (10927057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19908163265307 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19908163265307 / 16000000000000) = 1/(500000000000 / 19908163265307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14659 : Bounds (3684277039 / 1000000000) (736855409 / 200000000) (Real.log (19908163265307 / 500000000000)) := by
  have h := reflection_log_14659_neg
  have he : Real.log (19908163265307 / 500000000000) = -Real.log (500000000000 / 19908163265307) := by
    rw [show ((19908163265307 / 500000000000) : ℝ) = ((500000000000 / 19908163265307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14660_neg : (668854487 / 1000000000) ≤ -Real.log (125 / 244) ∧
    -Real.log (125 / 244) ≤ (83606811 / 125000000) := by
  have h := checkLog_sound (w := (119 / 369)) (n := 12)
    (lo := (668854487 / 1000000000)) (hi := (83606811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244 / 125) = 1/(125 / 244) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14660 : Bounds (668854487 / 1000000000) (83606811 / 125000000) (Real.log (244 / 125)) := by
  have h := reflection_log_14660_neg
  have he : Real.log (244 / 125) = -Real.log (125 / 244) := by
    rw [show ((244 / 125) : ℝ) = ((125 / 244) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14661_neg : (607310853 / 200000000) ≤ -Real.log (6 / 125) ∧
    -Real.log (6 / 125) ≤ (303655427 / 100000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 96) = 1/(6 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14661 : Bounds (-303655427 / 100000000) (-607310853 / 200000000) (Real.log (6 / 125)) := by
  have h := reflection_log_14661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14662_neg : (951547 / 1000000000) ≤ -Real.log (125000 / 125119) ∧
    -Real.log (125000 / 125119) ≤ (237887 / 250000000) := by
  have h := checkLog_sound (w := (119 / 250119)) (n := 12)
    (lo := (951547 / 1000000000)) (hi := (237887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125119 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125119 / 125000) = 1/(125000 / 125119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14662 : Bounds (951547 / 1000000000) (237887 / 250000000) (Real.log (125119 / 125000)) := by
  have h := reflection_log_14662_neg
  have he : Real.log (125119 / 125000) = -Real.log (125000 / 125119) := by
    rw [show ((125119 / 125000) : ℝ) = ((125000 / 125119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14663_neg : (952453 / 1000000000) ≤ -Real.log (124881 / 125000) ∧
    -Real.log (124881 / 125000) ≤ (476227 / 500000000) := by
  have h := checkLog_sound (w := (119 / 249881)) (n := 12)
    (lo := (952453 / 1000000000)) (hi := (476227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124881) = 1/(124881 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14663 : Bounds (-476227 / 500000000) (-952453 / 1000000000) (Real.log (124881 / 125000)) := by
  have h := reflection_log_14663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14664_neg : (465923441 / 1000000000) ≤ -Real.log (200000 / 318697) ∧
    -Real.log (200000 / 318697) ≤ (232961721 / 500000000) := by
  have h := checkLog_sound (w := (118697 / 518697)) (n := 12)
    (lo := (465923441 / 1000000000)) (hi := (232961721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318697 / 200000) = 1/(200000 / 318697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14664 : Bounds (465923441 / 1000000000) (232961721 / 500000000) (Real.log (318697 / 200000)) := by
  have h := reflection_log_14664_neg
  have he : Real.log (318697 / 200000) = -Real.log (200000 / 318697) := by
    rw [show ((318697 / 200000) : ℝ) = ((200000 / 318697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14665_neg : (900134449 / 1000000000) ≤ -Real.log (81303 / 200000) ∧
    -Real.log (81303 / 200000) ≤ (900134451 / 1000000000) := by
  have h := checkLog_sound (w := (18697 / 181303)) (n := 12)
    (lo := (206987269 / 1000000000)) (hi := (20698727 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 81303) = 1/(81303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14665 : Bounds (-900134451 / 1000000000) (-900134449 / 1000000000) (Real.log (81303 / 200000)) := by
  have h := reflection_log_14665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14666_neg : (18681043 / 40000000) ≤ -Real.log (1000000 / 1595243) ∧
    -Real.log (1000000 / 1595243) ≤ (116756519 / 250000000) := by
  have h := checkLog_sound (w := (595243 / 2595243)) (n := 12)
    (lo := (18681043 / 40000000)) (hi := (116756519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1595243 / 1000000) = 1/(1000000 / 1595243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14666 : Bounds (18681043 / 40000000) (116756519 / 250000000) (Real.log (1595243 / 1000000)) := by
  have h := reflection_log_14666_neg
  have he : Real.log (1595243 / 1000000) = -Real.log (1000000 / 1595243) := by
    rw [show ((1595243 / 1000000) : ℝ) = ((1000000 / 1595243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14667_neg : (904468391 / 1000000000) ≤ -Real.log (404757 / 1000000) ∧
    -Real.log (404757 / 1000000) ≤ (904468393 / 1000000000) := by
  have h := checkLog_sound (w := (95243 / 904757)) (n := 12)
    (lo := (211321211 / 1000000000)) (hi := (52830303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 404757) = 1/(404757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14667 : Bounds (-904468393 / 1000000000) (-904468391 / 1000000000) (Real.log (404757 / 1000000)) := by
  have h := reflection_log_14667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14668_neg : (109360579 / 250000000) ≤ -Real.log (645685770951 / 1000000000000) ∧
    -Real.log (645685770951 / 1000000000000) ≤ (437442317 / 1000000000) := by
  have h := checkLog_sound (w := (354314229049 / 1645685770951)) (n := 12)
    (lo := (109360579 / 250000000)) (hi := (437442317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 645685770951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 645685770951) = 1/(645685770951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14668 : Bounds (-437442317 / 1000000000) (-109360579 / 250000000) (Real.log (645685770951 / 1000000000000)) := by
  have h := reflection_log_14668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14669_neg : (6784547 / 15625000) ≤ -Real.log (25911022191 / 40000000000) ∧
    -Real.log (25911022191 / 40000000000) ≤ (434211009 / 1000000000) := by
  have h := checkLog_sound (w := (14088977809 / 65911022191)) (n := 12)
    (lo := (6784547 / 15625000)) (hi := (434211009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25911022191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25911022191) = 1/(25911022191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14669 : Bounds (-434211009 / 1000000000) (-6784547 / 15625000) (Real.log (25911022191 / 40000000000)) := by
  have h := reflection_log_14669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14670_neg : (1366057891 / 1000000000) ≤ -Real.log (25000000000 / 97996691389) ∧
    -Real.log (25000000000 / 97996691389) ≤ (1366057893 / 1000000000) := by
  have h := checkLog_sound (w := (47996691389 / 147996691389)) (n := 12)
    (lo := (672910711 / 1000000000)) (hi := (84113839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97996691389 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(97996691389 / 50000000000) = 1/(25000000000 / 97996691389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14670 : Bounds (1366057891 / 1000000000) (1366057893 / 1000000000) (Real.log (97996691389 / 25000000000)) := by
  have h := reflection_log_14670_neg
  have he : Real.log (97996691389 / 25000000000) = -Real.log (25000000000 / 97996691389) := by
    rw [show ((97996691389 / 25000000000) : ℝ) = ((25000000000 / 97996691389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14671_neg : (1371494467 / 1000000000) ≤ -Real.log (250000000000 / 985309086687) ∧
    -Real.log (250000000000 / 985309086687) ≤ (1371494469 / 1000000000) := by
  have h := checkLog_sound (w := (485309086687 / 1485309086687)) (n := 12)
    (lo := (678347287 / 1000000000)) (hi := (84793411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985309086687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(985309086687 / 500000000000) = 1/(250000000000 / 985309086687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14671 : Bounds (1371494467 / 1000000000) (1371494469 / 1000000000) (Real.log (985309086687 / 250000000000)) := by
  have h := reflection_log_14671_neg
  have he : Real.log (985309086687 / 250000000000) = -Real.log (250000000000 / 985309086687) := by
    rw [show ((985309086687 / 250000000000) : ℝ) = ((250000000000 / 985309086687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14672_neg : (3684277039 / 1000000000) ≤ -Real.log (250000000000 / 9954081632653) ∧
    -Real.log (250000000000 / 9954081632653) ≤ (736855409 / 200000000) := by
  have h := checkLog_sound (w := (1954081632653 / 17954081632653)) (n := 12)
    (lo := (218541139 / 1000000000)) (hi := (10927057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9954081632653 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9954081632653 / 8000000000000) = 1/(250000000000 / 9954081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14672 : Bounds (3684277039 / 1000000000) (736855409 / 200000000) (Real.log (9954081632653 / 250000000000)) := by
  have h := reflection_log_14672_neg
  have he : Real.log (9954081632653 / 250000000000) = -Real.log (250000000000 / 9954081632653) := by
    rw [show ((9954081632653 / 250000000000) : ℝ) = ((250000000000 / 9954081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14673_neg : (3705408753 / 1000000000) ≤ -Real.log (250000000000 / 10166666666667) ∧
    -Real.log (250000000000 / 10166666666667) ≤ (3705408759 / 1000000000) := by
  have h := checkLog_sound (w := (2166666666667 / 18166666666667)) (n := 12)
    (lo := (239672853 / 1000000000)) (hi := (119836427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10166666666667 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10166666666667 / 8000000000000) = 1/(250000000000 / 10166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14673 : Bounds (3705408753 / 1000000000) (3705408759 / 1000000000) (Real.log (10166666666667 / 250000000000)) := by
  have h := reflection_log_14673_neg
  have he : Real.log (10166666666667 / 250000000000) = -Real.log (250000000000 / 10166666666667) := by
    rw [show ((10166666666667 / 250000000000) : ℝ) = ((250000000000 / 10166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14674_neg : (669366651 / 1000000000) ≤ -Real.log (1000 / 1953) ∧
    -Real.log (1000 / 1953) ≤ (167341663 / 250000000) := by
  have h := checkLog_sound (w := (953 / 2953)) (n := 12)
    (lo := (669366651 / 1000000000)) (hi := (167341663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953 / 1000) = 1/(1000 / 1953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14674 : Bounds (669366651 / 1000000000) (167341663 / 250000000) (Real.log (1953 / 1000)) := by
  have h := reflection_log_14674_neg
  have he : Real.log (1953 / 1000) = -Real.log (1000 / 1953) := by
    rw [show ((1953 / 1000) : ℝ) = ((1000 / 1953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14675_neg : (122304307 / 40000000) ≤ -Real.log (47 / 1000) ∧
    -Real.log (47 / 1000) ≤ (1194378 / 390625) := by
  have h := checkLog_sound (w := (31 / 219)) (n := 12)
    (lo := (57003791 / 200000000)) (hi := (71254739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 94) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 94) = 1/(47 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14675 : Bounds (-1194378 / 390625) (-122304307 / 40000000) (Real.log (47 / 1000)) := by
  have h := reflection_log_14675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14676_neg : (476273 / 500000000) ≤ -Real.log (1000000 / 1000953) ∧
    -Real.log (1000000 / 1000953) ≤ (952547 / 1000000000) := by
  have h := checkLog_sound (w := (953 / 2000953)) (n := 12)
    (lo := (476273 / 500000000)) (hi := (952547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000953 / 1000000) = 1/(1000000 / 1000953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14676 : Bounds (476273 / 500000000) (952547 / 1000000000) (Real.log (1000953 / 1000000)) := by
  have h := reflection_log_14676_neg
  have he : Real.log (1000953 / 1000000) = -Real.log (1000000 / 1000953) := by
    rw [show ((1000953 / 1000000) : ℝ) = ((1000000 / 1000953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14677_neg : (476727 / 500000000) ≤ -Real.log (999047 / 1000000) ∧
    -Real.log (999047 / 1000000) ≤ (190691 / 200000000) := by
  have h := checkLog_sound (w := (953 / 1999047)) (n := 12)
    (lo := (476727 / 500000000)) (hi := (190691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999047) = 1/(999047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14677 : Bounds (-190691 / 200000000) (-476727 / 500000000) (Real.log (999047 / 1000000)) := by
  have h := reflection_log_14677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14678_neg : (466612887 / 1000000000) ≤ -Real.log (125000 / 199323) ∧
    -Real.log (125000 / 199323) ≤ (58326611 / 125000000) := by
  have h := checkLog_sound (w := (74323 / 324323)) (n := 12)
    (lo := (466612887 / 1000000000)) (hi := (58326611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199323 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199323 / 125000) = 1/(125000 / 199323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14678 : Bounds (466612887 / 1000000000) (58326611 / 125000000) (Real.log (199323 / 125000)) := by
  have h := reflection_log_14678_neg
  have he : Real.log (199323 / 125000) = -Real.log (125000 / 199323) := by
    rw [show ((199323 / 125000) : ℝ) = ((125000 / 199323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14679_neg : (902841577 / 1000000000) ≤ -Real.log (50677 / 125000) ∧
    -Real.log (50677 / 125000) ≤ (902841579 / 1000000000) := by
  have h := checkLog_sound (w := (11823 / 113177)) (n := 12)
    (lo := (209694397 / 1000000000)) (hi := (104847199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50677) = 1/(50677 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14679 : Bounds (-902841579 / 1000000000) (-902841577 / 1000000000) (Real.log (50677 / 125000)) := by
  have h := reflection_log_14679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14680_neg : (467717267 / 1000000000) ≤ -Real.log (500000 / 798173) ∧
    -Real.log (500000 / 798173) ≤ (116929317 / 250000000) := by
  have h := checkLog_sound (w := (298173 / 1298173)) (n := 12)
    (lo := (467717267 / 1000000000)) (hi := (116929317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798173 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798173 / 500000) = 1/(500000 / 798173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14680 : Bounds (467717267 / 1000000000) (116929317 / 250000000) (Real.log (798173 / 500000)) := by
  have h := reflection_log_14680_neg
  have he : Real.log (798173 / 500000) = -Real.log (500000 / 798173) := by
    rw [show ((798173 / 500000) : ℝ) = ((500000 / 798173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14681_neg : (907197203 / 1000000000) ≤ -Real.log (201827 / 500000) ∧
    -Real.log (201827 / 500000) ≤ (181439441 / 200000000) := by
  have h := checkLog_sound (w := (48173 / 451827)) (n := 12)
    (lo := (214050023 / 1000000000)) (hi := (26756253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201827) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 201827) = 1/(201827 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14681 : Bounds (-181439441 / 200000000) (-907197203 / 1000000000) (Real.log (201827 / 500000)) := by
  have h := reflection_log_14681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14682_neg : (3433437 / 7812500) ≤ -Real.log (161092862071 / 250000000000) ∧
    -Real.log (161092862071 / 250000000000) ≤ (439479937 / 1000000000) := by
  have h := checkLog_sound (w := (88907137929 / 411092862071)) (n := 12)
    (lo := (3433437 / 7812500)) (hi := (439479937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 161092862071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 161092862071) = 1/(161092862071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14682 : Bounds (-439479937 / 1000000000) (-3433437 / 7812500) (Real.log (161092862071 / 250000000000)) := by
  have h := reflection_log_14682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14683_neg : (436228691 / 1000000000) ≤ -Real.log (10101091671 / 15625000000) ∧
    -Real.log (10101091671 / 15625000000) ≤ (109057173 / 250000000) := by
  have h := checkLog_sound (w := (5523908329 / 25726091671)) (n := 12)
    (lo := (436228691 / 1000000000)) (hi := (109057173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10101091671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10101091671) = 1/(10101091671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14683 : Bounds (-109057173 / 250000000) (-436228691 / 1000000000) (Real.log (10101091671 / 15625000000)) := by
  have h := reflection_log_14683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14684_neg : (273890893 / 200000000) ≤ -Real.log (500000000000 / 1966602206129) ∧
    -Real.log (500000000000 / 1966602206129) ≤ (1369454467 / 1000000000) := by
  have h := checkLog_sound (w := (966602206129 / 2966602206129)) (n := 12)
    (lo := (135261457 / 200000000)) (hi := (338153643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966602206129 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1966602206129 / 1000000000000) = 1/(500000000000 / 1966602206129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14684 : Bounds (273890893 / 200000000) (1369454467 / 1000000000) (Real.log (1966602206129 / 500000000000)) := by
  have h := reflection_log_14684_neg
  have he : Real.log (1966602206129 / 500000000000) = -Real.log (500000000000 / 1966602206129) := by
    rw [show ((1966602206129 / 500000000000) : ℝ) = ((500000000000 / 1966602206129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14685_neg : (137491447 / 100000000) ≤ -Real.log (250000000000 / 988684616033) ∧
    -Real.log (250000000000 / 988684616033) ≤ (171864309 / 125000000) := by
  have h := checkLog_sound (w := (488684616033 / 1488684616033)) (n := 12)
    (lo := (68176729 / 100000000)) (hi := (681767291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988684616033 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(988684616033 / 500000000000) = 1/(250000000000 / 988684616033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14685 : Bounds (137491447 / 100000000) (171864309 / 125000000) (Real.log (988684616033 / 250000000000)) := by
  have h := reflection_log_14685_neg
  have he : Real.log (988684616033 / 250000000000) = -Real.log (250000000000 / 988684616033) := by
    rw [show ((988684616033 / 250000000000) : ℝ) = ((250000000000 / 988684616033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14686_neg : (3705408753 / 1000000000) ≤ -Real.log (500000000000 / 20333333333333) ∧
    -Real.log (500000000000 / 20333333333333) ≤ (3705408759 / 1000000000) := by
  have h := checkLog_sound (w := (4333333333333 / 36333333333333)) (n := 12)
    (lo := (239672853 / 1000000000)) (hi := (119836427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20333333333333 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20333333333333 / 16000000000000) = 1/(500000000000 / 20333333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14686 : Bounds (3705408753 / 1000000000) (3705408759 / 1000000000) (Real.log (20333333333333 / 500000000000)) := by
  have h := reflection_log_14686_neg
  have he : Real.log (20333333333333 / 500000000000) = -Real.log (500000000000 / 20333333333333) := by
    rw [show ((20333333333333 / 500000000000) : ℝ) = ((500000000000 / 20333333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14687_neg : (1863487163 / 500000000) ≤ -Real.log (500000000000 / 20776595744681) ∧
    -Real.log (500000000000 / 20776595744681) ≤ (931743583 / 250000000) := by
  have h := checkLog_sound (w := (4776595744681 / 36776595744681)) (n := 12)
    (lo := (130619213 / 500000000)) (hi := (261238427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20776595744681 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20776595744681 / 16000000000000) = 1/(500000000000 / 20776595744681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14687 : Bounds (1863487163 / 500000000) (931743583 / 250000000) (Real.log (20776595744681 / 500000000000)) := by
  have h := reflection_log_14687_neg
  have he : Real.log (20776595744681 / 500000000000) = -Real.log (500000000000 / 20776595744681) := by
    rw [show ((20776595744681 / 500000000000) : ℝ) = ((500000000000 / 20776595744681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14688_neg : (669878553 / 1000000000) ≤ -Real.log (500 / 977) ∧
    -Real.log (500 / 977) ≤ (334939277 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1477)) (n := 12)
    (lo := (669878553 / 1000000000)) (hi := (334939277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 500) = 1/(500 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14688 : Bounds (669878553 / 1000000000) (334939277 / 500000000) (Real.log (977 / 500)) := by
  have h := reflection_log_14688_neg
  have he : Real.log (977 / 500) = -Real.log (500 / 977) := by
    rw [show ((977 / 500) : ℝ) = ((500 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14689_neg : (76977847 / 25000000) ≤ -Real.log (23 / 500) ∧
    -Real.log (23 / 500) ≤ (615822777 / 200000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 92) = 1/(23 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14689 : Bounds (-615822777 / 200000000) (-76977847 / 25000000) (Real.log (23 / 500)) := by
  have h := reflection_log_14689_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14690_neg : (190709 / 200000000) ≤ -Real.log (500000 / 500477) ∧
    -Real.log (500000 / 500477) ≤ (476773 / 500000000) := by
  have h := checkLog_sound (w := (477 / 1000477)) (n := 12)
    (lo := (190709 / 200000000)) (hi := (476773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500477 / 500000) = 1/(500000 / 500477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14690 : Bounds (190709 / 200000000) (476773 / 500000000) (Real.log (500477 / 500000)) := by
  have h := reflection_log_14690_neg
  have he : Real.log (500477 / 500000) = -Real.log (500000 / 500477) := by
    rw [show ((500477 / 500000) : ℝ) = ((500000 / 500477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14691_neg : (190891 / 200000000) ≤ -Real.log (499523 / 500000) ∧
    -Real.log (499523 / 500000) ≤ (119307 / 125000000) := by
  have h := checkLog_sound (w := (477 / 999523)) (n := 12)
    (lo := (190891 / 200000000)) (hi := (119307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499523) = 1/(499523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14691 : Bounds (-119307 / 125000000) (-190891 / 200000000) (Real.log (499523 / 500000)) := by
  have h := reflection_log_14691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14692_neg : (467304991 / 1000000000) ≤ -Real.log (125000 / 199461) ∧
    -Real.log (125000 / 199461) ≤ (14603281 / 31250000) := by
  have h := checkLog_sound (w := (74461 / 324461)) (n := 12)
    (lo := (467304991 / 1000000000)) (hi := (14603281 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199461 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199461 / 125000) = 1/(125000 / 199461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14692 : Bounds (467304991 / 1000000000) (14603281 / 31250000) (Real.log (199461 / 125000)) := by
  have h := reflection_log_14692_neg
  have he : Real.log (199461 / 125000) = -Real.log (125000 / 199461) := by
    rw [show ((199461 / 125000) : ℝ) = ((125000 / 199461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14693_neg : (905568421 / 1000000000) ≤ -Real.log (50539 / 125000) ∧
    -Real.log (50539 / 125000) ≤ (905568423 / 1000000000) := by
  have h := checkLog_sound (w := (11961 / 113039)) (n := 12)
    (lo := (212421241 / 1000000000)) (hi := (106210621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50539) = 1/(50539 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14693 : Bounds (-905568423 / 1000000000) (-905568421 / 1000000000) (Real.log (50539 / 125000)) := by
  have h := reflection_log_14693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14694_neg : (468411111 / 1000000000) ≤ -Real.log (500000 / 798727) ∧
    -Real.log (500000 / 798727) ≤ (58551389 / 125000000) := by
  have h := checkLog_sound (w := (298727 / 1298727)) (n := 12)
    (lo := (468411111 / 1000000000)) (hi := (58551389 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798727 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798727 / 500000) = 1/(500000 / 798727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14694 : Bounds (468411111 / 1000000000) (58551389 / 125000000) (Real.log (798727 / 500000)) := by
  have h := reflection_log_14694_neg
  have he : Real.log (798727 / 500000) = -Real.log (500000 / 798727) := by
    rw [show ((798727 / 500000) : ℝ) = ((500000 / 798727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14695_neg : (454972951 / 500000000) ≤ -Real.log (201273 / 500000) ∧
    -Real.log (201273 / 500000) ≤ (56871619 / 62500000) := by
  have h := checkLog_sound (w := (48727 / 451273)) (n := 12)
    (lo := (108399361 / 500000000)) (hi := (216798723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 201273) = 1/(201273 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14695 : Bounds (-56871619 / 62500000) (-454972951 / 500000000) (Real.log (201273 / 500000)) := by
  have h := reflection_log_14695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14696_neg : (441534791 / 1000000000) ≤ -Real.log (160762179471 / 250000000000) ∧
    -Real.log (160762179471 / 250000000000) ≤ (55191849 / 125000000) := by
  have h := checkLog_sound (w := (89237820529 / 410762179471)) (n := 12)
    (lo := (441534791 / 1000000000)) (hi := (55191849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 160762179471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 160762179471) = 1/(160762179471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14696 : Bounds (-55191849 / 125000000) (-441534791 / 1000000000) (Real.log (160762179471 / 250000000000)) := by
  have h := reflection_log_14696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14697_neg : (43826343 / 100000000) ≤ -Real.log (10080559479 / 15625000000) ∧
    -Real.log (10080559479 / 15625000000) ≤ (438263431 / 1000000000) := by
  have h := checkLog_sound (w := (5544440521 / 25705559479)) (n := 12)
    (lo := (43826343 / 100000000)) (hi := (438263431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10080559479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10080559479) = 1/(10080559479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14697 : Bounds (-438263431 / 1000000000) (-43826343 / 100000000) (Real.log (10080559479 / 15625000000)) := by
  have h := reflection_log_14697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14698_neg : (343218353 / 250000000) ≤ -Real.log (62500000000 / 246667177823) ∧
    -Real.log (62500000000 / 246667177823) ≤ (686436707 / 500000000) := by
  have h := checkLog_sound (w := (121667177823 / 371667177823)) (n := 12)
    (lo := (84965779 / 125000000)) (hi := (679726233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246667177823 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(246667177823 / 125000000000) = 1/(62500000000 / 246667177823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14698 : Bounds (343218353 / 250000000) (686436707 / 500000000) (Real.log (246667177823 / 62500000000)) := by
  have h := reflection_log_14698_neg
  have he : Real.log (246667177823 / 62500000000) = -Real.log (62500000000 / 246667177823) := by
    rw [show ((246667177823 / 62500000000) : ℝ) = ((62500000000 / 246667177823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14699_neg : (689178507 / 500000000) ≤ -Real.log (250000000000 / 992094071237) ∧
    -Real.log (250000000000 / 992094071237) ≤ (172294627 / 125000000) := by
  have h := checkLog_sound (w := (492094071237 / 1492094071237)) (n := 12)
    (lo := (342604917 / 500000000)) (hi := (137041967 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((992094071237 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(992094071237 / 500000000000) = 1/(250000000000 / 992094071237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14699 : Bounds (689178507 / 500000000) (172294627 / 125000000) (Real.log (992094071237 / 250000000000)) := by
  have h := reflection_log_14699_neg
  have he : Real.log (992094071237 / 250000000000) = -Real.log (250000000000 / 992094071237) := by
    rw [show ((992094071237 / 250000000000) : ℝ) = ((250000000000 / 992094071237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14700_neg : (1863487163 / 500000000) ≤ -Real.log (12500000000 / 519414893617) ∧
    -Real.log (12500000000 / 519414893617) ≤ (931743583 / 250000000) := by
  have h := checkLog_sound (w := (119414893617 / 919414893617)) (n := 12)
    (lo := (130619213 / 500000000)) (hi := (261238427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519414893617 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(519414893617 / 400000000000) = 1/(12500000000 / 519414893617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14700 : Bounds (1863487163 / 500000000) (931743583 / 250000000) (Real.log (519414893617 / 12500000000)) := by
  have h := reflection_log_14700_neg
  have he : Real.log (519414893617 / 12500000000) = -Real.log (12500000000 / 519414893617) := by
    rw [show ((519414893617 / 12500000000) : ℝ) = ((12500000000 / 519414893617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14701_neg : (3748992433 / 1000000000) ≤ -Real.log (500000000000 / 21239130434783) ∧
    -Real.log (500000000000 / 21239130434783) ≤ (3748992439 / 1000000000) := by
  have h := checkLog_sound (w := (5239130434783 / 37239130434783)) (n := 12)
    (lo := (283256533 / 1000000000)) (hi := (141628267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21239130434783 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21239130434783 / 16000000000000) = 1/(500000000000 / 21239130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14701 : Bounds (3748992433 / 1000000000) (3748992439 / 1000000000) (Real.log (21239130434783 / 500000000000)) := by
  have h := reflection_log_14701_neg
  have he : Real.log (21239130434783 / 500000000000) = -Real.log (500000000000 / 21239130434783) := by
    rw [show ((21239130434783 / 500000000000) : ℝ) = ((500000000000 / 21239130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14702_neg : (670390193 / 1000000000) ≤ -Real.log (200 / 391) ∧
    -Real.log (200 / 391) ≤ (335195097 / 500000000) := by
  have h := checkLog_sound (w := (191 / 591)) (n := 12)
    (lo := (670390193 / 1000000000)) (hi := (335195097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391 / 200) = 1/(200 / 391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14702 : Bounds (670390193 / 1000000000) (335195097 / 500000000) (Real.log (391 / 200)) := by
  have h := reflection_log_14702_neg
  have he : Real.log (391 / 200) = -Real.log (200 / 391) := by
    rw [show ((391 / 200) : ℝ) = ((200 / 391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14703_neg : (1550546393 / 500000000) ≤ -Real.log (9 / 200) ∧
    -Real.log (9 / 200) ≤ (3101092791 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 43)) (n := 12)
    (lo := (164252033 / 500000000)) (hi := (328504067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 18) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 18) = 1/(9 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14703 : Bounds (-3101092791 / 1000000000) (-1550546393 / 500000000) (Real.log (9 / 200)) := by
  have h := reflection_log_14703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14704_neg : (59659 / 62500000) ≤ -Real.log (200000 / 200191) ∧
    -Real.log (200000 / 200191) ≤ (190909 / 200000000) := by
  have h := checkLog_sound (w := (191 / 400191)) (n := 12)
    (lo := (59659 / 62500000)) (hi := (190909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200191 / 200000) = 1/(200000 / 200191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14704 : Bounds (59659 / 62500000) (190909 / 200000000) (Real.log (200191 / 200000)) := by
  have h := reflection_log_14704_neg
  have he : Real.log (200191 / 200000) = -Real.log (200000 / 200191) := by
    rw [show ((200191 / 200000) : ℝ) = ((200000 / 200191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14705_neg : (14929 / 15625000) ≤ -Real.log (199809 / 200000) ∧
    -Real.log (199809 / 200000) ≤ (955457 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 399809)) (n := 12)
    (lo := (14929 / 15625000)) (hi := (955457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199809) = 1/(199809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14705 : Bounds (-955457 / 1000000000) (-14929 / 15625000) (Real.log (199809 / 200000)) := by
  have h := reflection_log_14705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14706_neg : (467999747 / 1000000000) ≤ -Real.log (1000000 / 1596797) ∧
    -Real.log (1000000 / 1596797) ≤ (116999937 / 250000000) := by
  have h := checkLog_sound (w := (596797 / 2596797)) (n := 12)
    (lo := (467999747 / 1000000000)) (hi := (116999937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1596797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1596797 / 1000000) = 1/(1000000 / 1596797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14706 : Bounds (467999747 / 1000000000) (116999937 / 250000000) (Real.log (1596797 / 1000000)) := by
  have h := reflection_log_14706_neg
  have he : Real.log (1596797 / 1000000) = -Real.log (1000000 / 1596797) := by
    rw [show ((1596797 / 1000000) : ℝ) = ((1000000 / 1596797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14707_neg : (908315121 / 1000000000) ≤ -Real.log (403203 / 1000000) ∧
    -Real.log (403203 / 1000000) ≤ (908315123 / 1000000000) := by
  have h := checkLog_sound (w := (96797 / 903203)) (n := 12)
    (lo := (215167941 / 1000000000)) (hi := (107583971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 403203) = 1/(403203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14707 : Bounds (-908315123 / 1000000000) (-908315121 / 1000000000) (Real.log (403203 / 1000000)) := by
  have h := reflection_log_14707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14708_neg : (117277057 / 250000000) ≤ -Real.log (125000 / 199821) ∧
    -Real.log (125000 / 199821) ≤ (469108229 / 1000000000) := by
  have h := checkLog_sound (w := (74821 / 324821)) (n := 12)
    (lo := (117277057 / 250000000)) (hi := (469108229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199821 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199821 / 125000) = 1/(125000 / 199821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14708 : Bounds (117277057 / 250000000) (469108229 / 1000000000) (Real.log (199821 / 125000)) := by
  have h := reflection_log_14708_neg
  have he : Real.log (199821 / 125000) = -Real.log (125000 / 199821) := by
    rw [show ((199821 / 125000) : ℝ) = ((125000 / 199821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14709_neg : (228179281 / 250000000) ≤ -Real.log (50179 / 125000) ∧
    -Real.log (50179 / 125000) ≤ (456358563 / 500000000) := by
  have h := checkLog_sound (w := (12321 / 112679)) (n := 12)
    (lo := (27446243 / 125000000)) (hi := (43913989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50179) = 1/(50179 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14709 : Bounds (-456358563 / 500000000) (-228179281 / 250000000) (Real.log (50179 / 125000)) := by
  have h := reflection_log_14709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14710_neg : (6931389 / 15625000) ≤ -Real.log (10026817959 / 15625000000) ∧
    -Real.log (10026817959 / 15625000000) ≤ (443608897 / 1000000000) := by
  have h := checkLog_sound (w := (5598182041 / 25651817959)) (n := 12)
    (lo := (6931389 / 15625000)) (hi := (443608897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10026817959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10026817959) = 1/(10026817959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14710 : Bounds (-443608897 / 1000000000) (-6931389 / 15625000) (Real.log (10026817959 / 15625000000)) := by
  have h := reflection_log_14710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14711_neg : (440315373 / 1000000000) ≤ -Real.log (643833340791 / 1000000000000) ∧
    -Real.log (643833340791 / 1000000000000) ≤ (220157687 / 500000000) := by
  have h := checkLog_sound (w := (356166659209 / 1643833340791)) (n := 12)
    (lo := (440315373 / 1000000000)) (hi := (220157687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 643833340791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 643833340791) = 1/(643833340791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14711 : Bounds (-220157687 / 500000000) (-440315373 / 1000000000) (Real.log (643833340791 / 1000000000000)) := by
  have h := reflection_log_14711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14712_neg : (1376314869 / 1000000000) ≤ -Real.log (250000000000 / 990070138367) ∧
    -Real.log (250000000000 / 990070138367) ≤ (1376314871 / 1000000000) := by
  have h := checkLog_sound (w := (490070138367 / 1490070138367)) (n := 12)
    (lo := (683167689 / 1000000000)) (hi := (68316769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990070138367 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(990070138367 / 500000000000) = 1/(250000000000 / 990070138367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14712 : Bounds (1376314869 / 1000000000) (1376314871 / 1000000000) (Real.log (990070138367 / 250000000000)) := by
  have h := reflection_log_14712_neg
  have he : Real.log (990070138367 / 250000000000) = -Real.log (250000000000 / 990070138367) := by
    rw [show ((990070138367 / 250000000000) : ℝ) = ((250000000000 / 990070138367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14713_neg : (172728169 / 125000000) ≤ -Real.log (500000000000 / 1991081926703) ∧
    -Real.log (500000000000 / 1991081926703) ≤ (690912677 / 500000000) := by
  have h := checkLog_sound (w := (991081926703 / 2991081926703)) (n := 12)
    (lo := (172169543 / 250000000)) (hi := (688678173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1991081926703 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1991081926703 / 1000000000000) = 1/(500000000000 / 1991081926703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14713 : Bounds (172728169 / 125000000) (690912677 / 500000000) (Real.log (1991081926703 / 500000000000)) := by
  have h := reflection_log_14713_neg
  have he : Real.log (1991081926703 / 500000000000) = -Real.log (500000000000 / 1991081926703) := by
    rw [show ((1991081926703 / 500000000000) : ℝ) = ((500000000000 / 1991081926703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14714_neg : (3748992433 / 1000000000) ≤ -Real.log (250000000000 / 10619565217391) ∧
    -Real.log (250000000000 / 10619565217391) ≤ (3748992439 / 1000000000) := by
  have h := checkLog_sound (w := (2619565217391 / 18619565217391)) (n := 12)
    (lo := (283256533 / 1000000000)) (hi := (141628267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10619565217391 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10619565217391 / 8000000000000) = 1/(250000000000 / 10619565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14714 : Bounds (3748992433 / 1000000000) (3748992439 / 1000000000) (Real.log (10619565217391 / 250000000000)) := by
  have h := reflection_log_14714_neg
  have he : Real.log (10619565217391 / 250000000000) = -Real.log (250000000000 / 10619565217391) := by
    rw [show ((10619565217391 / 250000000000) : ℝ) = ((250000000000 / 10619565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14715_neg : (3771482979 / 1000000000) ≤ -Real.log (500000000000 / 21722222222223) ∧
    -Real.log (500000000000 / 21722222222223) ≤ (754296597 / 200000000) := by
  have h := checkLog_sound (w := (5722222222223 / 37722222222223)) (n := 12)
    (lo := (305747079 / 1000000000)) (hi := (7643677 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21722222222223 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21722222222223 / 16000000000000) = 1/(500000000000 / 21722222222223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14715 : Bounds (3771482979 / 1000000000) (754296597 / 200000000) (Real.log (21722222222223 / 500000000000)) := by
  have h := reflection_log_14715_neg
  have he : Real.log (21722222222223 / 500000000000) = -Real.log (500000000000 / 21722222222223) := by
    rw [show ((21722222222223 / 500000000000) : ℝ) = ((500000000000 / 21722222222223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14716_neg : (670901571 / 1000000000) ≤ -Real.log (250 / 489) ∧
    -Real.log (250 / 489) ≤ (167725393 / 250000000) := by
  have h := checkLog_sound (w := (239 / 739)) (n := 12)
    (lo := (670901571 / 1000000000)) (hi := (167725393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489 / 250) = 1/(250 / 489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14716 : Bounds (670901571 / 1000000000) (167725393 / 250000000) (Real.log (489 / 250)) := by
  have h := reflection_log_14716_neg
  have he : Real.log (489 / 250) = -Real.log (250 / 489) := by
    rw [show ((489 / 250) : ℝ) = ((250 / 489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14717_neg : (1561782821 / 500000000) ≤ -Real.log (11 / 250) ∧
    -Real.log (11 / 250) ≤ (3123565647 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 88) = 1/(11 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14717 : Bounds (-3123565647 / 1000000000) (-1561782821 / 500000000) (Real.log (11 / 250)) := by
  have h := reflection_log_14717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14718_neg : (955543 / 1000000000) ≤ -Real.log (250000 / 250239) ∧
    -Real.log (250000 / 250239) ≤ (119443 / 125000000) := by
  have h := checkLog_sound (w := (239 / 500239)) (n := 12)
    (lo := (955543 / 1000000000)) (hi := (119443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250239 / 250000) = 1/(250000 / 250239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14718 : Bounds (955543 / 1000000000) (119443 / 125000000) (Real.log (250239 / 250000)) := by
  have h := reflection_log_14718_neg
  have he : Real.log (250239 / 250000) = -Real.log (250000 / 250239) := by
    rw [show ((250239 / 250000) : ℝ) = ((250000 / 250239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14719_neg : (956457 / 1000000000) ≤ -Real.log (249761 / 250000) ∧
    -Real.log (249761 / 250000) ≤ (478229 / 500000000) := by
  have h := checkLog_sound (w := (239 / 499761)) (n := 12)
    (lo := (956457 / 1000000000)) (hi := (478229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249761) = 1/(249761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14719 : Bounds (-478229 / 500000000) (-956457 / 1000000000) (Real.log (249761 / 250000)) := by
  have h := reflection_log_14719_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
