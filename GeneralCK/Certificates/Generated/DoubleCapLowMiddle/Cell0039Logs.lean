import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039
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

theorem reflection_log_1_neg : (340046801 / 500000000) ≤ -Real.log (3200 / 6317) ∧
    -Real.log (3200 / 6317) ≤ (680093603 / 1000000000) := by
  have h := checkLog_sound (w := (3117 / 9517)) (n := 12)
    (lo := (340046801 / 500000000)) (hi := (680093603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6317 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6317 / 3200) = 1/(3200 / 6317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (340046801 / 500000000) (680093603 / 1000000000) (Real.log (6317 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6317 / 3200) = -Real.log (3200 / 6317) := by
    rw [show ((6317 / 3200) : ℝ) = ((3200 / 6317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1826032739 / 500000000) ≤ -Real.log (83 / 3200) ∧
    -Real.log (83 / 3200) ≤ (913016371 / 250000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(100 / 83) = 1/(83 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-913016371 / 250000000) (-1826032739 / 500000000) (Real.log (83 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135999921 / 200000000) ≤ -Real.log (4096 / 8085) ∧
    -Real.log (4096 / 8085) ≤ (339999803 / 500000000) := by
  have h := checkLog_sound (w := (3989 / 12181)) (n := 12)
    (lo := (135999921 / 200000000)) (hi := (339999803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8085 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8085 / 4096) = 1/(4096 / 8085) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (135999921 / 200000000) (339999803 / 500000000) (Real.log (8085 / 4096)) := by
  have h := reflection_log_3_neg
  have he : Real.log (8085 / 4096) = -Real.log (4096 / 8085) := by
    rw [show ((8085 / 4096) : ℝ) = ((4096 / 8085) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3644937329 / 1000000000) ≤ -Real.log (107 / 4096) ∧
    -Real.log (107 / 4096) ≤ (728987467 / 200000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(128 / 107) = 1/(107 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) (Real.log (107 / 4096)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (666867371 / 1000000000) ≤ -Real.log (1600 / 3117) ∧
    -Real.log (1600 / 3117) ≤ (166716843 / 250000000) := by
  have h := checkLog_sound (w := (1517 / 4717)) (n := 12)
    (lo := (666867371 / 1000000000)) (hi := (166716843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3117 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3117 / 1600) = 1/(1600 / 3117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (666867371 / 1000000000) (166716843 / 250000000) (Real.log (3117 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3117 / 1600) = -Real.log (1600 / 3117) := by
    rw [show ((3117 / 1600) : ℝ) = ((1600 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1479459149 / 500000000) ≤ -Real.log (83 / 1600) ∧
    -Real.log (83 / 1600) ≤ (2958918303 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 183)) (n := 12)
    (lo := (93164789 / 500000000)) (hi := (186329579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 83) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 83) = 1/(83 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2958918303 / 1000000000) (-1479459149 / 500000000) (Real.log (83 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (133335373 / 200000000) ≤ -Real.log (2048 / 3989) ∧
    -Real.log (2048 / 3989) ≤ (333338433 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 6037)) (n := 12)
    (lo := (133335373 / 200000000)) (hi := (333338433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2048) = 1/(2048 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (133335373 / 200000000) (333338433 / 500000000) (Real.log (3989 / 2048)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3989 / 2048) = -Real.log (2048 / 3989) := by
    rw [show ((3989 / 2048) : ℝ) = ((2048 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2951790149 / 1000000000) ≤ -Real.log (107 / 2048) ∧
    -Real.log (107 / 2048) ≤ (1475895077 / 500000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(128 / 107) = 1/(107 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) (Real.log (107 / 2048)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136419471 / 200000000) ≤ -Real.log (500000 / 989011) ∧
    -Real.log (500000 / 989011) ≤ (170524339 / 250000000) := by
  have h := checkLog_sound (w := (489011 / 1489011)) (n := 12)
    (lo := (136419471 / 200000000)) (hi := (170524339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989011 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989011 / 500000) = 1/(500000 / 989011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136419471 / 200000000) (170524339 / 250000000) (Real.log (989011 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989011 / 500000) = -Real.log (500000 / 989011) := by
    rw [show ((989011 / 500000) : ℝ) = ((500000 / 989011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3817713323 / 1000000000) ≤ -Real.log (10989 / 500000) ∧
    -Real.log (10989 / 500000) ≤ (3817713329 / 1000000000) := by
  have h := checkLog_sound (w := (2318 / 13307)) (n := 12)
    (lo := (351977423 / 1000000000)) (hi := (21998589 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10989) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10989) = 1/(10989 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3817713329 / 1000000000) (-3817713323 / 1000000000) (Real.log (10989 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136434637 / 200000000) ≤ -Real.log (250000 / 494543) ∧
    -Real.log (250000 / 494543) ≤ (341086593 / 500000000) := by
  have h := checkLog_sound (w := (244543 / 744543)) (n := 12)
    (lo := (136434637 / 200000000)) (hi := (341086593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494543 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494543 / 250000) = 1/(250000 / 494543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136434637 / 200000000) (341086593 / 500000000) (Real.log (494543 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494543 / 250000) = -Real.log (250000 / 494543) := by
    rw [show ((494543 / 250000) : ℝ) = ((250000 / 494543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1912280863 / 500000000) ≤ -Real.log (5457 / 250000) ∧
    -Real.log (5457 / 250000) ≤ (956140433 / 250000000) := by
  have h := checkLog_sound (w := (4711 / 26539)) (n := 12)
    (lo := (179412913 / 500000000)) (hi := (358825827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10914) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10914) = 1/(5457 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-956140433 / 250000000) (-1912280863 / 500000000) (Real.log (5457 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682040731 / 1000000000) ≤ -Real.log (100000 / 197791) ∧
    -Real.log (100000 / 197791) ≤ (170510183 / 250000000) := by
  have h := checkLog_sound (w := (97791 / 297791)) (n := 12)
    (lo := (682040731 / 1000000000)) (hi := (170510183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197791 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197791 / 100000) = 1/(100000 / 197791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682040731 / 1000000000) (170510183 / 250000000) (Real.log (197791 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (197791 / 100000) = -Real.log (100000 / 197791) := by
    rw [show ((197791 / 100000) : ℝ) = ((100000 / 197791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1906315129 / 500000000) ≤ -Real.log (2209 / 100000) ∧
    -Real.log (2209 / 100000) ≤ (476578783 / 125000000) := by
  have h := checkLog_sound (w := (458 / 2667)) (n := 12)
    (lo := (173447179 / 500000000)) (hi := (346894359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2209) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2209) = 1/(2209 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-476578783 / 125000000) (-1906315129 / 500000000) (Real.log (2209 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682117577 / 1000000000) ≤ -Real.log (500000 / 989031) ∧
    -Real.log (500000 / 989031) ≤ (341058789 / 500000000) := by
  have h := checkLog_sound (w := (489031 / 1489031)) (n := 12)
    (lo := (682117577 / 1000000000)) (hi := (341058789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989031 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989031 / 500000) = 1/(500000 / 989031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682117577 / 1000000000) (341058789 / 500000000) (Real.log (989031 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (989031 / 500000) = -Real.log (500000 / 989031) := by
    rw [show ((989031 / 500000) : ℝ) = ((500000 / 989031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3819534983 / 1000000000) ≤ -Real.log (10969 / 500000) ∧
    -Real.log (10969 / 500000) ≤ (3819534989 / 1000000000) := by
  have h := checkLog_sound (w := (2328 / 13297)) (n := 12)
    (lo := (353799083 / 1000000000)) (hi := (88449771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10969) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10969) = 1/(10969 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3819534989 / 1000000000) (-3819534983 / 1000000000) (Real.log (10969 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2249905339 / 500000000) ≤ -Real.log (100000000000 / 9000009100009) ∧
    -Real.log (100000000000 / 9000009100009) ≤ (899962137 / 200000000) := by
  have h := checkLog_sound (w := (2600009100009 / 15400009100009)) (n := 12)
    (lo := (170463799 / 500000000)) (hi := (340927599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9000009100009 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9000009100009 / 6400000000000) = 1/(100000000000 / 9000009100009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2249905339 / 500000000) (899962137 / 200000000) (Real.log (9000009100009 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9000009100009 / 100000000000) = -Real.log (100000000000 / 9000009100009) := by
    rw [show ((9000009100009 / 100000000000) : ℝ) = ((100000000000 / 9000009100009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (70417733 / 15625000) ≤ -Real.log (500000000000 / 45312717610409) ∧
    -Real.log (500000000000 / 45312717610409) ≤ (4506734919 / 1000000000) := by
  have h := checkLog_sound (w := (13312717610409 / 77312717610409)) (n := 12)
    (lo := (43481479 / 125000000)) (hi := (347851833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45312717610409 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45312717610409 / 32000000000000) = 1/(500000000000 / 45312717610409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (70417733 / 15625000) (4506734919 / 1000000000) (Real.log (45312717610409 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45312717610409 / 500000000000) = -Real.log (500000000000 / 45312717610409) := by
    rw [show ((45312717610409 / 500000000000) : ℝ) = ((500000000000 / 45312717610409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4494670989 / 1000000000) ≤ -Real.log (500000000000 / 44769352648257) ∧
    -Real.log (500000000000 / 44769352648257) ≤ (1123667749 / 250000000) := by
  have h := checkLog_sound (w := (12769352648257 / 76769352648257)) (n := 12)
    (lo := (335787909 / 1000000000)) (hi := (33578791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44769352648257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44769352648257 / 32000000000000) = 1/(500000000000 / 44769352648257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4494670989 / 1000000000) (1123667749 / 250000000) (Real.log (44769352648257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44769352648257 / 500000000000) = -Real.log (500000000000 / 44769352648257) := by
    rw [show ((44769352648257 / 500000000000) : ℝ) = ((500000000000 / 44769352648257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (56270657 / 12500000) ≤ -Real.log (500000000000 / 45083006655119) ∧
    -Real.log (500000000000 / 45083006655119) ≤ (4501652567 / 1000000000) := by
  have h := checkLog_sound (w := (13083006655119 / 77083006655119)) (n := 12)
    (lo := (8569237 / 25000000)) (hi := (342769481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45083006655119 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45083006655119 / 32000000000000) = 1/(500000000000 / 45083006655119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (56270657 / 12500000) (4501652567 / 1000000000) (Real.log (45083006655119 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45083006655119 / 500000000000) = -Real.log (500000000000 / 45083006655119) := by
    rw [show ((45083006655119 / 500000000000) : ℝ) = ((500000000000 / 45083006655119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039
