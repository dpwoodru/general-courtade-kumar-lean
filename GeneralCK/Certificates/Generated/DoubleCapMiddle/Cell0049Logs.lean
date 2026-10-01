import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0049
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

theorem reflection_log_1_neg : (375328013 / 1000000000) ≤ -Real.log (1280 / 1863) ∧
    -Real.log (1280 / 1863) ≤ (187664007 / 500000000) := by
  have h := checkLog_sound (w := (583 / 3143)) (n := 12)
    (lo := (375328013 / 1000000000)) (hi := (187664007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1280) = 1/(1280 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (375328013 / 1000000000) (187664007 / 500000000) (Real.log (1863 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1863 / 1280) = -Real.log (1280 / 1863) := by
    rw [show ((1863 / 1280) : ℝ) = ((1280 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (303914973 / 500000000) ≤ -Real.log (697 / 1280) ∧
    -Real.log (697 / 1280) ≤ (607829947 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 1977)) (n := 12)
    (lo := (303914973 / 500000000)) (hi := (607829947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 697) = 1/(697 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-607829947 / 1000000000) (-303914973 / 500000000) (Real.log (697 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (46815317 / 125000000) ≤ -Real.log (2560 / 3723) ∧
    -Real.log (2560 / 3723) ≤ (374522537 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 6283)) (n := 12)
    (lo := (46815317 / 125000000)) (hi := (374522537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3723 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3723 / 2560) = 1/(2560 / 3723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (46815317 / 125000000) (374522537 / 1000000000) (Real.log (3723 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3723 / 2560) = -Real.log (2560 / 3723) := by
    rw [show ((3723 / 2560) : ℝ) = ((2560 / 3723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302840089 / 500000000) ≤ -Real.log (1397 / 2560) ∧
    -Real.log (1397 / 2560) ≤ (605680179 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 3957)) (n := 12)
    (lo := (302840089 / 500000000)) (hi := (605680179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1397) = 1/(1397 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-605680179 / 1000000000) (-302840089 / 500000000) (Real.log (1397 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (647593959 / 1000000000) ≤ -Real.log (640 / 1223) ∧
    -Real.log (640 / 1223) ≤ (16189849 / 25000000) := by
  have h := checkLog_sound (w := (583 / 1863)) (n := 12)
    (lo := (647593959 / 1000000000)) (hi := (16189849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223 / 640) = 1/(640 / 1223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (647593959 / 1000000000) (16189849 / 25000000) (Real.log (1223 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223 / 640) = -Real.log (640 / 1223) := by
    rw [show ((1223 / 640) : ℝ) = ((640 / 1223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1209208453 / 500000000) ≤ -Real.log (57 / 640) ∧
    -Real.log (57 / 640) ≤ (241841691 / 100000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 57) = 1/(57 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-241841691 / 100000000) (-1209208453 / 500000000) (Real.log (57 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (323183357 / 500000000) ≤ -Real.log (1280 / 2443) ∧
    -Real.log (1280 / 2443) ≤ (129273343 / 200000000) := by
  have h := checkLog_sound (w := (1163 / 3723)) (n := 12)
    (lo := (323183357 / 500000000)) (hi := (129273343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 1280) = 1/(1280 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (323183357 / 500000000) (129273343 / 200000000) (Real.log (2443 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2443 / 1280) = -Real.log (1280 / 2443) := by
    rw [show ((2443 / 1280) : ℝ) = ((1280 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (119622071 / 50000000) ≤ -Real.log (117 / 1280) ∧
    -Real.log (117 / 1280) ≤ (149527589 / 62500000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 117) = 1/(117 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-149527589 / 62500000) (-119622071 / 50000000) (Real.log (117 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (518983061 / 1000000000) ≤ -Real.log (500000 / 840159) ∧
    -Real.log (500000 / 840159) ≤ (259491531 / 500000000) := by
  have h := checkLog_sound (w := (340159 / 1340159)) (n := 12)
    (lo := (518983061 / 1000000000)) (hi := (259491531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840159 / 500000) = 1/(500000 / 840159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (518983061 / 1000000000) (259491531 / 500000000) (Real.log (840159 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (840159 / 500000) = -Real.log (500000 / 840159) := by
    rw [show ((840159 / 500000) : ℝ) = ((500000 / 840159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (570214263 / 500000000) ≤ -Real.log (159841 / 500000) ∧
    -Real.log (159841 / 500000) ≤ (71276783 / 62500000) := by
  have h := checkLog_sound (w := (90159 / 409841)) (n := 12)
    (lo := (223640673 / 500000000)) (hi := (447281347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159841) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 159841) = 1/(159841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-71276783 / 62500000) (-570214263 / 500000000) (Real.log (159841 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (520262951 / 1000000000) ≤ -Real.log (100000 / 168247) ∧
    -Real.log (100000 / 168247) ≤ (65032869 / 125000000) := by
  have h := checkLog_sound (w := (68247 / 268247)) (n := 12)
    (lo := (520262951 / 1000000000)) (hi := (65032869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168247 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168247 / 100000) = 1/(100000 / 168247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (520262951 / 1000000000) (65032869 / 125000000) (Real.log (168247 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (168247 / 100000) = -Real.log (100000 / 168247) := by
    rw [show ((168247 / 100000) : ℝ) = ((100000 / 168247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8962367 / 7812500) ≤ -Real.log (31753 / 100000) ∧
    -Real.log (31753 / 100000) ≤ (573591489 / 500000000) := by
  have h := checkLog_sound (w := (18247 / 81753)) (n := 12)
    (lo := (113508949 / 250000000)) (hi := (454035797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 31753) = 1/(31753 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-573591489 / 500000000) (-8962367 / 7812500) (Real.log (31753 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (438739329 / 1000000000) ≤ -Real.log (1000000 / 1550751) ∧
    -Real.log (1000000 / 1550751) ≤ (43873933 / 100000000) := by
  have h := checkLog_sound (w := (550751 / 2550751)) (n := 12)
    (lo := (438739329 / 1000000000)) (hi := (43873933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1550751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1550751 / 1000000) = 1/(1000000 / 1550751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (438739329 / 1000000000) (43873933 / 100000000) (Real.log (1550751 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1550751 / 1000000) = -Real.log (1000000 / 1550751) := by
    rw [show ((1550751 / 1000000) : ℝ) = ((1000000 / 1550751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (400088989 / 500000000) ≤ -Real.log (449249 / 1000000) ∧
    -Real.log (449249 / 1000000) ≤ (40008899 / 50000000) := by
  have h := checkLog_sound (w := (50751 / 949249)) (n := 12)
    (lo := (53515399 / 500000000)) (hi := (107030799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 449249) = 1/(449249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40008899 / 50000000) (-400088989 / 500000000) (Real.log (449249 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (440179529 / 1000000000) ≤ -Real.log (500000 / 776493) ∧
    -Real.log (500000 / 776493) ≤ (44017953 / 100000000) := by
  have h := checkLog_sound (w := (276493 / 1276493)) (n := 12)
    (lo := (440179529 / 1000000000)) (hi := (44017953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776493 / 500000) = 1/(500000 / 776493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (440179529 / 1000000000) (44017953 / 100000000) (Real.log (776493 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (776493 / 500000) = -Real.log (500000 / 776493) := by
    rw [show ((776493 / 500000) : ℝ) = ((500000 / 776493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (201291341 / 250000000) ≤ -Real.log (223507 / 500000) ∧
    -Real.log (223507 / 500000) ≤ (402582683 / 500000000) := by
  have h := checkLog_sound (w := (26493 / 473507)) (n := 12)
    (lo := (14002273 / 125000000)) (hi := (22403637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 223507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 223507) = 1/(223507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-402582683 / 500000000) (-201291341 / 250000000) (Real.log (223507 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1659411587 / 1000000000) ≤ -Real.log (500000000000 / 2628108557879) ∧
    -Real.log (500000000000 / 2628108557879) ≤ (165941159 / 100000000) := by
  have h := checkLog_sound (w := (628108557879 / 4628108557879)) (n := 12)
    (lo := (273117227 / 1000000000)) (hi := (68279307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2628108557879 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2628108557879 / 2000000000000) = 1/(500000000000 / 2628108557879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1659411587 / 1000000000) (165941159 / 100000000) (Real.log (2628108557879 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2628108557879 / 500000000000) = -Real.log (500000000000 / 2628108557879) := by
    rw [show ((2628108557879 / 500000000000) : ℝ) = ((500000000000 / 2628108557879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1667445927 / 1000000000) ≤ -Real.log (100000000000 / 529861745347) ∧
    -Real.log (100000000000 / 529861745347) ≤ (166744593 / 100000000) := by
  have h := checkLog_sound (w := (129861745347 / 929861745347)) (n := 12)
    (lo := (281151567 / 1000000000)) (hi := (17571973 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529861745347 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(529861745347 / 400000000000) = 1/(100000000000 / 529861745347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1667445927 / 1000000000) (166744593 / 100000000) (Real.log (529861745347 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (529861745347 / 100000000000) = -Real.log (100000000000 / 529861745347) := by
    rw [show ((529861745347 / 100000000000) : ℝ) = ((100000000000 / 529861745347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309729327 / 250000000) ≤ -Real.log (100000000000 / 345187412771) ∧
    -Real.log (100000000000 / 345187412771) ≤ (123891731 / 100000000) := by
  have h := checkLog_sound (w := (145187412771 / 545187412771)) (n := 12)
    (lo := (34110633 / 62500000)) (hi := (545770129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345187412771 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(345187412771 / 200000000000) = 1/(100000000000 / 345187412771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309729327 / 250000000) (123891731 / 100000000) (Real.log (345187412771 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (345187412771 / 100000000000) = -Real.log (100000000000 / 345187412771) := by
    rw [show ((345187412771 / 100000000000) : ℝ) = ((100000000000 / 345187412771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1245344893 / 1000000000) ≤ -Real.log (100000000000 / 347413280121) ∧
    -Real.log (100000000000 / 347413280121) ≤ (249068979 / 200000000) := by
  have h := checkLog_sound (w := (147413280121 / 547413280121)) (n := 12)
    (lo := (552197713 / 1000000000)) (hi := (276098857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347413280121 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(347413280121 / 200000000000) = 1/(100000000000 / 347413280121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1245344893 / 1000000000) (249068979 / 200000000) (Real.log (347413280121 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (347413280121 / 100000000000) = -Real.log (100000000000 / 347413280121) := by
    rw [show ((347413280121 / 100000000000) : ℝ) = ((100000000000 / 347413280121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0049
