import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0086
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

theorem reflection_log_1_neg : (337029961 / 500000000) ≤ -Real.log (3200 / 6279) ∧
    -Real.log (3200 / 6279) ≤ (674059923 / 1000000000) := by
  have h := checkLog_sound (w := (3079 / 9479)) (n := 12)
    (lo := (337029961 / 500000000)) (hi := (674059923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 3200) = 1/(3200 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337029961 / 500000000) (674059923 / 1000000000) (Real.log (6279 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6279 / 3200) = -Real.log (3200 / 6279) := by
    rw [show ((6279 / 3200) : ℝ) = ((3200 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (163755777 / 50000000) ≤ -Real.log (121 / 3200) ∧
    -Real.log (121 / 3200) ≤ (655023109 / 200000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 121) = 1/(121 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-655023109 / 200000000) (-163755777 / 50000000) (Real.log (121 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (673870781 / 1000000000) ≤ -Real.log (10240 / 20089) ∧
    -Real.log (10240 / 20089) ≤ (336935391 / 500000000) := by
  have h := checkLog_sound (w := (9849 / 30329)) (n := 12)
    (lo := (673870781 / 1000000000)) (hi := (336935391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20089 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20089 / 10240) = 1/(10240 / 20089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (673870781 / 1000000000) (336935391 / 500000000) (Real.log (20089 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20089 / 10240) = -Real.log (10240 / 20089) := by
    rw [show ((20089 / 10240) : ℝ) = ((10240 / 20089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (408168667 / 125000000) ≤ -Real.log (391 / 10240) ∧
    -Real.log (391 / 10240) ≤ (3265349341 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 391) = 1/(391 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3265349341 / 1000000000) (-408168667 / 125000000) (Real.log (391 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (654601239 / 1000000000) ≤ -Real.log (1600 / 3079) ∧
    -Real.log (1600 / 3079) ≤ (16365031 / 25000000) := by
  have h := checkLog_sound (w := (1479 / 4679)) (n := 12)
    (lo := (654601239 / 1000000000)) (hi := (16365031 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3079 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3079 / 1600) = 1/(1600 / 3079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (654601239 / 1000000000) (16365031 / 25000000) (Real.log (3079 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3079 / 1600) = -Real.log (1600 / 3079) := by
    rw [show ((3079 / 1600) : ℝ) = ((1600 / 3079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64549209 / 25000000) ≤ -Real.log (121 / 1600) ∧
    -Real.log (121 / 1600) ≤ (645492091 / 250000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 121) = 1/(121 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-645492091 / 250000000) (-64549209 / 25000000) (Real.log (121 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10222117 / 15625000) ≤ -Real.log (5120 / 9849) ∧
    -Real.log (5120 / 9849) ≤ (654215489 / 1000000000) := by
  have h := checkLog_sound (w := (4729 / 14969)) (n := 12)
    (lo := (10222117 / 15625000)) (hi := (654215489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9849 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9849 / 5120) = 1/(5120 / 9849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10222117 / 15625000) (654215489 / 1000000000) (Real.log (9849 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9849 / 5120) = -Real.log (5120 / 9849) := by
    rw [show ((9849 / 5120) : ℝ) = ((5120 / 9849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (643050539 / 250000000) ≤ -Real.log (391 / 5120) ∧
    -Real.log (391 / 5120) ≤ (32152527 / 12500000) := by
  have h := checkLog_sound (w := (249 / 1031)) (n := 12)
    (lo := (61595077 / 125000000)) (hi := (492760617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 391) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 391) = 1/(391 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32152527 / 12500000) (-643050539 / 250000000) (Real.log (391 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677256591 / 1000000000) ≤ -Real.log (100000 / 196847) ∧
    -Real.log (100000 / 196847) ≤ (42328537 / 62500000) := by
  have h := checkLog_sound (w := (96847 / 296847)) (n := 12)
    (lo := (677256591 / 1000000000)) (hi := (42328537 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196847 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196847 / 100000) = 1/(100000 / 196847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677256591 / 1000000000) (42328537 / 62500000) (Real.log (196847 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196847 / 100000) = -Real.log (100000 / 196847) := by
    rw [show ((196847 / 100000) : ℝ) = ((100000 / 196847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3456815803 / 1000000000) ≤ -Real.log (3153 / 100000) ∧
    -Real.log (3153 / 100000) ≤ (54012747 / 15625000) := by
  have h := checkLog_sound (w := (3097 / 9403)) (n := 12)
    (lo := (684227083 / 1000000000)) (hi := (171056771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3153) = 1/(3153 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-54012747 / 15625000) (-3456815803 / 1000000000) (Real.log (3153 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (338701951 / 500000000) ≤ -Real.log (25000 / 49219) ∧
    -Real.log (25000 / 49219) ≤ (677403903 / 1000000000) := by
  have h := checkLog_sound (w := (24219 / 74219)) (n := 12)
    (lo := (338701951 / 500000000)) (hi := (677403903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49219 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49219 / 25000) = 1/(25000 / 49219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (338701951 / 500000000) (677403903 / 1000000000) (Real.log (49219 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49219 / 25000) = -Real.log (25000 / 49219) := by
    rw [show ((49219 / 25000) : ℝ) = ((25000 / 49219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3466055951 / 1000000000) ≤ -Real.log (781 / 25000) ∧
    -Real.log (781 / 25000) ≤ (3466055957 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6249)) (n := 12)
    (lo := (320051 / 1000000000)) (hi := (80013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3124) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 3124) = 1/(781 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3466055957 / 1000000000) (-3466055951 / 1000000000) (Real.log (781 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84640499 / 125000000) ≤ -Real.log (1000000 / 1968209) ∧
    -Real.log (1000000 / 1968209) ≤ (677123993 / 1000000000) := by
  have h := checkLog_sound (w := (968209 / 2968209)) (n := 12)
    (lo := (84640499 / 125000000)) (hi := (677123993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968209 / 1000000) = 1/(1000000 / 1968209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84640499 / 125000000) (677123993 / 1000000000) (Real.log (1968209 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1968209 / 1000000) = -Real.log (1000000 / 1968209) := by
    rw [show ((1968209 / 1000000) : ℝ) = ((1000000 / 1968209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (689714409 / 200000000) ≤ -Real.log (31791 / 1000000) ∧
    -Real.log (31791 / 1000000) ≤ (68971441 / 20000000) := by
  have h := checkLog_sound (w := (30709 / 94291)) (n := 12)
    (lo := (27039333 / 40000000)) (hi := (337991663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31791) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31791) = 1/(31791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-68971441 / 20000000) (-689714409 / 200000000) (Real.log (31791 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (677274371 / 1000000000) ≤ -Real.log (200000 / 393701) ∧
    -Real.log (200000 / 393701) ≤ (169318593 / 250000000) := by
  have h := checkLog_sound (w := (193701 / 593701)) (n := 12)
    (lo := (677274371 / 1000000000)) (hi := (169318593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393701 / 200000) = 1/(200000 / 393701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (677274371 / 1000000000) (169318593 / 250000000) (Real.log (393701 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (393701 / 200000) = -Real.log (200000 / 393701) := by
    rw [show ((393701 / 200000) : ℝ) = ((200000 / 393701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3457926473 / 1000000000) ≤ -Real.log (6299 / 200000) ∧
    -Real.log (6299 / 200000) ≤ (1728963239 / 500000000) := by
  have h := checkLog_sound (w := (6201 / 18799)) (n := 12)
    (lo := (685337753 / 1000000000)) (hi := (342668877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 6299) = 1/(6299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1728963239 / 500000000) (-3457926473 / 1000000000) (Real.log (6299 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4134072393 / 1000000000) ≤ -Real.log (62500000000 / 3901978274659) ∧
    -Real.log (62500000000 / 3901978274659) ≤ (4134072399 / 1000000000) := by
  have h := checkLog_sound (w := (1901978274659 / 5901978274659)) (n := 12)
    (lo := (668336493 / 1000000000)) (hi := (334168247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3901978274659 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3901978274659 / 2000000000000) = 1/(62500000000 / 3901978274659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4134072393 / 1000000000) (4134072399 / 1000000000) (Real.log (3901978274659 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3901978274659 / 62500000000) = -Real.log (62500000000 / 3901978274659) := by
    rw [show ((3901978274659 / 62500000000) : ℝ) = ((62500000000 / 3901978274659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2071729927 / 500000000) ≤ -Real.log (500000000000 / 31510243277849) ∧
    -Real.log (500000000000 / 31510243277849) ≤ (207172993 / 50000000) := by
  have h := checkLog_sound (w := (15510243277849 / 47510243277849)) (n := 12)
    (lo := (338861977 / 500000000)) (hi := (135544791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31510243277849 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31510243277849 / 16000000000000) = 1/(500000000000 / 31510243277849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2071729927 / 500000000) (207172993 / 50000000) (Real.log (31510243277849 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (31510243277849 / 500000000000) = -Real.log (500000000000 / 31510243277849) := by
    rw [show ((31510243277849 / 500000000000) : ℝ) = ((500000000000 / 31510243277849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4125696037 / 1000000000) ≤ -Real.log (250000000000 / 15477721682237) ∧
    -Real.log (250000000000 / 15477721682237) ≤ (4125696043 / 1000000000) := by
  have h := checkLog_sound (w := (7477721682237 / 23477721682237)) (n := 12)
    (lo := (659960137 / 1000000000)) (hi := (329980069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15477721682237 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15477721682237 / 8000000000000) = 1/(250000000000 / 15477721682237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4125696037 / 1000000000) (4125696043 / 1000000000) (Real.log (15477721682237 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15477721682237 / 250000000000) = -Real.log (250000000000 / 15477721682237) := by
    rw [show ((15477721682237 / 250000000000) : ℝ) = ((250000000000 / 15477721682237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1033800211 / 250000000) ≤ -Real.log (500000000000 / 31251071598667) ∧
    -Real.log (500000000000 / 31251071598667) ≤ (82704017 / 20000000) := by
  have h := checkLog_sound (w := (15251071598667 / 47251071598667)) (n := 12)
    (lo := (41841559 / 62500000)) (hi := (133892989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31251071598667 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31251071598667 / 16000000000000) = 1/(500000000000 / 31251071598667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1033800211 / 250000000) (82704017 / 20000000) (Real.log (31251071598667 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31251071598667 / 500000000000) = -Real.log (500000000000 / 31251071598667) := by
    rw [show ((31251071598667 / 500000000000) : ℝ) = ((500000000000 / 31251071598667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0086
