import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0087
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

theorem reflection_log_1_neg : (673870781 / 1000000000) ≤ -Real.log (10240 / 20089) ∧
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


theorem reflection_log_1 : Bounds (673870781 / 1000000000) (336935391 / 500000000) (Real.log (20089 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20089 / 10240) = -Real.log (10240 / 20089) := by
    rw [show ((20089 / 10240) : ℝ) = ((10240 / 20089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (408168667 / 125000000) ≤ -Real.log (391 / 10240) ∧
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


theorem reflection_log_2 : Bounds (-3265349341 / 1000000000) (-408168667 / 125000000) (Real.log (391 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (134736321 / 200000000) ≤ -Real.log (25600 / 50213) ∧
    -Real.log (25600 / 50213) ≤ (336840803 / 500000000) := by
  have h := checkLog_sound (w := (24613 / 75813)) (n := 12)
    (lo := (134736321 / 200000000)) (hi := (336840803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50213 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50213 / 25600) = 1/(25600 / 50213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (134736321 / 200000000) (336840803 / 500000000) (Real.log (50213 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50213 / 25600) = -Real.log (25600 / 50213) := by
    rw [show ((50213 / 25600) : ℝ) = ((25600 / 50213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (813919397 / 250000000) ≤ -Real.log (987 / 25600) ∧
    -Real.log (987 / 25600) ≤ (3255677593 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 987) = 1/(987 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3255677593 / 1000000000) (-813919397 / 250000000) (Real.log (987 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10222117 / 15625000) ≤ -Real.log (5120 / 9849) ∧
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


theorem reflection_log_5 : Bounds (10222117 / 15625000) (654215489 / 1000000000) (Real.log (9849 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9849 / 5120) = -Real.log (5120 / 9849) := by
    rw [show ((9849 / 5120) : ℝ) = ((5120 / 9849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (643050539 / 250000000) ≤ -Real.log (391 / 5120) ∧
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


theorem reflection_log_6 : Bounds (-32152527 / 12500000) (-643050539 / 250000000) (Real.log (391 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653829587 / 1000000000) ≤ -Real.log (12800 / 24613) ∧
    -Real.log (12800 / 24613) ≤ (163457397 / 250000000) := by
  have h := checkLog_sound (w := (11813 / 37413)) (n := 12)
    (lo := (653829587 / 1000000000)) (hi := (163457397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24613 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24613 / 12800) = 1/(12800 / 24613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653829587 / 1000000000) (163457397 / 250000000) (Real.log (24613 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24613 / 12800) = -Real.log (12800 / 24613) := by
    rw [show ((24613 / 12800) : ℝ) = ((12800 / 24613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (320316301 / 125000000) ≤ -Real.log (987 / 12800) ∧
    -Real.log (987 / 12800) ≤ (640632603 / 250000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 987) = 1/(987 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-640632603 / 250000000) (-320316301 / 125000000) (Real.log (987 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (677109257 / 1000000000) ≤ -Real.log (50000 / 98409) ∧
    -Real.log (50000 / 98409) ≤ (338554629 / 500000000) := by
  have h := checkLog_sound (w := (48409 / 148409)) (n := 12)
    (lo := (677109257 / 1000000000)) (hi := (338554629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98409 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98409 / 50000) = 1/(50000 / 98409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (677109257 / 1000000000) (338554629 / 500000000) (Real.log (98409 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98409 / 50000) = -Real.log (50000 / 98409) := by
    rw [show ((98409 / 50000) : ℝ) = ((50000 / 98409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3447660253 / 1000000000) ≤ -Real.log (1591 / 50000) ∧
    -Real.log (1591 / 50000) ≤ (1723830129 / 500000000) := by
  have h := checkLog_sound (w := (767 / 2358)) (n := 12)
    (lo := (675071533 / 1000000000)) (hi := (337535767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1591) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1591) = 1/(1591 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1723830129 / 500000000) (-3447660253 / 1000000000) (Real.log (1591 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (677257099 / 1000000000) ≤ -Real.log (1000000 / 1968471) ∧
    -Real.log (1000000 / 1968471) ≤ (6772571 / 10000000) := by
  have h := checkLog_sound (w := (968471 / 2968471)) (n := 12)
    (lo := (677257099 / 1000000000)) (hi := (6772571 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968471 / 1000000) = 1/(1000000 / 1968471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (677257099 / 1000000000) (6772571 / 10000000) (Real.log (1968471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1968471 / 1000000) = -Real.log (1000000 / 1968471) := by
    rw [show ((1968471 / 1000000) : ℝ) = ((1000000 / 1968471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3456847519 / 1000000000) ≤ -Real.log (31529 / 1000000) ∧
    -Real.log (31529 / 1000000) ≤ (864211881 / 250000000) := by
  have h := checkLog_sound (w := (30971 / 94029)) (n := 12)
    (lo := (684258799 / 1000000000)) (hi := (1710647 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31529) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31529) = 1/(31529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-864211881 / 250000000) (-3456847519 / 1000000000) (Real.log (31529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (67697359 / 100000000) ≤ -Real.log (1000000 / 1967913) ∧
    -Real.log (1000000 / 1967913) ≤ (676973591 / 1000000000) := by
  have h := checkLog_sound (w := (967913 / 2967913)) (n := 12)
    (lo := (67697359 / 100000000)) (hi := (676973591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967913 / 1000000) = 1/(1000000 / 1967913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (67697359 / 100000000) (676973591 / 1000000000) (Real.log (1967913 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1967913 / 1000000) = -Real.log (1000000 / 1967913) := by
    rw [show ((1967913 / 1000000) : ℝ) = ((1000000 / 1967913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3439304313 / 1000000000) ≤ -Real.log (32087 / 1000000) ∧
    -Real.log (32087 / 1000000) ≤ (1719652159 / 500000000) := by
  have h := checkLog_sound (w := (30413 / 94587)) (n := 12)
    (lo := (666715593 / 1000000000)) (hi := (333357797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32087) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32087) = 1/(32087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1719652159 / 500000000) (-3439304313 / 1000000000) (Real.log (32087 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1354249 / 2000000) ≤ -Real.log (100000 / 196821) ∧
    -Real.log (100000 / 196821) ≤ (677124501 / 1000000000) := by
  have h := checkLog_sound (w := (96821 / 296821)) (n := 12)
    (lo := (1354249 / 2000000)) (hi := (677124501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196821 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196821 / 100000) = 1/(100000 / 196821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1354249 / 2000000) (677124501 / 1000000000) (Real.log (196821 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196821 / 100000) = -Real.log (100000 / 196821) := by
    rw [show ((196821 / 100000) : ℝ) = ((100000 / 196821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3448603501 / 1000000000) ≤ -Real.log (3179 / 100000) ∧
    -Real.log (3179 / 100000) ≤ (1724301753 / 500000000) := by
  have h := checkLog_sound (w := (3071 / 9429)) (n := 12)
    (lo := (676014781 / 1000000000)) (hi := (338007391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3179) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3179) = 1/(3179 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1724301753 / 500000000) (-3448603501 / 1000000000) (Real.log (3179 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4124769511 / 1000000000) ≤ -Real.log (250000000000 / 15463387806411) ∧
    -Real.log (250000000000 / 15463387806411) ≤ (4124769517 / 1000000000) := by
  have h := checkLog_sound (w := (7463387806411 / 23463387806411)) (n := 12)
    (lo := (659033611 / 1000000000)) (hi := (164758403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15463387806411 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15463387806411 / 8000000000000) = 1/(250000000000 / 15463387806411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4124769511 / 1000000000) (4124769517 / 1000000000) (Real.log (15463387806411 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15463387806411 / 250000000000) = -Real.log (250000000000 / 15463387806411) := by
    rw [show ((15463387806411 / 250000000000) : ℝ) = ((250000000000 / 15463387806411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2067052309 / 500000000) ≤ -Real.log (62500000000 / 3902104015351) ∧
    -Real.log (62500000000 / 3902104015351) ≤ (258381539 / 62500000) := by
  have h := checkLog_sound (w := (1902104015351 / 5902104015351)) (n := 12)
    (lo := (334184359 / 500000000)) (hi := (668368719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3902104015351 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3902104015351 / 2000000000000) = 1/(62500000000 / 3902104015351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2067052309 / 500000000) (258381539 / 62500000) (Real.log (3902104015351 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3902104015351 / 62500000000) = -Real.log (62500000000 / 3902104015351) := by
    rw [show ((3902104015351 / 62500000000) : ℝ) = ((62500000000 / 3902104015351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2058138951 / 500000000) ≤ -Real.log (250000000000 / 15332634711877) ∧
    -Real.log (250000000000 / 15332634711877) ≤ (1029069477 / 250000000) := by
  have h := checkLog_sound (w := (7332634711877 / 23332634711877)) (n := 12)
    (lo := (325271001 / 500000000)) (hi := (650542003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15332634711877 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15332634711877 / 8000000000000) = 1/(250000000000 / 15332634711877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2058138951 / 500000000) (1029069477 / 250000000) (Real.log (15332634711877 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15332634711877 / 250000000000) = -Real.log (250000000000 / 15332634711877) := by
    rw [show ((15332634711877 / 250000000000) : ℝ) = ((250000000000 / 15332634711877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4125728001 / 1000000000) ≤ -Real.log (125000000000 / 7739108210129) ∧
    -Real.log (125000000000 / 7739108210129) ≤ (4125728007 / 1000000000) := by
  have h := checkLog_sound (w := (3739108210129 / 11739108210129)) (n := 12)
    (lo := (659992101 / 1000000000)) (hi := (329996051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7739108210129 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7739108210129 / 4000000000000) = 1/(125000000000 / 7739108210129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4125728001 / 1000000000) (4125728007 / 1000000000) (Real.log (7739108210129 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7739108210129 / 125000000000) = -Real.log (125000000000 / 7739108210129) := by
    rw [show ((7739108210129 / 125000000000) : ℝ) = ((125000000000 / 7739108210129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0087
