import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219
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

theorem reflection_log_1_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (524173641 / 1000000000) ≤ -Real.log (640 / 1081) ∧
    -Real.log (640 / 1081) ≤ (262086821 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1721)) (n := 12)
    (lo := (524173641 / 1000000000)) (hi := (262086821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081 / 640) = 1/(640 / 1081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (524173641 / 1000000000) (262086821 / 500000000) (Real.log (1081 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1081 / 640) = -Real.log (640 / 1081) := by
    rw [show ((1081 / 640) : ℝ) = ((640 / 1081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1168163351 / 1000000000) ≤ -Real.log (199 / 640) ∧
    -Real.log (199 / 640) ≤ (1168163353 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 199) = 1/(199 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1168163353 / 1000000000) (-1168163351 / 1000000000) (Real.log (199 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_5_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148822941 / 250000000) ≤ -Real.log (25000 / 45339) ∧
    -Real.log (25000 / 45339) ≤ (119058353 / 200000000) := by
  have h := checkLog_sound (w := (20339 / 70339)) (n := 12)
    (lo := (148822941 / 250000000)) (hi := (119058353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45339 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45339 / 25000) = 1/(25000 / 45339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148822941 / 250000000) (119058353 / 200000000) (Real.log (45339 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (45339 / 25000) = -Real.log (25000 / 45339) := by
    rw [show ((45339 / 25000) : ℝ) = ((25000 / 45339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (839822903 / 500000000) ≤ -Real.log (4661 / 25000) ∧
    -Real.log (4661 / 25000) ≤ (1679645809 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 10911)) (n := 12)
    (lo := (146675723 / 500000000)) (hi := (293351447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4661) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 4661) = 1/(4661 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1679645809 / 1000000000) (-839822903 / 500000000) (Real.log (4661 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (298226997 / 500000000) ≤ -Real.log (1000000 / 1815669) ∧
    -Real.log (1000000 / 1815669) ≤ (119290799 / 200000000) := by
  have h := checkLog_sound (w := (815669 / 2815669)) (n := 12)
    (lo := (298226997 / 500000000)) (hi := (119290799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815669 / 1000000) = 1/(1000000 / 1815669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (298226997 / 500000000) (119290799 / 200000000) (Real.log (1815669 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1815669 / 1000000) = -Real.log (1000000 / 1815669) := by
    rw [show ((1815669 / 1000000) : ℝ) = ((1000000 / 1815669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1691022223 / 1000000000) ≤ -Real.log (184331 / 1000000) ∧
    -Real.log (184331 / 1000000) ≤ (845511113 / 500000000) := by
  have h := checkLog_sound (w := (65669 / 434331)) (n := 12)
    (lo := (304727863 / 1000000000)) (hi := (38090983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184331) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184331) = 1/(184331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-845511113 / 500000000) (-1691022223 / 1000000000) (Real.log (184331 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (287493943 / 500000000) ≤ -Real.log (1000000 / 1777109) ∧
    -Real.log (1000000 / 1777109) ≤ (574987887 / 1000000000) := by
  have h := checkLog_sound (w := (777109 / 2777109)) (n := 12)
    (lo := (287493943 / 500000000)) (hi := (574987887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777109 / 1000000) = 1/(1000000 / 1777109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (287493943 / 500000000) (574987887 / 1000000000) (Real.log (1777109 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1777109 / 1000000) = -Real.log (1000000 / 1777109) := by
    rw [show ((1777109 / 1000000) : ℝ) = ((1000000 / 1777109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (300214483 / 200000000) ≤ -Real.log (222891 / 1000000) ∧
    -Real.log (222891 / 1000000) ≤ (750536209 / 500000000) := by
  have h := checkLog_sound (w := (27109 / 472891)) (n := 12)
    (lo := (22955611 / 200000000)) (hi := (14347257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222891) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 222891) = 1/(222891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-750536209 / 500000000) (-300214483 / 200000000) (Real.log (222891 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (577135699 / 1000000000) ≤ -Real.log (100000 / 178093) ∧
    -Real.log (100000 / 178093) ≤ (5771357 / 10000000) := by
  have h := checkLog_sound (w := (78093 / 278093)) (n := 12)
    (lo := (577135699 / 1000000000)) (hi := (5771357 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178093 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178093 / 100000) = 1/(100000 / 178093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (577135699 / 1000000000) (5771357 / 10000000) (Real.log (178093 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (178093 / 100000) = -Real.log (100000 / 178093) := by
    rw [show ((178093 / 100000) : ℝ) = ((100000 / 178093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (379590991 / 250000000) ≤ -Real.log (21907 / 100000) ∧
    -Real.log (21907 / 100000) ≤ (1518363967 / 1000000000) := by
  have h := checkLog_sound (w := (3093 / 46907)) (n := 12)
    (lo := (33017401 / 250000000)) (hi := (26413921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 21907) = 1/(21907 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1518363967 / 1000000000) (-379590991 / 250000000) (Real.log (21907 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (227493757 / 100000000) ≤ -Real.log (500000000000 / 4863655867839) ∧
    -Real.log (500000000000 / 4863655867839) ≤ (1137468787 / 500000000) := by
  have h := checkLog_sound (w := (863655867839 / 8863655867839)) (n := 12)
    (lo := (19549603 / 100000000)) (hi := (195496031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4863655867839 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4863655867839 / 4000000000000) = 1/(500000000000 / 4863655867839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (227493757 / 100000000) (1137468787 / 500000000) (Real.log (4863655867839 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4863655867839 / 500000000000) = -Real.log (500000000000 / 4863655867839) := by
    rw [show ((4863655867839 / 500000000000) : ℝ) = ((500000000000 / 4863655867839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2287476217 / 1000000000) ≤ -Real.log (500000000000 / 4925023463227) ∧
    -Real.log (500000000000 / 4925023463227) ≤ (2287476221 / 1000000000) := by
  have h := checkLog_sound (w := (925023463227 / 8925023463227)) (n := 12)
    (lo := (208034677 / 1000000000)) (hi := (104017339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4925023463227 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4925023463227 / 4000000000000) = 1/(500000000000 / 4925023463227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2287476217 / 1000000000) (2287476221 / 1000000000) (Real.log (4925023463227 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4925023463227 / 500000000000) = -Real.log (500000000000 / 4925023463227) := by
    rw [show ((4925023463227 / 500000000000) : ℝ) = ((500000000000 / 4925023463227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2076060301 / 1000000000) ≤ -Real.log (62500000000 / 498312235577) ∧
    -Real.log (62500000000 / 498312235577) ≤ (129753769 / 62500000) := by
  have h := checkLog_sound (w := (248312235577 / 748312235577)) (n := 12)
    (lo := (689765941 / 1000000000)) (hi := (344882971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((498312235577 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(498312235577 / 250000000000) = 1/(62500000000 / 498312235577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2076060301 / 1000000000) (129753769 / 62500000) (Real.log (498312235577 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (498312235577 / 62500000000) = -Real.log (62500000000 / 498312235577) := by
    rw [show ((498312235577 / 62500000000) : ℝ) = ((62500000000 / 498312235577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2095499663 / 1000000000) ≤ -Real.log (250000000000 / 2032375496417) ∧
    -Real.log (250000000000 / 2032375496417) ≤ (2095499667 / 1000000000) := by
  have h := checkLog_sound (w := (32375496417 / 4032375496417)) (n := 12)
    (lo := (16058123 / 1000000000)) (hi := (4014531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2032375496417 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2032375496417 / 2000000000000) = 1/(250000000000 / 2032375496417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2095499663 / 1000000000) (2095499667 / 1000000000) (Real.log (2032375496417 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2032375496417 / 250000000000) = -Real.log (250000000000 / 2032375496417) := by
    rw [show ((2032375496417 / 250000000000) : ℝ) = ((250000000000 / 2032375496417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219
