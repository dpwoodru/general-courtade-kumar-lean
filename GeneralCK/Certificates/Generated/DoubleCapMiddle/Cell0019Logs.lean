import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0019
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

theorem reflection_log_1_neg : (79839099 / 200000000) ≤ -Real.log (320 / 477) ∧
    -Real.log (320 / 477) ≤ (49899437 / 125000000) := by
  have h := checkLog_sound (w := (157 / 797)) (n := 12)
    (lo := (79839099 / 200000000)) (hi := (49899437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 320) = 1/(320 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (79839099 / 200000000) (49899437 / 125000000) (Real.log (477 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (477 / 320) = -Real.log (320 / 477) := by
    rw [show ((477 / 320) : ℝ) = ((320 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (337285397 / 500000000) ≤ -Real.log (163 / 320) ∧
    -Real.log (163 / 320) ≤ (134914159 / 200000000) := by
  have h := checkLog_sound (w := (157 / 483)) (n := 12)
    (lo := (337285397 / 500000000)) (hi := (134914159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 163) = 1/(163 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-134914159 / 200000000) (-337285397 / 500000000) (Real.log (163 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199204511 / 500000000) ≤ -Real.log (2560 / 3813) ∧
    -Real.log (2560 / 3813) ≤ (398409023 / 1000000000) := by
  have h := checkLog_sound (w := (1253 / 6373)) (n := 12)
    (lo := (199204511 / 500000000)) (hi := (398409023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3813 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3813 / 2560) = 1/(2560 / 3813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199204511 / 500000000) (398409023 / 1000000000) (Real.log (3813 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3813 / 2560) = -Real.log (2560 / 3813) := by
    rw [show ((3813 / 2560) : ℝ) = ((2560 / 3813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (672272823 / 1000000000) ≤ -Real.log (1307 / 2560) ∧
    -Real.log (1307 / 2560) ≤ (84034103 / 125000000) := by
  have h := checkLog_sound (w := (1253 / 3867)) (n := 12)
    (lo := (672272823 / 1000000000)) (hi := (84034103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1307) = 1/(1307 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-84034103 / 125000000) (-672272823 / 1000000000) (Real.log (1307 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (341863979 / 500000000) ≤ -Real.log (160 / 317) ∧
    -Real.log (160 / 317) ≤ (683727959 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 477)) (n := 12)
    (lo := (341863979 / 500000000)) (hi := (683727959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 160) = 1/(160 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (341863979 / 500000000) (683727959 / 1000000000) (Real.log (317 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (317 / 160) = -Real.log (160 / 317) := by
    rw [show ((317 / 160) : ℝ) = ((160 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3976561523 / 1000000000) ≤ -Real.log (3 / 160) ∧
    -Real.log (3 / 160) ≤ (3976561529 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 3) = 1/(3 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3976561529 / 1000000000) (-3976561523 / 1000000000) (Real.log (3 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (682544293 / 1000000000) ≤ -Real.log (1280 / 2533) ∧
    -Real.log (1280 / 2533) ≤ (341272147 / 500000000) := by
  have h := checkLog_sound (w := (1253 / 3813)) (n := 12)
    (lo := (682544293 / 1000000000)) (hi := (341272147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2533 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2533 / 1280) = 1/(1280 / 2533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (682544293 / 1000000000) (341272147 / 500000000) (Real.log (2533 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2533 / 1280) = -Real.log (1280 / 2533) := by
    rw [show ((2533 / 1280) : ℝ) = ((1280 / 2533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (482347311 / 125000000) ≤ -Real.log (27 / 1280) ∧
    -Real.log (27 / 1280) ≤ (1929389247 / 500000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 27) = 1/(27 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1929389247 / 500000000) (-482347311 / 125000000) (Real.log (27 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (560170491 / 1000000000) ≤ -Real.log (1000000 / 1750971) ∧
    -Real.log (1000000 / 1750971) ≤ (140042623 / 250000000) := by
  have h := checkLog_sound (w := (750971 / 2750971)) (n := 12)
    (lo := (560170491 / 1000000000)) (hi := (140042623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1750971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1750971 / 1000000) = 1/(1000000 / 1750971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (560170491 / 1000000000) (140042623 / 250000000) (Real.log (1750971 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1750971 / 1000000) = -Real.log (1000000 / 1750971) := by
    rw [show ((1750971 / 1000000) : ℝ) = ((1000000 / 1750971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (695092961 / 500000000) ≤ -Real.log (249029 / 1000000) ∧
    -Real.log (249029 / 1000000) ≤ (55607437 / 40000000) := by
  have h := checkLog_sound (w := (971 / 499029)) (n := 12)
    (lo := (1945781 / 500000000)) (hi := (3891563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249029) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 249029) = 1/(249029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-55607437 / 40000000) (-695092961 / 500000000) (Real.log (249029 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (561743237 / 1000000000) ≤ -Real.log (1000000 / 1753727) ∧
    -Real.log (1000000 / 1753727) ≤ (280871619 / 500000000) := by
  have h := checkLog_sound (w := (753727 / 2753727)) (n := 12)
    (lo := (561743237 / 1000000000)) (hi := (280871619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753727 / 1000000) = 1/(1000000 / 1753727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (561743237 / 1000000000) (280871619 / 500000000) (Real.log (1753727 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1753727 / 1000000) = -Real.log (1000000 / 1753727) := by
    rw [show ((1753727 / 1000000) : ℝ) = ((1000000 / 1753727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1401314601 / 1000000000) ≤ -Real.log (246273 / 1000000) ∧
    -Real.log (246273 / 1000000) ≤ (350328651 / 250000000) := by
  have h := checkLog_sound (w := (3727 / 496273)) (n := 12)
    (lo := (15020241 / 1000000000)) (hi := (7510121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 246273) = 1/(246273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-350328651 / 250000000) (-1401314601 / 1000000000) (Real.log (246273 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2433013 / 5000000) ≤ -Real.log (50000 / 81339) ∧
    -Real.log (50000 / 81339) ≤ (486602601 / 1000000000) := by
  have h := checkLog_sound (w := (31339 / 131339)) (n := 12)
    (lo := (2433013 / 5000000)) (hi := (486602601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81339 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81339 / 50000) = 1/(50000 / 81339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2433013 / 5000000) (486602601 / 1000000000) (Real.log (81339 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (81339 / 50000) = -Real.log (50000 / 81339) := by
    rw [show ((81339 / 50000) : ℝ) = ((50000 / 81339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49279361 / 50000000) ≤ -Real.log (18661 / 50000) ∧
    -Real.log (18661 / 50000) ≤ (492793611 / 500000000) := by
  have h := checkLog_sound (w := (6339 / 43661)) (n := 12)
    (lo := (7311001 / 25000000)) (hi := (292440041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 18661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 18661) = 1/(18661 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-492793611 / 500000000) (-49279361 / 50000000) (Real.log (18661 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (244242459 / 500000000) ≤ -Real.log (200000 / 325969) ∧
    -Real.log (200000 / 325969) ≤ (488484919 / 1000000000) := by
  have h := checkLog_sound (w := (125969 / 525969)) (n := 12)
    (lo := (244242459 / 500000000)) (hi := (488484919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325969 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325969 / 200000) = 1/(200000 / 325969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (244242459 / 500000000) (488484919 / 1000000000) (Real.log (325969 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (325969 / 200000) = -Real.log (200000 / 325969) := by
    rw [show ((325969 / 200000) : ℝ) = ((200000 / 325969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (993833441 / 1000000000) ≤ -Real.log (74031 / 200000) ∧
    -Real.log (74031 / 200000) ≤ (993833443 / 1000000000) := by
  have h := checkLog_sound (w := (25969 / 174031)) (n := 12)
    (lo := (300686261 / 1000000000)) (hi := (150343131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 74031) = 1/(74031 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-993833443 / 1000000000) (-993833441 / 1000000000) (Real.log (74031 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1950356413 / 1000000000) ≤ -Real.log (100000000000 / 703119315421) ∧
    -Real.log (100000000000 / 703119315421) ≤ (30474319 / 15625000) := by
  have h := checkLog_sound (w := (303119315421 / 1103119315421)) (n := 12)
    (lo := (564062053 / 1000000000)) (hi := (282031027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703119315421 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(703119315421 / 400000000000) = 1/(100000000000 / 703119315421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1950356413 / 1000000000) (30474319 / 15625000) (Real.log (703119315421 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703119315421 / 100000000000) = -Real.log (100000000000 / 703119315421) := by
    rw [show ((703119315421 / 100000000000) : ℝ) = ((100000000000 / 703119315421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (981528919 / 500000000) ≤ -Real.log (62500000000 / 445066805943) ∧
    -Real.log (62500000000 / 445066805943) ≤ (1963057841 / 1000000000) := by
  have h := checkLog_sound (w := (195066805943 / 695066805943)) (n := 12)
    (lo := (288381739 / 500000000)) (hi := (576763479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445066805943 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(445066805943 / 250000000000) = 1/(62500000000 / 445066805943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (981528919 / 500000000) (1963057841 / 1000000000) (Real.log (445066805943 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (445066805943 / 62500000000) = -Real.log (62500000000 / 445066805943) := by
    rw [show ((445066805943 / 62500000000) : ℝ) = ((62500000000 / 445066805943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (73609491 / 50000000) ≤ -Real.log (250000000000 / 1089692406623) ∧
    -Real.log (250000000000 / 1089692406623) ≤ (1472189823 / 1000000000) := by
  have h := checkLog_sound (w := (89692406623 / 2089692406623)) (n := 12)
    (lo := (4294773 / 50000000)) (hi := (85895461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089692406623 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1089692406623 / 1000000000000) = 1/(250000000000 / 1089692406623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (73609491 / 50000000) (1472189823 / 1000000000) (Real.log (1089692406623 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1089692406623 / 250000000000) = -Real.log (250000000000 / 1089692406623) := by
    rw [show ((1089692406623 / 250000000000) : ℝ) = ((250000000000 / 1089692406623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1482318359 / 1000000000) ≤ -Real.log (125000000000 / 550392740879) ∧
    -Real.log (125000000000 / 550392740879) ≤ (741159181 / 500000000) := by
  have h := checkLog_sound (w := (50392740879 / 1050392740879)) (n := 12)
    (lo := (96023999 / 1000000000)) (hi := (12003 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550392740879 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(550392740879 / 500000000000) = 1/(125000000000 / 550392740879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1482318359 / 1000000000) (741159181 / 500000000) (Real.log (550392740879 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (550392740879 / 125000000000) = -Real.log (125000000000 / 550392740879) := by
    rw [show ((550392740879 / 125000000000) : ℝ) = ((125000000000 / 550392740879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0019
