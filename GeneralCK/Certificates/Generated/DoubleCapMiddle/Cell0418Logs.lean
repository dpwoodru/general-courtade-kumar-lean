import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0418
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

theorem reflection_log_1_neg : (97950407 / 500000000) ≤ -Real.log (1280 / 1557) ∧
    -Real.log (1280 / 1557) ≤ (39180163 / 200000000) := by
  have h := checkLog_sound (w := (277 / 2837)) (n := 12)
    (lo := (97950407 / 500000000)) (hi := (39180163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557 / 1280) = 1/(1280 / 1557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97950407 / 500000000) (39180163 / 200000000) (Real.log (1557 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1557 / 1280) = -Real.log (1280 / 1557) := by
    rw [show ((1557 / 1280) : ℝ) = ((1280 / 1557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30483071 / 125000000) ≤ -Real.log (1003 / 1280) ∧
    -Real.log (1003 / 1280) ≤ (243864569 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2283)) (n := 12)
    (lo := (30483071 / 125000000)) (hi := (243864569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1003) = 1/(1003 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-243864569 / 1000000000) (-30483071 / 125000000) (Real.log (1003 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97829969 / 500000000) ≤ -Real.log (10240 / 12453) ∧
    -Real.log (10240 / 12453) ≤ (195659939 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 22693)) (n := 12)
    (lo := (97829969 / 500000000)) (hi := (195659939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12453 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12453 / 10240) = 1/(10240 / 12453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97829969 / 500000000) (195659939 / 1000000000) (Real.log (12453 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12453 / 10240) = -Real.log (10240 / 12453) := by
    rw [show ((12453 / 10240) : ℝ) = ((10240 / 12453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6087269 / 25000000) ≤ -Real.log (8027 / 10240) ∧
    -Real.log (8027 / 10240) ≤ (243490761 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 18267)) (n := 12)
    (lo := (6087269 / 25000000)) (hi := (243490761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8027) = 1/(8027 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-243490761 / 1000000000) (-6087269 / 25000000) (Real.log (8027 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71927859 / 200000000) ≤ -Real.log (640 / 917) ∧
    -Real.log (640 / 917) ≤ (1404841 / 3906250) := by
  have h := checkLog_sound (w := (277 / 1557)) (n := 12)
    (lo := (71927859 / 200000000)) (hi := (1404841 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917 / 640) = 1/(640 / 917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71927859 / 200000000) (1404841 / 3906250) (Real.log (917 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (917 / 640) = -Real.log (640 / 917) := by
    rw [show ((917 / 640) : ℝ) = ((640 / 917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283532671 / 500000000) ≤ -Real.log (363 / 640) ∧
    -Real.log (363 / 640) ≤ (567065343 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1003)) (n := 12)
    (lo := (283532671 / 500000000)) (hi := (567065343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 363) = 1/(363 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-567065343 / 1000000000) (-283532671 / 500000000) (Real.log (363 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (35923027 / 100000000) ≤ -Real.log (5120 / 7333) ∧
    -Real.log (5120 / 7333) ≤ (359230271 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 12453)) (n := 12)
    (lo := (35923027 / 100000000)) (hi := (359230271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7333 / 5120) = 1/(5120 / 7333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (35923027 / 100000000) (359230271 / 1000000000) (Real.log (7333 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7333 / 5120) = -Real.log (5120 / 7333) := by
    rw [show ((7333 / 5120) : ℝ) = ((5120 / 7333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (566032817 / 1000000000) ≤ -Real.log (2907 / 5120) ∧
    -Real.log (2907 / 5120) ≤ (283016409 / 500000000) := by
  have h := checkLog_sound (w := (2213 / 8027)) (n := 12)
    (lo := (566032817 / 1000000000)) (hi := (283016409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2907) = 1/(2907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-283016409 / 500000000) (-566032817 / 1000000000) (Real.log (2907 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4197857 / 15625000) ≤ -Real.log (500000 / 654107) ∧
    -Real.log (500000 / 654107) ≤ (268662849 / 1000000000) := by
  have h := checkLog_sound (w := (154107 / 1154107)) (n := 12)
    (lo := (4197857 / 15625000)) (hi := (268662849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654107 / 500000) = 1/(500000 / 654107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4197857 / 15625000) (268662849 / 1000000000) (Real.log (654107 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (654107 / 500000) = -Real.log (500000 / 654107) := by
    rw [show ((654107 / 500000) : ℝ) = ((500000 / 654107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (368478619 / 1000000000) ≤ -Real.log (345893 / 500000) ∧
    -Real.log (345893 / 500000) ≤ (18423931 / 50000000) := by
  have h := checkLog_sound (w := (154107 / 845893)) (n := 12)
    (lo := (368478619 / 1000000000)) (hi := (18423931 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 345893) = 1/(345893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18423931 / 50000000) (-368478619 / 1000000000) (Real.log (345893 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26898843 / 100000000) ≤ -Real.log (6250 / 8179) ∧
    -Real.log (6250 / 8179) ≤ (268988431 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 14429)) (n := 12)
    (lo := (26898843 / 100000000)) (hi := (268988431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8179 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8179 / 6250) = 1/(6250 / 8179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26898843 / 100000000) (268988431 / 1000000000) (Real.log (8179 / 6250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (8179 / 6250) = -Real.log (6250 / 8179) := by
    rw [show ((8179 / 6250) : ℝ) = ((6250 / 8179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184547303 / 500000000) ≤ -Real.log (4321 / 6250) ∧
    -Real.log (4321 / 6250) ≤ (369094607 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 10571)) (n := 12)
    (lo := (184547303 / 500000000)) (hi := (369094607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4321) = 1/(4321 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-369094607 / 1000000000) (-184547303 / 500000000) (Real.log (4321 / 6250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (100991417 / 500000000) ≤ -Real.log (1000000 / 1223827) ∧
    -Real.log (1000000 / 1223827) ≤ (40396567 / 200000000) := by
  have h := checkLog_sound (w := (223827 / 2223827)) (n := 12)
    (lo := (100991417 / 500000000)) (hi := (40396567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223827 / 1000000) = 1/(1000000 / 1223827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (100991417 / 500000000) (40396567 / 200000000) (Real.log (1223827 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1223827 / 1000000) = -Real.log (1000000 / 1223827) := by
    rw [show ((1223827 / 1000000) : ℝ) = ((1000000 / 1223827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (50675969 / 200000000) ≤ -Real.log (776173 / 1000000) ∧
    -Real.log (776173 / 1000000) ≤ (126689923 / 500000000) := by
  have h := checkLog_sound (w := (223827 / 1776173)) (n := 12)
    (lo := (50675969 / 200000000)) (hi := (126689923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776173) = 1/(776173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-126689923 / 500000000) (-50675969 / 200000000) (Real.log (776173 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (25281147 / 125000000) ≤ -Real.log (1000000 / 1224153) ∧
    -Real.log (1000000 / 1224153) ≤ (202249177 / 1000000000) := by
  have h := checkLog_sound (w := (224153 / 2224153)) (n := 12)
    (lo := (25281147 / 125000000)) (hi := (202249177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224153 / 1000000) = 1/(1000000 / 1224153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (25281147 / 125000000) (202249177 / 1000000000) (Real.log (1224153 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1224153 / 1000000) = -Real.log (1000000 / 1224153) := by
    rw [show ((1224153 / 1000000) : ℝ) = ((1000000 / 1224153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253799943 / 1000000000) ≤ -Real.log (775847 / 1000000) ∧
    -Real.log (775847 / 1000000) ≤ (31724993 / 125000000) := by
  have h := checkLog_sound (w := (224153 / 1775847)) (n := 12)
    (lo := (253799943 / 1000000000)) (hi := (31724993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775847) = 1/(775847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-31724993 / 125000000) (-253799943 / 1000000000) (Real.log (775847 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (637141467 / 1000000000) ≤ -Real.log (25000000000 / 47276686721) ∧
    -Real.log (25000000000 / 47276686721) ≤ (159285367 / 250000000) := by
  have h := checkLog_sound (w := (22276686721 / 72276686721)) (n := 12)
    (lo := (637141467 / 1000000000)) (hi := (159285367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47276686721 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47276686721 / 25000000000) = 1/(25000000000 / 47276686721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (637141467 / 1000000000) (159285367 / 250000000) (Real.log (47276686721 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (47276686721 / 25000000000) = -Real.log (25000000000 / 47276686721) := by
    rw [show ((47276686721 / 25000000000) : ℝ) = ((25000000000 / 47276686721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (159520759 / 250000000) ≤ -Real.log (125000000000 / 236606109697) ∧
    -Real.log (125000000000 / 236606109697) ≤ (638083037 / 1000000000) := by
  have h := checkLog_sound (w := (111606109697 / 361606109697)) (n := 12)
    (lo := (159520759 / 250000000)) (hi := (638083037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236606109697 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236606109697 / 125000000000) = 1/(125000000000 / 236606109697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (159520759 / 250000000) (638083037 / 1000000000) (Real.log (236606109697 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (236606109697 / 125000000000) = -Real.log (125000000000 / 236606109697) := by
    rw [show ((236606109697 / 125000000000) : ℝ) = ((125000000000 / 236606109697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (455362679 / 1000000000) ≤ -Real.log (20000000000 / 31534902657) ∧
    -Real.log (20000000000 / 31534902657) ≤ (11384067 / 25000000) := by
  have h := checkLog_sound (w := (11534902657 / 51534902657)) (n := 12)
    (lo := (455362679 / 1000000000)) (hi := (11384067 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31534902657 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31534902657 / 20000000000) = 1/(20000000000 / 31534902657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (455362679 / 1000000000) (11384067 / 25000000) (Real.log (31534902657 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31534902657 / 20000000000) = -Real.log (20000000000 / 31534902657) := by
    rw [show ((31534902657 / 20000000000) : ℝ) = ((20000000000 / 31534902657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (456049119 / 1000000000) ≤ -Real.log (250000000000 / 394456961231) ∧
    -Real.log (250000000000 / 394456961231) ≤ (2850307 / 6250000) := by
  have h := checkLog_sound (w := (144456961231 / 644456961231)) (n := 12)
    (lo := (456049119 / 1000000000)) (hi := (2850307 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394456961231 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394456961231 / 250000000000) = 1/(250000000000 / 394456961231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (456049119 / 1000000000) (2850307 / 6250000) (Real.log (394456961231 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (394456961231 / 250000000000) = -Real.log (250000000000 / 394456961231) := by
    rw [show ((394456961231 / 250000000000) : ℝ) = ((250000000000 / 394456961231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0418
