import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0262
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

theorem reflection_log_1_neg : (23741621 / 100000000) ≤ -Real.log (1280 / 1623) ∧
    -Real.log (1280 / 1623) ≤ (237416211 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 2903)) (n := 12)
    (lo := (23741621 / 100000000)) (hi := (237416211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623 / 1280) = 1/(1280 / 1623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23741621 / 100000000) (237416211 / 1000000000) (Real.log (1623 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1623 / 1280) = -Real.log (1280 / 1623) := by
    rw [show ((1623 / 1280) : ℝ) = ((1280 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155966037 / 500000000) ≤ -Real.log (937 / 1280) ∧
    -Real.log (937 / 1280) ≤ (12477283 / 40000000) := by
  have h := checkLog_sound (w := (343 / 2217)) (n := 12)
    (lo := (155966037 / 500000000)) (hi := (12477283 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 937) = 1/(937 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) (Real.log (937 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59238499 / 250000000) ≤ -Real.log (5120 / 6489) ∧
    -Real.log (5120 / 6489) ≤ (236953997 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 11609)) (n := 12)
    (lo := (59238499 / 250000000)) (hi := (236953997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6489 / 5120) = 1/(5120 / 6489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59238499 / 250000000) (236953997 / 1000000000) (Real.log (6489 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6489 / 5120) = -Real.log (5120 / 6489) := by
    rw [show ((6489 / 5120) : ℝ) = ((5120 / 6489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (311131967 / 1000000000) ≤ -Real.log (3751 / 5120) ∧
    -Real.log (3751 / 5120) ≤ (4861437 / 15625000) := by
  have h := checkLog_sound (w := (1369 / 8871)) (n := 12)
    (lo := (311131967 / 1000000000)) (hi := (4861437 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3751) = 1/(3751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4861437 / 15625000) (-311131967 / 1000000000) (Real.log (3751 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (429140943 / 1000000000) ≤ -Real.log (640 / 983) ∧
    -Real.log (640 / 983) ≤ (26821309 / 62500000) := by
  have h := checkLog_sound (w := (343 / 1623)) (n := 12)
    (lo := (429140943 / 1000000000)) (hi := (26821309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 640) = 1/(640 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (429140943 / 1000000000) (26821309 / 62500000) (Real.log (983 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (983 / 640) = -Real.log (640 / 983) := by
    rw [show ((983 / 640) : ℝ) = ((640 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (191934009 / 250000000) ≤ -Real.log (297 / 640) ∧
    -Real.log (297 / 640) ≤ (383868019 / 500000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 297) = 1/(297 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) (Real.log (297 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214188841 / 500000000) ≤ -Real.log (2560 / 3929) ∧
    -Real.log (2560 / 3929) ≤ (428377683 / 1000000000) := by
  have h := checkLog_sound (w := (1369 / 6489)) (n := 12)
    (lo := (214188841 / 500000000)) (hi := (428377683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3929 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3929 / 2560) = 1/(2560 / 3929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214188841 / 500000000) (428377683 / 1000000000) (Real.log (3929 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3929 / 2560) = -Real.log (2560 / 3929) := by
    rw [show ((3929 / 2560) : ℝ) = ((2560 / 3929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (765213967 / 1000000000) ≤ -Real.log (1191 / 2560) ∧
    -Real.log (1191 / 2560) ≤ (765213969 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 2471)) (n := 12)
    (lo := (72066787 / 1000000000)) (hi := (18016697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1191) = 1/(1191 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-765213969 / 1000000000) (-765213967 / 1000000000) (Real.log (1191 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (324455321 / 1000000000) ≤ -Real.log (1000000 / 1383277) ∧
    -Real.log (1000000 / 1383277) ≤ (162227661 / 500000000) := by
  have h := checkLog_sound (w := (383277 / 2383277)) (n := 12)
    (lo := (324455321 / 1000000000)) (hi := (162227661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1383277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1383277 / 1000000) = 1/(1000000 / 1383277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (324455321 / 1000000000) (162227661 / 500000000) (Real.log (1383277 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1383277 / 1000000) = -Real.log (1000000 / 1383277) := by
    rw [show ((1383277 / 1000000) : ℝ) = ((1000000 / 1383277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (241667651 / 500000000) ≤ -Real.log (616723 / 1000000) ∧
    -Real.log (616723 / 1000000) ≤ (483335303 / 1000000000) := by
  have h := checkLog_sound (w := (383277 / 1616723)) (n := 12)
    (lo := (241667651 / 500000000)) (hi := (483335303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 616723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 616723) = 1/(616723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-483335303 / 1000000000) (-241667651 / 500000000) (Real.log (616723 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162540949 / 500000000) ≤ -Real.log (62500 / 86509) ∧
    -Real.log (62500 / 86509) ≤ (325081899 / 1000000000) := by
  have h := checkLog_sound (w := (24009 / 149009)) (n := 12)
    (lo := (162540949 / 500000000)) (hi := (325081899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86509 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86509 / 62500) = 1/(62500 / 86509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162540949 / 500000000) (325081899 / 1000000000) (Real.log (86509 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (86509 / 62500) = -Real.log (62500 / 86509) := by
    rw [show ((86509 / 62500) : ℝ) = ((62500 / 86509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (484742109 / 1000000000) ≤ -Real.log (38491 / 62500) ∧
    -Real.log (38491 / 62500) ≤ (48474211 / 100000000) := by
  have h := checkLog_sound (w := (24009 / 100991)) (n := 12)
    (lo := (484742109 / 1000000000)) (hi := (48474211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 38491) = 1/(38491 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48474211 / 100000000) (-484742109 / 1000000000) (Real.log (38491 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (248805839 / 1000000000) ≤ -Real.log (1000000 / 1282493) ∧
    -Real.log (1000000 / 1282493) ≤ (3110073 / 12500000) := by
  have h := checkLog_sound (w := (282493 / 2282493)) (n := 12)
    (lo := (248805839 / 1000000000)) (hi := (3110073 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282493 / 1000000) = 1/(1000000 / 1282493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (248805839 / 1000000000) (3110073 / 12500000) (Real.log (1282493 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1282493 / 1000000) = -Real.log (1000000 / 1282493) := by
    rw [show ((1282493 / 1000000) : ℝ) = ((1000000 / 1282493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13278903 / 40000000) ≤ -Real.log (717507 / 1000000) ∧
    -Real.log (717507 / 1000000) ≤ (10374143 / 31250000) := by
  have h := checkLog_sound (w := (282493 / 1717507)) (n := 12)
    (lo := (13278903 / 40000000)) (hi := (10374143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717507) = 1/(717507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10374143 / 31250000) (-13278903 / 40000000) (Real.log (717507 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (249346827 / 1000000000) ≤ -Real.log (1000000 / 1283187) ∧
    -Real.log (1000000 / 1283187) ≤ (62336707 / 250000000) := by
  have h := checkLog_sound (w := (283187 / 2283187)) (n := 12)
    (lo := (249346827 / 1000000000)) (hi := (62336707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283187 / 1000000) = 1/(1000000 / 1283187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (249346827 / 1000000000) (62336707 / 250000000) (Real.log (1283187 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1283187 / 1000000) = -Real.log (1000000 / 1283187) := by
    rw [show ((1283187 / 1000000) : ℝ) = ((1000000 / 1283187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (332940281 / 1000000000) ≤ -Real.log (716813 / 1000000) ∧
    -Real.log (716813 / 1000000) ≤ (166470141 / 500000000) := by
  have h := checkLog_sound (w := (283187 / 1716813)) (n := 12)
    (lo := (332940281 / 1000000000)) (hi := (166470141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716813) = 1/(716813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-166470141 / 500000000) (-332940281 / 1000000000) (Real.log (716813 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (807790623 / 1000000000) ≤ -Real.log (250000000000 / 560736748913) ∧
    -Real.log (250000000000 / 560736748913) ≤ (258493 / 320000) := by
  have h := checkLog_sound (w := (60736748913 / 1060736748913)) (n := 12)
    (lo := (114643443 / 1000000000)) (hi := (28660861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560736748913 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(560736748913 / 500000000000) = 1/(250000000000 / 560736748913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (807790623 / 1000000000) (258493 / 320000) (Real.log (560736748913 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (560736748913 / 250000000000) = -Real.log (250000000000 / 560736748913) := by
    rw [show ((560736748913 / 250000000000) : ℝ) = ((250000000000 / 560736748913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (404912003 / 500000000) ≤ -Real.log (500000000000 / 1123756202749) ∧
    -Real.log (500000000000 / 1123756202749) ≤ (101228001 / 125000000) := by
  have h := checkLog_sound (w := (123756202749 / 2123756202749)) (n := 12)
    (lo := (58338413 / 500000000)) (hi := (116676827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123756202749 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123756202749 / 1000000000000) = 1/(500000000000 / 1123756202749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (404912003 / 500000000) (101228001 / 125000000) (Real.log (1123756202749 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1123756202749 / 500000000000) = -Real.log (500000000000 / 1123756202749) := by
    rw [show ((1123756202749 / 500000000000) : ℝ) = ((500000000000 / 1123756202749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116155683 / 200000000) ≤ -Real.log (25000000000 / 44685731289) ∧
    -Real.log (25000000000 / 44685731289) ≤ (36298651 / 62500000) := by
  have h := checkLog_sound (w := (19685731289 / 69685731289)) (n := 12)
    (lo := (116155683 / 200000000)) (hi := (36298651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44685731289 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44685731289 / 25000000000) = 1/(25000000000 / 44685731289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116155683 / 200000000) (36298651 / 62500000) (Real.log (44685731289 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44685731289 / 25000000000) = -Real.log (25000000000 / 44685731289) := by
    rw [show ((44685731289 / 25000000000) : ℝ) = ((25000000000 / 44685731289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (145571777 / 250000000) ≤ -Real.log (50000000000 / 89506398461) ∧
    -Real.log (50000000000 / 89506398461) ≤ (582287109 / 1000000000) := by
  have h := checkLog_sound (w := (39506398461 / 139506398461)) (n := 12)
    (lo := (145571777 / 250000000)) (hi := (582287109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89506398461 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89506398461 / 50000000000) = 1/(50000000000 / 89506398461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (145571777 / 250000000) (582287109 / 1000000000) (Real.log (89506398461 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (89506398461 / 50000000000) = -Real.log (50000000000 / 89506398461) := by
    rw [show ((89506398461 / 50000000000) : ℝ) = ((50000000000 / 89506398461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0262
