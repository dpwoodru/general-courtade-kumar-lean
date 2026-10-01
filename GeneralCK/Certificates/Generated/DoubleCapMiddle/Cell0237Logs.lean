import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0237
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

theorem reflection_log_1_neg : (62225667 / 250000000) ≤ -Real.log (5120 / 6567) ∧
    -Real.log (5120 / 6567) ≤ (248902669 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 11687)) (n := 12)
    (lo := (62225667 / 250000000)) (hi := (248902669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6567 / 5120) = 1/(5120 / 6567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62225667 / 250000000) (248902669 / 1000000000) (Real.log (6567 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6567 / 5120) = -Real.log (5120 / 6567) := by
    rw [show ((6567 / 5120) : ℝ) = ((5120 / 6567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41518209 / 125000000) ≤ -Real.log (3673 / 5120) ∧
    -Real.log (3673 / 5120) ≤ (332145673 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 8793)) (n := 12)
    (lo := (41518209 / 125000000)) (hi := (332145673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3673) = 1/(3673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332145673 / 1000000000) (-41518209 / 125000000) (Real.log (3673 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (124222867 / 500000000) ≤ -Real.log (1280 / 1641) ∧
    -Real.log (1280 / 1641) ≤ (49689147 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2921)) (n := 12)
    (lo := (124222867 / 500000000)) (hi := (49689147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1280) = 1/(1280 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (124222867 / 500000000) (49689147 / 200000000) (Real.log (1641 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1641 / 1280) = -Real.log (1280 / 1641) := by
    rw [show ((1641 / 1280) : ℝ) = ((1280 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (165664617 / 500000000) ≤ -Real.log (919 / 1280) ∧
    -Real.log (919 / 1280) ≤ (66265847 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2199)) (n := 12)
    (lo := (165664617 / 500000000)) (hi := (66265847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 919) = 1/(919 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-66265847 / 200000000) (-165664617 / 500000000) (Real.log (919 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (448035573 / 1000000000) ≤ -Real.log (2560 / 4007) ∧
    -Real.log (2560 / 4007) ≤ (224017787 / 500000000) := by
  have h := checkLog_sound (w := (1447 / 6567)) (n := 12)
    (lo := (448035573 / 1000000000)) (hi := (224017787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4007 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4007 / 2560) = 1/(2560 / 4007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (448035573 / 1000000000) (224017787 / 500000000) (Real.log (4007 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4007 / 2560) = -Real.log (2560 / 4007) := by
    rw [show ((4007 / 2560) : ℝ) = ((2560 / 4007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166589637 / 200000000) ≤ -Real.log (1113 / 2560) ∧
    -Real.log (1113 / 2560) ≤ (832948187 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2393)) (n := 12)
    (lo := (27960201 / 200000000)) (hi := (69900503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1113) = 1/(1113 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-832948187 / 1000000000) (-166589637 / 200000000) (Real.log (1113 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (223643301 / 500000000) ≤ -Real.log (640 / 1001) ∧
    -Real.log (640 / 1001) ≤ (447286603 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 1641)) (n := 12)
    (lo := (223643301 / 500000000)) (hi := (447286603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1001 / 640) = 1/(640 / 1001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (223643301 / 500000000) (447286603 / 1000000000) (Real.log (1001 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1001 / 640) = -Real.log (640 / 1001) := by
    rw [show ((1001 / 640) : ℝ) = ((640 / 1001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (830256393 / 1000000000) ≤ -Real.log (279 / 640) ∧
    -Real.log (279 / 640) ≤ (166051279 / 200000000) := by
  have h := checkLog_sound (w := (41 / 599)) (n := 12)
    (lo := (137109213 / 1000000000)) (hi := (68554607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 279) = 1/(279 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-166051279 / 200000000) (-830256393 / 1000000000) (Real.log (279 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340028761 / 1000000000) ≤ -Real.log (250000 / 351247) ∧
    -Real.log (250000 / 351247) ≤ (170014381 / 500000000) := by
  have h := checkLog_sound (w := (101247 / 601247)) (n := 12)
    (lo := (340028761 / 1000000000)) (hi := (170014381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351247 / 250000) = 1/(250000 / 351247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340028761 / 1000000000) (170014381 / 500000000) (Real.log (351247 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (351247 / 250000) = -Real.log (250000 / 351247) := by
    rw [show ((351247 / 250000) : ℝ) = ((250000 / 351247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (103834741 / 200000000) ≤ -Real.log (148753 / 250000) ∧
    -Real.log (148753 / 250000) ≤ (259586853 / 500000000) := by
  have h := checkLog_sound (w := (101247 / 398753)) (n := 12)
    (lo := (103834741 / 200000000)) (hi := (259586853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148753) = 1/(148753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-259586853 / 500000000) (-103834741 / 200000000) (Real.log (148753 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68129843 / 200000000) ≤ -Real.log (50000 / 70293) ∧
    -Real.log (50000 / 70293) ≤ (1330661 / 3906250) := by
  have h := checkLog_sound (w := (20293 / 120293)) (n := 12)
    (lo := (68129843 / 200000000)) (hi := (1330661 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70293 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70293 / 50000) = 1/(50000 / 70293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68129843 / 200000000) (1330661 / 3906250) (Real.log (70293 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (70293 / 50000) = -Real.log (50000 / 70293) := by
    rw [show ((70293 / 50000) : ℝ) = ((50000 / 70293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (520640297 / 1000000000) ≤ -Real.log (29707 / 50000) ∧
    -Real.log (29707 / 50000) ≤ (260320149 / 500000000) := by
  have h := checkLog_sound (w := (20293 / 79707)) (n := 12)
    (lo := (520640297 / 1000000000)) (hi := (260320149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 29707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 29707) = 1/(29707 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-260320149 / 500000000) (-520640297 / 1000000000) (Real.log (29707 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (262341187 / 1000000000) ≤ -Real.log (100000 / 129997) ∧
    -Real.log (100000 / 129997) ≤ (65585297 / 250000000) := by
  have h := checkLog_sound (w := (29997 / 229997)) (n := 12)
    (lo := (262341187 / 1000000000)) (hi := (65585297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129997 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129997 / 100000) = 1/(100000 / 129997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (262341187 / 1000000000) (65585297 / 250000000) (Real.log (129997 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (129997 / 100000) = -Real.log (100000 / 129997) := by
    rw [show ((129997 / 100000) : ℝ) = ((100000 / 129997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (356632087 / 1000000000) ≤ -Real.log (70003 / 100000) ∧
    -Real.log (70003 / 100000) ≤ (44579011 / 125000000) := by
  have h := checkLog_sound (w := (29997 / 170003)) (n := 12)
    (lo := (356632087 / 1000000000)) (hi := (44579011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 70003) = 1/(70003 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-44579011 / 125000000) (-356632087 / 1000000000) (Real.log (70003 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131442833 / 500000000) ≤ -Real.log (500000 / 650339) ∧
    -Real.log (500000 / 650339) ≤ (262885667 / 1000000000) := by
  have h := checkLog_sound (w := (150339 / 1150339)) (n := 12)
    (lo := (131442833 / 500000000)) (hi := (262885667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650339 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650339 / 500000) = 1/(500000 / 650339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131442833 / 500000000) (262885667 / 1000000000) (Real.log (650339 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (650339 / 500000) = -Real.log (500000 / 650339) := by
    rw [show ((650339 / 500000) : ℝ) = ((500000 / 650339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22352749 / 62500000) ≤ -Real.log (349661 / 500000) ∧
    -Real.log (349661 / 500000) ≤ (71528797 / 200000000) := by
  have h := checkLog_sound (w := (150339 / 849661)) (n := 12)
    (lo := (22352749 / 62500000)) (hi := (71528797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 349661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 349661) = 1/(349661 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-71528797 / 200000000) (-22352749 / 62500000) (Real.log (349661 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (429601233 / 500000000) ≤ -Real.log (500000000000 / 1180638373679) ∧
    -Real.log (500000000000 / 1180638373679) ≤ (214800617 / 250000000) := by
  have h := checkLog_sound (w := (180638373679 / 2180638373679)) (n := 12)
    (lo := (83027643 / 500000000)) (hi := (166055287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180638373679 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1180638373679 / 1000000000000) = 1/(500000000000 / 1180638373679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (429601233 / 500000000) (214800617 / 250000000) (Real.log (1180638373679 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1180638373679 / 500000000000) = -Real.log (500000000000 / 1180638373679) := by
    rw [show ((1180638373679 / 500000000000) : ℝ) = ((500000000000 / 1180638373679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (861289511 / 1000000000) ≤ -Real.log (50000000000 / 118310499209) ∧
    -Real.log (50000000000 / 118310499209) ≤ (861289513 / 1000000000) := by
  have h := checkLog_sound (w := (18310499209 / 218310499209)) (n := 12)
    (lo := (168142331 / 1000000000)) (hi := (42035583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118310499209 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118310499209 / 100000000000) = 1/(50000000000 / 118310499209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (861289511 / 1000000000) (861289513 / 1000000000) (Real.log (118310499209 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118310499209 / 50000000000) = -Real.log (50000000000 / 118310499209) := by
    rw [show ((118310499209 / 50000000000) : ℝ) = ((50000000000 / 118310499209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309486637 / 500000000) ≤ -Real.log (100000000000 / 185702041341) ∧
    -Real.log (100000000000 / 185702041341) ≤ (24758931 / 40000000) := by
  have h := checkLog_sound (w := (85702041341 / 285702041341)) (n := 12)
    (lo := (309486637 / 500000000)) (hi := (24758931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185702041341 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185702041341 / 100000000000) = 1/(100000000000 / 185702041341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309486637 / 500000000) (24758931 / 40000000) (Real.log (185702041341 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (185702041341 / 100000000000) = -Real.log (100000000000 / 185702041341) := by
    rw [show ((185702041341 / 100000000000) : ℝ) = ((100000000000 / 185702041341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (620529651 / 1000000000) ≤ -Real.log (500000000000 / 929956443527) ∧
    -Real.log (500000000000 / 929956443527) ≤ (155132413 / 250000000) := by
  have h := checkLog_sound (w := (429956443527 / 1429956443527)) (n := 12)
    (lo := (620529651 / 1000000000)) (hi := (155132413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929956443527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929956443527 / 500000000000) = 1/(500000000000 / 929956443527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (620529651 / 1000000000) (155132413 / 250000000) (Real.log (929956443527 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (929956443527 / 500000000000) = -Real.log (500000000000 / 929956443527) := by
    rw [show ((929956443527 / 500000000000) : ℝ) = ((500000000000 / 929956443527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0237
