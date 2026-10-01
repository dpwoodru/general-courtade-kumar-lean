import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0076
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

theorem reflection_log_1_neg : (176674553 / 500000000) ≤ -Real.log (512 / 729) ∧
    -Real.log (512 / 729) ≤ (353349107 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1241)) (n := 12)
    (lo := (176674553 / 500000000)) (hi := (353349107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 512) = 1/(512 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (176674553 / 500000000) (353349107 / 1000000000) (Real.log (729 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (729 / 512) = -Real.log (512 / 729) := by
    rw [show ((729 / 512) : ℝ) = ((512 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (137837317 / 250000000) ≤ -Real.log (295 / 512) ∧
    -Real.log (295 / 512) ≤ (551349269 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 807)) (n := 12)
    (lo := (137837317 / 250000000)) (hi := (551349269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 295) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 295) = 1/(295 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-551349269 / 1000000000) (-137837317 / 250000000) (Real.log (295 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (176262861 / 500000000) ≤ -Real.log (1280 / 1821) ∧
    -Real.log (1280 / 1821) ≤ (352525723 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3101)) (n := 12)
    (lo := (176262861 / 500000000)) (hi := (352525723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1821 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1821 / 1280) = 1/(1280 / 1821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (176262861 / 500000000) (352525723 / 1000000000) (Real.log (1821 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1821 / 1280) = -Real.log (1280 / 1821) := by
    rw [show ((1821 / 1280) : ℝ) = ((1280 / 1821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (109863487 / 200000000) ≤ -Real.log (739 / 1280) ∧
    -Real.log (739 / 1280) ≤ (137329359 / 250000000) := by
  have h := checkLog_sound (w := (541 / 2019)) (n := 12)
    (lo := (109863487 / 200000000)) (hi := (137329359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 739) = 1/(739 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137329359 / 250000000) (-109863487 / 200000000) (Real.log (739 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76739743 / 125000000) ≤ -Real.log (256 / 473) ∧
    -Real.log (256 / 473) ≤ (122783589 / 200000000) := by
  have h := checkLog_sound (w := (217 / 729)) (n := 12)
    (lo := (76739743 / 125000000)) (hi := (122783589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473 / 256) = 1/(256 / 473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76739743 / 125000000) (122783589 / 200000000) (Real.log (473 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (473 / 256) = -Real.log (256 / 473) := by
    rw [show ((473 / 256) : ℝ) = ((256 / 473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1881615797 / 1000000000) ≤ -Real.log (39 / 256) ∧
    -Real.log (39 / 256) ≤ (9408079 / 5000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 39) = 1/(39 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9408079 / 5000000) (-1881615797 / 1000000000) (Real.log (39 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (612648639 / 1000000000) ≤ -Real.log (640 / 1181) ∧
    -Real.log (640 / 1181) ≤ (1914527 / 3125000) := by
  have h := checkLog_sound (w := (541 / 1821)) (n := 12)
    (lo := (612648639 / 1000000000)) (hi := (1914527 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 640) = 1/(640 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (612648639 / 1000000000) (1914527 / 3125000) (Real.log (1181 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1181 / 640) = -Real.log (640 / 1181) := by
    rw [show ((1181 / 640) : ℝ) = ((640 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (74653933 / 40000000) ≤ -Real.log (99 / 640) ∧
    -Real.log (99 / 640) ≤ (233293541 / 125000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 99) = 1/(99 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-233293541 / 125000000) (-74653933 / 40000000) (Real.log (99 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (242706521 / 500000000) ≤ -Real.log (500000 / 812423) ∧
    -Real.log (500000 / 812423) ≤ (485413043 / 1000000000) := by
  have h := checkLog_sound (w := (312423 / 1312423)) (n := 12)
    (lo := (242706521 / 500000000)) (hi := (485413043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812423 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812423 / 500000) = 1/(500000 / 812423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (242706521 / 500000000) (485413043 / 1000000000) (Real.log (812423 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (812423 / 500000) = -Real.log (500000 / 812423) := by
    rw [show ((812423 / 500000) : ℝ) = ((500000 / 812423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98041867 / 100000000) ≤ -Real.log (187577 / 500000) ∧
    -Real.log (187577 / 500000) ≤ (61276167 / 62500000) := by
  have h := checkLog_sound (w := (62423 / 437577)) (n := 12)
    (lo := (28727149 / 100000000)) (hi := (287271491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 187577) = 1/(187577 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-61276167 / 62500000) (-98041867 / 100000000) (Real.log (187577 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9732679 / 20000000) ≤ -Real.log (1000000 / 1626831) ∧
    -Real.log (1000000 / 1626831) ≤ (486633951 / 1000000000) := by
  have h := checkLog_sound (w := (626831 / 2626831)) (n := 12)
    (lo := (9732679 / 20000000)) (hi := (486633951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626831 / 1000000) = 1/(1000000 / 1626831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9732679 / 20000000) (486633951 / 1000000000) (Real.log (1626831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1626831 / 1000000) = -Real.log (1000000 / 1626831) := by
    rw [show ((1626831 / 1000000) : ℝ) = ((1000000 / 1626831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (492861939 / 500000000) ≤ -Real.log (373169 / 1000000) ∧
    -Real.log (373169 / 1000000) ≤ (24643097 / 25000000) := by
  have h := checkLog_sound (w := (126831 / 873169)) (n := 12)
    (lo := (146288349 / 500000000)) (hi := (292576699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373169) = 1/(373169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24643097 / 25000000) (-492861939 / 500000000) (Real.log (373169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (402028543 / 1000000000) ≤ -Real.log (500000 / 747427) ∧
    -Real.log (500000 / 747427) ≤ (785212 / 1953125) := by
  have h := checkLog_sound (w := (247427 / 1247427)) (n := 12)
    (lo := (402028543 / 1000000000)) (hi := (785212 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747427 / 500000) = 1/(500000 / 747427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (402028543 / 1000000000) (785212 / 1953125) (Real.log (747427 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (747427 / 500000) = -Real.log (500000 / 747427) := by
    rw [show ((747427 / 500000) : ℝ) = ((500000 / 747427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (341453891 / 500000000) ≤ -Real.log (252573 / 500000) ∧
    -Real.log (252573 / 500000) ≤ (682907783 / 1000000000) := by
  have h := checkLog_sound (w := (247427 / 752573)) (n := 12)
    (lo := (341453891 / 500000000)) (hi := (682907783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 252573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 252573) = 1/(252573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-682907783 / 1000000000) (-341453891 / 500000000) (Real.log (252573 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (403328827 / 1000000000) ≤ -Real.log (1000000 / 1496799) ∧
    -Real.log (1000000 / 1496799) ≤ (100832207 / 250000000) := by
  have h := checkLog_sound (w := (496799 / 2496799)) (n := 12)
    (lo := (403328827 / 1000000000)) (hi := (100832207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1496799 / 1000000) = 1/(1000000 / 1496799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (403328827 / 1000000000) (100832207 / 250000000) (Real.log (1496799 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1496799 / 1000000) = -Real.log (1000000 / 1496799) := by
    rw [show ((1496799 / 1000000) : ℝ) = ((1000000 / 1496799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (343382793 / 500000000) ≤ -Real.log (503201 / 1000000) ∧
    -Real.log (503201 / 1000000) ≤ (686765587 / 1000000000) := by
  have h := checkLog_sound (w := (496799 / 1503201)) (n := 12)
    (lo := (343382793 / 500000000)) (hi := (686765587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 503201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 503201) = 1/(503201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-686765587 / 1000000000) (-343382793 / 500000000) (Real.log (503201 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1465831711 / 1000000000) ≤ -Real.log (62500000000 / 270696500637) ∧
    -Real.log (62500000000 / 270696500637) ≤ (732915857 / 500000000) := by
  have h := checkLog_sound (w := (20696500637 / 520696500637)) (n := 12)
    (lo := (79537351 / 1000000000)) (hi := (9942169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270696500637 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(270696500637 / 250000000000) = 1/(62500000000 / 270696500637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1465831711 / 1000000000) (732915857 / 500000000) (Real.log (270696500637 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (270696500637 / 62500000000) = -Real.log (62500000000 / 270696500637) := by
    rw [show ((270696500637 / 62500000000) : ℝ) = ((62500000000 / 270696500637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (368089457 / 250000000) ≤ -Real.log (250000000000 / 1089875498769) ∧
    -Real.log (250000000000 / 1089875498769) ≤ (1472357831 / 1000000000) := by
  have h := checkLog_sound (w := (89875498769 / 2089875498769)) (n := 12)
    (lo := (21515867 / 250000000)) (hi := (86063469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089875498769 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1089875498769 / 1000000000000) = 1/(250000000000 / 1089875498769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (368089457 / 250000000) (1472357831 / 1000000000) (Real.log (1089875498769 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1089875498769 / 250000000000) = -Real.log (250000000000 / 1089875498769) := by
    rw [show ((1089875498769 / 250000000000) : ℝ) = ((250000000000 / 1089875498769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43397453 / 40000000) ≤ -Real.log (250000000000 / 739812846187) ∧
    -Real.log (250000000000 / 739812846187) ≤ (1084936327 / 1000000000) := by
  have h := checkLog_sound (w := (239812846187 / 1239812846187)) (n := 12)
    (lo := (78357829 / 200000000)) (hi := (195894573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739812846187 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(739812846187 / 500000000000) = 1/(250000000000 / 739812846187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (43397453 / 40000000) (1084936327 / 1000000000) (Real.log (739812846187 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (739812846187 / 250000000000) = -Real.log (250000000000 / 739812846187) := by
    rw [show ((739812846187 / 250000000000) : ℝ) = ((250000000000 / 739812846187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1090094413 / 1000000000) ≤ -Real.log (500000000000 / 1487277449767) ∧
    -Real.log (500000000000 / 1487277449767) ≤ (218018883 / 200000000) := by
  have h := checkLog_sound (w := (487277449767 / 2487277449767)) (n := 12)
    (lo := (396947233 / 1000000000)) (hi := (198473617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487277449767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1487277449767 / 1000000000000) = 1/(500000000000 / 1487277449767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1090094413 / 1000000000) (218018883 / 200000000) (Real.log (1487277449767 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1487277449767 / 500000000000) = -Real.log (500000000000 / 1487277449767) := by
    rw [show ((1487277449767 / 500000000000) : ℝ) = ((500000000000 / 1487277449767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0076
