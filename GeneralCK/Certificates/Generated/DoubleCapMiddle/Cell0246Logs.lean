import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0246
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

theorem reflection_log_1_neg : (122391363 / 500000000) ≤ -Real.log (256 / 327) ∧
    -Real.log (256 / 327) ≤ (244782727 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 583)) (n := 12)
    (lo := (122391363 / 500000000)) (hi := (244782727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 256) = 1/(256 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (122391363 / 500000000) (244782727 / 1000000000) (Real.log (327 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (327 / 256) = -Real.log (256 / 327) := by
    rw [show ((327 / 256) : ℝ) = ((256 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (324821619 / 1000000000) ≤ -Real.log (185 / 256) ∧
    -Real.log (185 / 256) ≤ (16241081 / 50000000) := by
  have h := checkLog_sound (w := (71 / 441)) (n := 12)
    (lo := (324821619 / 1000000000)) (hi := (16241081 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 185) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 185) = 1/(185 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16241081 / 50000000) (-324821619 / 1000000000) (Real.log (185 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48864781 / 200000000) ≤ -Real.log (5120 / 6537) ∧
    -Real.log (5120 / 6537) ≤ (122161953 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 11657)) (n := 12)
    (lo := (48864781 / 200000000)) (hi := (122161953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6537 / 5120) = 1/(5120 / 6537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48864781 / 200000000) (122161953 / 500000000) (Real.log (6537 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6537 / 5120) = -Real.log (5120 / 6537) := by
    rw [show ((6537 / 5120) : ℝ) = ((5120 / 6537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (324011137 / 1000000000) ≤ -Real.log (3703 / 5120) ∧
    -Real.log (3703 / 5120) ≤ (162005569 / 500000000) := by
  have h := checkLog_sound (w := (1417 / 8823)) (n := 12)
    (lo := (324011137 / 1000000000)) (hi := (162005569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3703) = 1/(3703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-162005569 / 500000000) (-324011137 / 1000000000) (Real.log (3703 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1378983 / 3125000) ≤ -Real.log (128 / 199) ∧
    -Real.log (128 / 199) ≤ (441274561 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 128) = 1/(128 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1378983 / 3125000) (441274561 / 1000000000) (Real.log (199 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (199 / 128) = -Real.log (128 / 199) := by
    rw [show ((199 / 128) : ℝ) = ((128 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (161795799 / 200000000) ≤ -Real.log (57 / 128) ∧
    -Real.log (57 / 128) ≤ (808978997 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 57) = 1/(57 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-808978997 / 1000000000) (-161795799 / 200000000) (Real.log (57 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (440520507 / 1000000000) ≤ -Real.log (2560 / 3977) ∧
    -Real.log (2560 / 3977) ≤ (110130127 / 250000000) := by
  have h := checkLog_sound (w := (1417 / 6537)) (n := 12)
    (lo := (440520507 / 1000000000)) (hi := (110130127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3977 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3977 / 2560) = 1/(2560 / 3977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (440520507 / 1000000000) (110130127 / 250000000) (Real.log (3977 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3977 / 2560) = -Real.log (2560 / 3977) := by
    rw [show ((3977 / 2560) : ℝ) = ((2560 / 3977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (806350873 / 1000000000) ≤ -Real.log (1143 / 2560) ∧
    -Real.log (1143 / 2560) ≤ (6450807 / 8000000) := by
  have h := checkLog_sound (w := (137 / 2423)) (n := 12)
    (lo := (113203693 / 1000000000)) (hi := (56601847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1143) = 1/(1143 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6450807 / 8000000) (-806350873 / 1000000000) (Real.log (1143 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (334438741 / 1000000000) ≤ -Real.log (250000 / 349289) ∧
    -Real.log (250000 / 349289) ≤ (167219371 / 500000000) := by
  have h := checkLog_sound (w := (99289 / 599289)) (n := 12)
    (lo := (334438741 / 1000000000)) (hi := (167219371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349289 / 250000) = 1/(250000 / 349289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (334438741 / 1000000000) (167219371 / 500000000) (Real.log (349289 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (349289 / 250000) = -Real.log (250000 / 349289) := by
    rw [show ((349289 / 250000) : ℝ) = ((250000 / 349289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (253048411 / 500000000) ≤ -Real.log (150711 / 250000) ∧
    -Real.log (150711 / 250000) ≤ (506096823 / 1000000000) := by
  have h := checkLog_sound (w := (99289 / 400711)) (n := 12)
    (lo := (253048411 / 500000000)) (hi := (506096823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 150711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 150711) = 1/(150711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-506096823 / 1000000000) (-253048411 / 500000000) (Real.log (150711 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (335061241 / 1000000000) ≤ -Real.log (500000 / 699013) ∧
    -Real.log (500000 / 699013) ≤ (167530621 / 500000000) := by
  have h := checkLog_sound (w := (199013 / 1199013)) (n := 12)
    (lo := (335061241 / 1000000000)) (hi := (167530621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699013 / 500000) = 1/(500000 / 699013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (335061241 / 1000000000) (167530621 / 500000000) (Real.log (699013 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (699013 / 500000) = -Real.log (500000 / 699013) := by
    rw [show ((699013 / 500000) : ℝ) = ((500000 / 699013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (507541023 / 1000000000) ≤ -Real.log (300987 / 500000) ∧
    -Real.log (300987 / 500000) ≤ (15860657 / 31250000) := by
  have h := checkLog_sound (w := (199013 / 800987)) (n := 12)
    (lo := (507541023 / 1000000000)) (hi := (15860657 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 300987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 300987) = 1/(300987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15860657 / 31250000) (-507541023 / 1000000000) (Real.log (300987 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257457631 / 1000000000) ≤ -Real.log (1000000 / 1293637) ∧
    -Real.log (1000000 / 1293637) ≤ (8045551 / 31250000) := by
  have h := checkLog_sound (w := (293637 / 2293637)) (n := 12)
    (lo := (257457631 / 1000000000)) (hi := (8045551 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293637 / 1000000) = 1/(1000000 / 1293637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257457631 / 1000000000) (8045551 / 31250000) (Real.log (1293637 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1293637 / 1000000) = -Real.log (1000000 / 1293637) := by
    rw [show ((1293637 / 1000000) : ℝ) = ((1000000 / 1293637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (347626009 / 1000000000) ≤ -Real.log (706363 / 1000000) ∧
    -Real.log (706363 / 1000000) ≤ (34762601 / 100000000) := by
  have h := checkLog_sound (w := (293637 / 1706363)) (n := 12)
    (lo := (347626009 / 1000000000)) (hi := (34762601 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 706363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 706363) = 1/(706363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-34762601 / 100000000) (-347626009 / 1000000000) (Real.log (706363 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (12900007 / 50000000) ≤ -Real.log (1000000 / 1294339) ∧
    -Real.log (1000000 / 1294339) ≤ (258000141 / 1000000000) := by
  have h := checkLog_sound (w := (294339 / 2294339)) (n := 12)
    (lo := (12900007 / 50000000)) (hi := (258000141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294339 / 1000000) = 1/(1000000 / 1294339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (12900007 / 50000000) (258000141 / 1000000000) (Real.log (1294339 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1294339 / 1000000) = -Real.log (1000000 / 1294339) := by
    rw [show ((1294339 / 1000000) : ℝ) = ((1000000 / 1294339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (174310163 / 500000000) ≤ -Real.log (705661 / 1000000) ∧
    -Real.log (705661 / 1000000) ≤ (348620327 / 1000000000) := by
  have h := checkLog_sound (w := (294339 / 1705661)) (n := 12)
    (lo := (174310163 / 500000000)) (hi := (348620327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705661) = 1/(705661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-348620327 / 1000000000) (-174310163 / 500000000) (Real.log (705661 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (840535563 / 1000000000) ≤ -Real.log (500000000000 / 1158803936009) ∧
    -Real.log (500000000000 / 1158803936009) ≤ (168107113 / 200000000) := by
  have h := checkLog_sound (w := (158803936009 / 2158803936009)) (n := 12)
    (lo := (147388383 / 1000000000)) (hi := (4605887 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158803936009 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1158803936009 / 1000000000000) = 1/(500000000000 / 1158803936009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (840535563 / 1000000000) (168107113 / 200000000) (Real.log (1158803936009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1158803936009 / 500000000000) = -Real.log (500000000000 / 1158803936009) := by
    rw [show ((1158803936009 / 500000000000) : ℝ) = ((500000000000 / 1158803936009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (168520453 / 200000000) ≤ -Real.log (500000000000 / 1161201314343) ∧
    -Real.log (500000000000 / 1161201314343) ≤ (842602267 / 1000000000) := by
  have h := checkLog_sound (w := (161201314343 / 2161201314343)) (n := 12)
    (lo := (29891017 / 200000000)) (hi := (74727543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161201314343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1161201314343 / 1000000000000) = 1/(500000000000 / 1161201314343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (168520453 / 200000000) (842602267 / 1000000000) (Real.log (1161201314343 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1161201314343 / 500000000000) = -Real.log (500000000000 / 1161201314343) := by
    rw [show ((1161201314343 / 500000000000) : ℝ) = ((500000000000 / 1161201314343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15127091 / 25000000) ≤ -Real.log (500000000000 / 915702691109) ∧
    -Real.log (500000000000 / 915702691109) ≤ (605083641 / 1000000000) := by
  have h := checkLog_sound (w := (415702691109 / 1415702691109)) (n := 12)
    (lo := (15127091 / 25000000)) (hi := (605083641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915702691109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915702691109 / 500000000000) = 1/(500000000000 / 915702691109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15127091 / 25000000) (605083641 / 1000000000) (Real.log (915702691109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (915702691109 / 500000000000) = -Real.log (500000000000 / 915702691109) := by
    rw [show ((915702691109 / 500000000000) : ℝ) = ((500000000000 / 915702691109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (303310233 / 500000000) ≤ -Real.log (250000000000 / 458555524537) ∧
    -Real.log (250000000000 / 458555524537) ≤ (606620467 / 1000000000) := by
  have h := checkLog_sound (w := (208555524537 / 708555524537)) (n := 12)
    (lo := (303310233 / 500000000)) (hi := (606620467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458555524537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(458555524537 / 250000000000) = 1/(250000000000 / 458555524537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (303310233 / 500000000) (606620467 / 1000000000) (Real.log (458555524537 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (458555524537 / 250000000000) = -Real.log (250000000000 / 458555524537) := by
    rw [show ((458555524537 / 250000000000) : ℝ) = ((250000000000 / 458555524537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0246
