import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0432
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

theorem reflection_log_1_neg : (12032703 / 62500000) ≤ -Real.log (5120 / 6207) ∧
    -Real.log (5120 / 6207) ≤ (192523249 / 1000000000) := by
  have h := checkLog_sound (w := (1087 / 11327)) (n := 12)
    (lo := (12032703 / 62500000)) (hi := (192523249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6207 / 5120) = 1/(5120 / 6207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12032703 / 62500000) (192523249 / 1000000000) (Real.log (6207 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6207 / 5120) = -Real.log (5120 / 6207) := by
    rw [show ((6207 / 5120) : ℝ) = ((5120 / 6207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (238643923 / 1000000000) ≤ -Real.log (4033 / 5120) ∧
    -Real.log (4033 / 5120) ≤ (59660981 / 250000000) := by
  have h := checkLog_sound (w := (1087 / 9153)) (n := 12)
    (lo := (238643923 / 1000000000)) (hi := (59660981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4033) = 1/(4033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59660981 / 250000000) (-238643923 / 1000000000) (Real.log (4033 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48070389 / 250000000) ≤ -Real.log (10240 / 12411) ∧
    -Real.log (10240 / 12411) ≤ (192281557 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 22651)) (n := 12)
    (lo := (48070389 / 250000000)) (hi := (192281557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 10240) = 1/(10240 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48070389 / 250000000) (192281557 / 1000000000) (Real.log (12411 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12411 / 10240) = -Real.log (10240 / 12411) := by
    rw [show ((12411 / 10240) : ℝ) = ((10240 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (11913603 / 50000000) ≤ -Real.log (8069 / 10240) ∧
    -Real.log (8069 / 10240) ≤ (238272061 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 18309)) (n := 12)
    (lo := (11913603 / 50000000)) (hi := (238272061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8069) = 1/(8069 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-238272061 / 1000000000) (-11913603 / 50000000) (Real.log (8069 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (353897653 / 1000000000) ≤ -Real.log (2560 / 3647) ∧
    -Real.log (2560 / 3647) ≤ (176948827 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 6207)) (n := 12)
    (lo := (353897653 / 1000000000)) (hi := (176948827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3647 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3647 / 2560) = 1/(2560 / 3647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (353897653 / 1000000000) (176948827 / 500000000) (Real.log (3647 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3647 / 2560) = -Real.log (2560 / 3647) := by
    rw [show ((3647 / 2560) : ℝ) = ((2560 / 3647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (552706121 / 1000000000) ≤ -Real.log (1473 / 2560) ∧
    -Real.log (1473 / 2560) ≤ (276353061 / 500000000) := by
  have h := checkLog_sound (w := (1087 / 4033)) (n := 12)
    (lo := (552706121 / 1000000000)) (hi := (276353061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1473) = 1/(1473 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-276353061 / 500000000) (-552706121 / 1000000000) (Real.log (1473 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (353486271 / 1000000000) ≤ -Real.log (5120 / 7291) ∧
    -Real.log (5120 / 7291) ≤ (5523223 / 15625000) := by
  have h := checkLog_sound (w := (2171 / 12411)) (n := 12)
    (lo := (353486271 / 1000000000)) (hi := (5523223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7291 / 5120) = 1/(5120 / 7291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (353486271 / 1000000000) (5523223 / 15625000) (Real.log (7291 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7291 / 5120) = -Real.log (5120 / 7291) := by
    rw [show ((7291 / 5120) : ℝ) = ((5120 / 7291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (551688309 / 1000000000) ≤ -Real.log (2949 / 5120) ∧
    -Real.log (2949 / 5120) ≤ (55168831 / 100000000) := by
  have h := checkLog_sound (w := (2171 / 8069)) (n := 12)
    (lo := (551688309 / 1000000000)) (hi := (55168831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2949) = 1/(2949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55168831 / 100000000) (-551688309 / 1000000000) (Real.log (2949 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (8253187 / 31250000) ≤ -Real.log (1000000 / 1302261) ∧
    -Real.log (1000000 / 1302261) ≤ (52820397 / 200000000) := by
  have h := checkLog_sound (w := (302261 / 2302261)) (n := 12)
    (lo := (8253187 / 31250000)) (hi := (52820397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302261 / 1000000) = 1/(1000000 / 1302261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (8253187 / 31250000) (52820397 / 200000000) (Real.log (1302261 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1302261 / 1000000) = -Real.log (1000000 / 1302261) := by
    rw [show ((1302261 / 1000000) : ℝ) = ((1000000 / 1302261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (359910171 / 1000000000) ≤ -Real.log (697739 / 1000000) ∧
    -Real.log (697739 / 1000000) ≤ (89977543 / 250000000) := by
  have h := checkLog_sound (w := (302261 / 1697739)) (n := 12)
    (lo := (359910171 / 1000000000)) (hi := (89977543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697739) = 1/(697739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-89977543 / 250000000) (-359910171 / 1000000000) (Real.log (697739 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (132214527 / 500000000) ≤ -Real.log (1000000 / 1302687) ∧
    -Real.log (1000000 / 1302687) ≤ (52885811 / 200000000) := by
  have h := checkLog_sound (w := (302687 / 2302687)) (n := 12)
    (lo := (132214527 / 500000000)) (hi := (52885811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1302687 / 1000000) = 1/(1000000 / 1302687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (132214527 / 500000000) (52885811 / 200000000) (Real.log (1302687 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1302687 / 1000000) = -Real.log (1000000 / 1302687) := by
    rw [show ((1302687 / 1000000) : ℝ) = ((1000000 / 1302687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (360520901 / 1000000000) ≤ -Real.log (697313 / 1000000) ∧
    -Real.log (697313 / 1000000) ≤ (180260451 / 500000000) := by
  have h := checkLog_sound (w := (302687 / 1697313)) (n := 12)
    (lo := (360520901 / 1000000000)) (hi := (180260451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 697313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 697313) = 1/(697313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180260451 / 500000000) (-360520901 / 1000000000) (Real.log (697313 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9912903 / 50000000) ≤ -Real.log (1000000 / 1219277) ∧
    -Real.log (1000000 / 1219277) ≤ (198258061 / 1000000000) := by
  have h := checkLog_sound (w := (219277 / 2219277)) (n := 12)
    (lo := (9912903 / 50000000)) (hi := (198258061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219277 / 1000000) = 1/(1000000 / 1219277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9912903 / 50000000) (198258061 / 1000000000) (Real.log (1219277 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1219277 / 1000000) = -Real.log (1000000 / 1219277) := by
    rw [show ((1219277 / 1000000) : ℝ) = ((1000000 / 1219277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49506973 / 200000000) ≤ -Real.log (780723 / 1000000) ∧
    -Real.log (780723 / 1000000) ≤ (123767433 / 500000000) := by
  have h := checkLog_sound (w := (219277 / 1780723)) (n := 12)
    (lo := (49506973 / 200000000)) (hi := (123767433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780723) = 1/(780723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-123767433 / 500000000) (-49506973 / 200000000) (Real.log (780723 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39705079 / 200000000) ≤ -Real.log (1000000 / 1219603) ∧
    -Real.log (1000000 / 1219603) ≤ (49631349 / 250000000) := by
  have h := checkLog_sound (w := (219603 / 2219603)) (n := 12)
    (lo := (39705079 / 200000000)) (hi := (49631349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219603 / 1000000) = 1/(1000000 / 1219603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39705079 / 200000000) (49631349 / 250000000) (Real.log (1219603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1219603 / 1000000) = -Real.log (1000000 / 1219603) := by
    rw [show ((1219603 / 1000000) : ℝ) = ((1000000 / 1219603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (123976257 / 500000000) ≤ -Real.log (780397 / 1000000) ∧
    -Real.log (780397 / 1000000) ≤ (49590503 / 200000000) := by
  have h := checkLog_sound (w := (219603 / 1780397)) (n := 12)
    (lo := (123976257 / 500000000)) (hi := (49590503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780397) = 1/(780397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-49590503 / 200000000) (-123976257 / 500000000) (Real.log (780397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (156003039 / 250000000) ≤ -Real.log (125000000000 / 233300166681) ∧
    -Real.log (125000000000 / 233300166681) ≤ (624012157 / 1000000000) := by
  have h := checkLog_sound (w := (108300166681 / 358300166681)) (n := 12)
    (lo := (156003039 / 250000000)) (hi := (624012157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233300166681 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233300166681 / 125000000000) = 1/(125000000000 / 233300166681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (156003039 / 250000000) (624012157 / 1000000000) (Real.log (233300166681 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233300166681 / 125000000000) = -Real.log (125000000000 / 233300166681) := by
    rw [show ((233300166681 / 125000000000) : ℝ) = ((125000000000 / 233300166681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (124989991 / 200000000) ≤ -Real.log (4000000000 / 7472609861) ∧
    -Real.log (4000000000 / 7472609861) ≤ (156237489 / 250000000) := by
  have h := checkLog_sound (w := (3472609861 / 11472609861)) (n := 12)
    (lo := (124989991 / 200000000)) (hi := (156237489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7472609861 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7472609861 / 4000000000) = 1/(4000000000 / 7472609861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (124989991 / 200000000) (156237489 / 250000000) (Real.log (7472609861 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7472609861 / 4000000000) = -Real.log (4000000000 / 7472609861) := by
    rw [show ((7472609861 / 4000000000) : ℝ) = ((4000000000 / 7472609861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17831717 / 40000000) ≤ -Real.log (500000000000 / 780864019633) ∧
    -Real.log (500000000000 / 780864019633) ≤ (222896463 / 500000000) := by
  have h := checkLog_sound (w := (280864019633 / 1280864019633)) (n := 12)
    (lo := (17831717 / 40000000)) (hi := (222896463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780864019633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780864019633 / 500000000000) = 1/(500000000000 / 780864019633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17831717 / 40000000) (222896463 / 500000000) (Real.log (780864019633 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780864019633 / 500000000000) = -Real.log (500000000000 / 780864019633) := by
    rw [show ((780864019633 / 500000000000) : ℝ) = ((500000000000 / 780864019633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (44647791 / 100000000) ≤ -Real.log (20000000000 / 31255963311) ∧
    -Real.log (20000000000 / 31255963311) ≤ (446477911 / 1000000000) := by
  have h := checkLog_sound (w := (11255963311 / 51255963311)) (n := 12)
    (lo := (44647791 / 100000000)) (hi := (446477911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31255963311 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31255963311 / 20000000000) = 1/(20000000000 / 31255963311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (44647791 / 100000000) (446477911 / 1000000000) (Real.log (31255963311 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31255963311 / 20000000000) = -Real.log (20000000000 / 31255963311) := by
    rw [show ((31255963311 / 20000000000) : ℝ) = ((20000000000 / 31255963311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0432
