import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0141
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

theorem reflection_log_1_neg : (74591743 / 250000000) ≤ -Real.log (256 / 345) ∧
    -Real.log (256 / 345) ≤ (298366973 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 601)) (n := 12)
    (lo := (74591743 / 250000000)) (hi := (298366973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345 / 256) = 1/(256 / 345) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (74591743 / 250000000) (298366973 / 1000000000) (Real.log (345 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (345 / 256) = -Real.log (256 / 345) := by
    rw [show ((345 / 256) : ℝ) = ((256 / 345) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26698977 / 62500000) ≤ -Real.log (167 / 256) ∧
    -Real.log (167 / 256) ≤ (427183633 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 423)) (n := 12)
    (lo := (26698977 / 62500000)) (hi := (427183633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 167) = 1/(167 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-427183633 / 1000000000) (-26698977 / 62500000) (Real.log (167 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (297497029 / 1000000000) ≤ -Real.log (2560 / 3447) ∧
    -Real.log (2560 / 3447) ≤ (29749703 / 100000000) := by
  have h := checkLog_sound (w := (887 / 6007)) (n := 12)
    (lo := (297497029 / 1000000000)) (hi := (29749703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3447 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3447 / 2560) = 1/(2560 / 3447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (297497029 / 1000000000) (29749703 / 100000000) (Real.log (3447 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3447 / 2560) = -Real.log (2560 / 3447) := by
    rw [show ((3447 / 2560) : ℝ) = ((2560 / 3447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (106347209 / 250000000) ≤ -Real.log (1673 / 2560) ∧
    -Real.log (1673 / 2560) ≤ (425388837 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 4233)) (n := 12)
    (lo := (106347209 / 250000000)) (hi := (425388837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1673) = 1/(1673 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-425388837 / 1000000000) (-106347209 / 250000000) (Real.log (1673 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (527867089 / 1000000000) ≤ -Real.log (128 / 217) ∧
    -Real.log (128 / 217) ≤ (52786709 / 100000000) := by
  have h := checkLog_sound (w := (89 / 345)) (n := 12)
    (lo := (527867089 / 1000000000)) (hi := (52786709 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217 / 128) = 1/(128 / 217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (527867089 / 1000000000) (52786709 / 100000000) (Real.log (217 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (217 / 128) = -Real.log (128 / 217) := by
    rw [show ((217 / 128) : ℝ) = ((128 / 217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1188468617 / 1000000000) ≤ -Real.log (39 / 128) ∧
    -Real.log (39 / 128) ≤ (1188468619 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 39) = 1/(39 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1188468619 / 1000000000) (-1188468617 / 1000000000) (Real.log (39 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131620911 / 250000000) ≤ -Real.log (1280 / 2167) ∧
    -Real.log (1280 / 2167) ≤ (105296729 / 200000000) := by
  have h := checkLog_sound (w := (887 / 3447)) (n := 12)
    (lo := (131620911 / 250000000)) (hi := (105296729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2167 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2167 / 1280) = 1/(1280 / 2167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131620911 / 250000000) (105296729 / 200000000) (Real.log (2167 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2167 / 1280) = -Real.log (1280 / 2167) := by
    rw [show ((2167 / 1280) : ℝ) = ((1280 / 2167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (73800359 / 62500000) ≤ -Real.log (393 / 1280) ∧
    -Real.log (393 / 1280) ≤ (590402873 / 500000000) := by
  have h := checkLog_sound (w := (247 / 1033)) (n := 12)
    (lo := (121914641 / 250000000)) (hi := (97531713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 393) = 1/(393 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-590402873 / 500000000) (-73800359 / 62500000) (Real.log (393 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (407135711 / 1000000000) ≤ -Real.log (250000 / 375627) ∧
    -Real.log (250000 / 375627) ≤ (12722991 / 31250000) := by
  have h := checkLog_sound (w := (125627 / 625627)) (n := 12)
    (lo := (407135711 / 1000000000)) (hi := (12722991 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375627 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375627 / 250000) = 1/(250000 / 375627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (407135711 / 1000000000) (12722991 / 31250000) (Real.log (375627 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (375627 / 250000) = -Real.log (250000 / 375627) := by
    rw [show ((375627 / 250000) : ℝ) = ((250000 / 375627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349087901 / 500000000) ≤ -Real.log (124373 / 250000) ∧
    -Real.log (124373 / 250000) ≤ (174543951 / 250000000) := by
  have h := checkLog_sound (w := (627 / 249373)) (n := 12)
    (lo := (2514311 / 500000000)) (hi := (5028623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124373) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 124373) = 1/(124373 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174543951 / 250000000) (-349087901 / 500000000) (Real.log (124373 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51042621 / 125000000) ≤ -Real.log (3125 / 4701) ∧
    -Real.log (3125 / 4701) ≤ (408340969 / 1000000000) := by
  have h := checkLog_sound (w := (788 / 3913)) (n := 12)
    (lo := (51042621 / 125000000)) (hi := (408340969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4701 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4701 / 3125) = 1/(3125 / 4701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51042621 / 125000000) (408340969 / 1000000000) (Real.log (4701 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (4701 / 3125) = -Real.log (3125 / 4701) := by
    rw [show ((4701 / 3125) : ℝ) = ((3125 / 4701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (701824721 / 1000000000) ≤ -Real.log (1549 / 3125) ∧
    -Real.log (1549 / 3125) ≤ (701824723 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 6223)) (n := 12)
    (lo := (8677541 / 1000000000)) (hi := (4338771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3098) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 3098) = 1/(1549 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-701824723 / 1000000000) (-701824721 / 1000000000) (Real.log (1549 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323476007 / 1000000000) ≤ -Real.log (1000000 / 1381923) ∧
    -Real.log (1000000 / 1381923) ≤ (40434501 / 125000000) := by
  have h := checkLog_sound (w := (381923 / 2381923)) (n := 12)
    (lo := (323476007 / 1000000000)) (hi := (40434501 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381923 / 1000000) = 1/(1000000 / 1381923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323476007 / 1000000000) (40434501 / 125000000) (Real.log (1381923 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1381923 / 1000000) = -Real.log (1000000 / 1381923) := by
    rw [show ((1381923 / 1000000) : ℝ) = ((1000000 / 1381923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (481142233 / 1000000000) ≤ -Real.log (618077 / 1000000) ∧
    -Real.log (618077 / 1000000) ≤ (240571117 / 500000000) := by
  have h := checkLog_sound (w := (381923 / 1618077)) (n := 12)
    (lo := (481142233 / 1000000000)) (hi := (240571117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618077) = 1/(618077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-240571117 / 500000000) (-481142233 / 1000000000) (Real.log (618077 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (324620857 / 1000000000) ≤ -Real.log (500000 / 691753) ∧
    -Real.log (500000 / 691753) ≤ (162310429 / 500000000) := by
  have h := checkLog_sound (w := (191753 / 1191753)) (n := 12)
    (lo := (324620857 / 1000000000)) (hi := (162310429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691753 / 500000) = 1/(500000 / 691753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (324620857 / 1000000000) (162310429 / 500000000) (Real.log (691753 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (691753 / 500000) = -Real.log (500000 / 691753) := by
    rw [show ((691753 / 500000) : ℝ) = ((500000 / 691753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7557917 / 15625000) ≤ -Real.log (308247 / 500000) ∧
    -Real.log (308247 / 500000) ≤ (483706689 / 1000000000) := by
  have h := checkLog_sound (w := (191753 / 808247)) (n := 12)
    (lo := (7557917 / 15625000)) (hi := (483706689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 308247) = 1/(308247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-483706689 / 1000000000) (-7557917 / 15625000) (Real.log (308247 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (552655757 / 500000000) ≤ -Real.log (31250000000 / 94380160887) ∧
    -Real.log (31250000000 / 94380160887) ≤ (276327879 / 250000000) := by
  have h := checkLog_sound (w := (31880160887 / 156880160887)) (n := 12)
    (lo := (206082167 / 500000000)) (hi := (82432867 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94380160887 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(94380160887 / 62500000000) = 1/(31250000000 / 94380160887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (552655757 / 500000000) (276327879 / 250000000) (Real.log (94380160887 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (94380160887 / 31250000000) = -Real.log (31250000000 / 94380160887) := by
    rw [show ((94380160887 / 31250000000) : ℝ) = ((31250000000 / 94380160887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (111016569 / 100000000) ≤ -Real.log (125000000000 / 379357650097) ∧
    -Real.log (125000000000 / 379357650097) ≤ (277541423 / 250000000) := by
  have h := checkLog_sound (w := (129357650097 / 629357650097)) (n := 12)
    (lo := (41701851 / 100000000)) (hi := (417018511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379357650097 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(379357650097 / 250000000000) = 1/(125000000000 / 379357650097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (111016569 / 100000000) (277541423 / 250000000) (Real.log (379357650097 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (379357650097 / 125000000000) = -Real.log (125000000000 / 379357650097) := by
    rw [show ((379357650097 / 125000000000) : ℝ) = ((125000000000 / 379357650097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (314304 / 390625) ≤ -Real.log (500000000000 / 1117921391671) ∧
    -Real.log (500000000000 / 1117921391671) ≤ (402309121 / 500000000) := by
  have h := checkLog_sound (w := (117921391671 / 2117921391671)) (n := 12)
    (lo := (5573553 / 50000000)) (hi := (111471061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1117921391671 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1117921391671 / 1000000000000) = 1/(500000000000 / 1117921391671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (314304 / 390625) (402309121 / 500000000) (Real.log (1117921391671 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1117921391671 / 500000000000) = -Real.log (500000000000 / 1117921391671) := by
    rw [show ((1117921391671 / 500000000000) : ℝ) = ((500000000000 / 1117921391671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (161665509 / 200000000) ≤ -Real.log (500000000000 / 1122075802847) ∧
    -Real.log (500000000000 / 1122075802847) ≤ (808327547 / 1000000000) := by
  have h := checkLog_sound (w := (122075802847 / 2122075802847)) (n := 12)
    (lo := (23036073 / 200000000)) (hi := (57590183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122075802847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1122075802847 / 1000000000000) = 1/(500000000000 / 1122075802847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (161665509 / 200000000) (808327547 / 1000000000) (Real.log (1122075802847 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1122075802847 / 500000000000) = -Real.log (500000000000 / 1122075802847) := by
    rw [show ((1122075802847 / 500000000000) : ℝ) = ((500000000000 / 1122075802847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0141
