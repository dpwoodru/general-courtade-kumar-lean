import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0167
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

theorem reflection_log_1_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (639424951 / 1000000000) ≤ -Real.log (12800 / 24261) ∧
    -Real.log (12800 / 24261) ≤ (79928119 / 125000000) := by
  have h := checkLog_sound (w := (11461 / 37061)) (n := 12)
    (lo := (639424951 / 1000000000)) (hi := (79928119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24261 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24261 / 12800) = 1/(12800 / 24261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (639424951 / 1000000000) (79928119 / 125000000) (Real.log (24261 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24261 / 12800) = -Real.log (12800 / 24261) := by
    rw [show ((24261 / 12800) : ℝ) = ((12800 / 24261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1128761051 / 500000000) ≤ -Real.log (1339 / 12800) ∧
    -Real.log (1339 / 12800) ≤ (1128761053 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1339) = 1/(1339 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1128761053 / 500000000) (-1128761051 / 500000000) (Real.log (1339 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (582651977 / 1000000000) ≤ -Real.log (6400 / 11461) ∧
    -Real.log (6400 / 11461) ≤ (291325989 / 500000000) := by
  have h := checkLog_sound (w := (5061 / 17861)) (n := 12)
    (lo := (582651977 / 1000000000)) (hi := (291325989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11461 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11461 / 6400) = 1/(6400 / 11461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (582651977 / 1000000000) (291325989 / 500000000) (Real.log (11461 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11461 / 6400) = -Real.log (6400 / 11461) := by
    rw [show ((11461 / 6400) : ℝ) = ((6400 / 11461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (782187461 / 500000000) ≤ -Real.log (1339 / 6400) ∧
    -Real.log (1339 / 6400) ≤ (62574997 / 40000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1339) = 1/(1339 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-62574997 / 40000000) (-782187461 / 500000000) (Real.log (1339 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130490973 / 200000000) ≤ -Real.log (1000000 / 1920249) ∧
    -Real.log (1000000 / 1920249) ≤ (326227433 / 500000000) := by
  have h := checkLog_sound (w := (920249 / 2920249)) (n := 12)
    (lo := (130490973 / 200000000)) (hi := (326227433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1920249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1920249 / 1000000) = 1/(1000000 / 1920249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130490973 / 200000000) (326227433 / 500000000) (Real.log (1920249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1920249 / 1000000) = -Real.log (1000000 / 1920249) := by
    rw [show ((1920249 / 1000000) : ℝ) = ((1000000 / 1920249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (632211499 / 250000000) ≤ -Real.log (79751 / 1000000) ∧
    -Real.log (79751 / 1000000) ≤ (1264423 / 500000) := by
  have h := checkLog_sound (w := (45249 / 204751)) (n := 12)
    (lo := (56175557 / 125000000)) (hi := (449404457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79751) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 79751) = 1/(79751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1264423 / 500000) (-632211499 / 250000000) (Real.log (79751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (652978097 / 1000000000) ≤ -Real.log (500000 / 960627) ∧
    -Real.log (500000 / 960627) ≤ (326489049 / 500000000) := by
  have h := checkLog_sound (w := (460627 / 1460627)) (n := 12)
    (lo := (652978097 / 1000000000)) (hi := (326489049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960627 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960627 / 500000) = 1/(500000 / 960627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (652978097 / 1000000000) (326489049 / 500000000) (Real.log (960627 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (960627 / 500000) = -Real.log (500000 / 960627) := by
    rw [show ((960627 / 500000) : ℝ) = ((500000 / 960627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1270763897 / 500000000) ≤ -Real.log (39373 / 500000) ∧
    -Real.log (39373 / 500000) ≤ (1270763899 / 500000000) := by
  have h := checkLog_sound (w := (23127 / 101873)) (n := 12)
    (lo := (231043127 / 500000000)) (hi := (92417251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 39373) = 1/(39373 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1270763899 / 500000000) (-1270763897 / 500000000) (Real.log (39373 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (651084833 / 1000000000) ≤ -Real.log (50000 / 95881) ∧
    -Real.log (50000 / 95881) ≤ (325542417 / 500000000) := by
  have h := checkLog_sound (w := (45881 / 145881)) (n := 12)
    (lo := (651084833 / 1000000000)) (hi := (325542417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95881 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95881 / 50000) = 1/(50000 / 95881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (651084833 / 1000000000) (325542417 / 500000000) (Real.log (95881 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (95881 / 50000) = -Real.log (50000 / 95881) := by
    rw [show ((95881 / 50000) : ℝ) = ((50000 / 95881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (624103147 / 250000000) ≤ -Real.log (4119 / 50000) ∧
    -Real.log (4119 / 50000) ≤ (156025787 / 62500000) := by
  have h := checkLog_sound (w := (2131 / 10369)) (n := 12)
    (lo := (52121381 / 125000000)) (hi := (416971049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4119) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 4119) = 1/(4119 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-156025787 / 62500000) (-624103147 / 250000000) (Real.log (4119 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (325826803 / 500000000) ≤ -Real.log (1000000 / 1918711) ∧
    -Real.log (1000000 / 1918711) ≤ (651653607 / 1000000000) := by
  have h := checkLog_sound (w := (918711 / 2918711)) (n := 12)
    (lo := (325826803 / 500000000)) (hi := (651653607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1918711 / 1000000) = 1/(1000000 / 1918711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (325826803 / 500000000) (651653607 / 1000000000) (Real.log (1918711 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1918711 / 1000000) = -Real.log (1000000 / 1918711) := by
    rw [show ((1918711 / 1000000) : ℝ) = ((1000000 / 1918711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2509744571 / 1000000000) ≤ -Real.log (81289 / 1000000) ∧
    -Real.log (81289 / 1000000) ≤ (100389783 / 40000000) := by
  have h := checkLog_sound (w := (43711 / 206289)) (n := 12)
    (lo := (430303031 / 1000000000)) (hi := (53787879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81289) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 81289) = 1/(81289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-100389783 / 40000000) (-2509744571 / 1000000000) (Real.log (81289 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3181300861 / 1000000000) ≤ -Real.log (50000000000 / 1203902772379) ∧
    -Real.log (50000000000 / 1203902772379) ≤ (1590650433 / 500000000) := by
  have h := checkLog_sound (w := (403902772379 / 2003902772379)) (n := 12)
    (lo := (408712141 / 1000000000)) (hi := (204356071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203902772379 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1203902772379 / 800000000000) = 1/(50000000000 / 1203902772379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3181300861 / 1000000000) (1590650433 / 500000000) (Real.log (1203902772379 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1203902772379 / 50000000000) = -Real.log (50000000000 / 1203902772379) := by
    rw [show ((1203902772379 / 50000000000) : ℝ) = ((50000000000 / 1203902772379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3194505891 / 1000000000) ≤ -Real.log (500000000000 / 12199057729917) ∧
    -Real.log (500000000000 / 12199057729917) ≤ (399313237 / 125000000) := by
  have h := checkLog_sound (w := (4199057729917 / 20199057729917)) (n := 12)
    (lo := (421917171 / 1000000000)) (hi := (105479293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12199057729917 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12199057729917 / 8000000000000) = 1/(500000000000 / 12199057729917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3194505891 / 1000000000) (399313237 / 125000000) (Real.log (12199057729917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12199057729917 / 500000000000) = -Real.log (500000000000 / 12199057729917) := by
    rw [show ((12199057729917 / 500000000000) : ℝ) = ((500000000000 / 12199057729917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3147497421 / 1000000000) ≤ -Real.log (500000000000 / 11638868657441) ∧
    -Real.log (500000000000 / 11638868657441) ≤ (1573748713 / 500000000) := by
  have h := checkLog_sound (w := (3638868657441 / 19638868657441)) (n := 12)
    (lo := (374908701 / 1000000000)) (hi := (187454351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11638868657441 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11638868657441 / 8000000000000) = 1/(500000000000 / 11638868657441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3147497421 / 1000000000) (1573748713 / 500000000) (Real.log (11638868657441 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11638868657441 / 500000000000) = -Real.log (500000000000 / 11638868657441) := by
    rw [show ((11638868657441 / 500000000000) : ℝ) = ((500000000000 / 11638868657441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3161398177 / 1000000000) ≤ -Real.log (500000000000 / 11801787449717) ∧
    -Real.log (500000000000 / 11801787449717) ≤ (1580699091 / 500000000) := by
  have h := checkLog_sound (w := (3801787449717 / 19801787449717)) (n := 12)
    (lo := (388809457 / 1000000000)) (hi := (194404729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801787449717 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11801787449717 / 8000000000000) = 1/(500000000000 / 11801787449717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3161398177 / 1000000000) (1580699091 / 500000000) (Real.log (11801787449717 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11801787449717 / 500000000000) = -Real.log (500000000000 / 11801787449717) := by
    rw [show ((11801787449717 / 500000000000) : ℝ) = ((500000000000 / 11801787449717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0167
