import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0275
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

theorem reflection_log_1_neg : (231390699 / 1000000000) ≤ -Real.log (5120 / 6453) ∧
    -Real.log (5120 / 6453) ≤ (2313907 / 10000000) := by
  have h := checkLog_sound (w := (1333 / 11573)) (n := 12)
    (lo := (231390699 / 1000000000)) (hi := (2313907 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6453 / 5120) = 1/(5120 / 6453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (231390699 / 1000000000) (2313907 / 10000000) (Real.log (6453 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6453 / 5120) = -Real.log (5120 / 6453) := by
    rw [show ((6453 / 5120) : ℝ) = ((5120 / 6453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (30158029 / 100000000) ≤ -Real.log (3787 / 5120) ∧
    -Real.log (3787 / 5120) ≤ (301580291 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 8907)) (n := 12)
    (lo := (30158029 / 100000000)) (hi := (301580291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3787) = 1/(3787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301580291 / 1000000000) (-30158029 / 100000000) (Real.log (3787 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230925691 / 1000000000) ≤ -Real.log (512 / 645) ∧
    -Real.log (512 / 645) ≤ (57731423 / 250000000) := by
  have h := checkLog_sound (w := (133 / 1157)) (n := 12)
    (lo := (230925691 / 1000000000)) (hi := (57731423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645 / 512) = 1/(512 / 645) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230925691 / 1000000000) (57731423 / 250000000) (Real.log (645 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (645 / 512) = -Real.log (512 / 645) := by
    rw [show ((645 / 512) : ℝ) = ((512 / 645) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (300788419 / 1000000000) ≤ -Real.log (379 / 512) ∧
    -Real.log (379 / 512) ≤ (15039421 / 50000000) := by
  have h := checkLog_sound (w := (133 / 891)) (n := 12)
    (lo := (300788419 / 1000000000)) (hi := (15039421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 379) = 1/(379 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) (Real.log (379 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41917281 / 100000000) ≤ -Real.log (2560 / 3893) ∧
    -Real.log (2560 / 3893) ≤ (419172811 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6453)) (n := 12)
    (lo := (41917281 / 100000000)) (hi := (419172811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3893 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3893 / 2560) = 1/(2560 / 3893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41917281 / 100000000) (419172811 / 1000000000) (Real.log (3893 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3893 / 2560) = -Real.log (2560 / 3893) := by
    rw [show ((3893 / 2560) : ℝ) = ((2560 / 3893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (183858773 / 250000000) ≤ -Real.log (1227 / 2560) ∧
    -Real.log (1227 / 2560) ≤ (367717547 / 500000000) := by
  have h := checkLog_sound (w := (53 / 2507)) (n := 12)
    (lo := (5285989 / 125000000)) (hi := (42287913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1227) = 1/(1227 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-367717547 / 500000000) (-183858773 / 250000000) (Real.log (1227 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (418401899 / 1000000000) ≤ -Real.log (256 / 389) ∧
    -Real.log (256 / 389) ≤ (4184019 / 10000000) := by
  have h := checkLog_sound (w := (133 / 645)) (n := 12)
    (lo := (418401899 / 1000000000)) (hi := (4184019 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389 / 256) = 1/(256 / 389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (418401899 / 1000000000) (4184019 / 10000000) (Real.log (389 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (389 / 256) = -Real.log (256 / 389) := by
    rw [show ((389 / 256) : ℝ) = ((256 / 389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11453017 / 15625000) ≤ -Real.log (123 / 256) ∧
    -Real.log (123 / 256) ≤ (73299309 / 100000000) := by
  have h := checkLog_sound (w := (5 / 251)) (n := 12)
    (lo := (9961477 / 250000000)) (hi := (39845909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 123) = 1/(123 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) (Real.log (123 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158148977 / 500000000) ≤ -Real.log (1000000 / 1372039) ∧
    -Real.log (1000000 / 1372039) ≤ (63259591 / 200000000) := by
  have h := checkLog_sound (w := (372039 / 2372039)) (n := 12)
    (lo := (158148977 / 500000000)) (hi := (63259591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372039 / 1000000) = 1/(1000000 / 1372039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158148977 / 500000000) (63259591 / 200000000) (Real.log (1372039 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1372039 / 1000000) = -Real.log (1000000 / 1372039) := by
    rw [show ((1372039 / 1000000) : ℝ) = ((1000000 / 1372039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (14539913 / 31250000) ≤ -Real.log (627961 / 1000000) ∧
    -Real.log (627961 / 1000000) ≤ (465277217 / 1000000000) := by
  have h := checkLog_sound (w := (372039 / 1627961)) (n := 12)
    (lo := (14539913 / 31250000)) (hi := (465277217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627961) = 1/(627961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-465277217 / 1000000000) (-14539913 / 31250000) (Real.log (627961 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (79231869 / 250000000) ≤ -Real.log (1000000 / 1372903) ∧
    -Real.log (1000000 / 1372903) ≤ (316927477 / 1000000000) := by
  have h := checkLog_sound (w := (372903 / 2372903)) (n := 12)
    (lo := (79231869 / 250000000)) (hi := (316927477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1372903 / 1000000) = 1/(1000000 / 1372903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (79231869 / 250000000) (316927477 / 1000000000) (Real.log (1372903 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1372903 / 1000000) = -Real.log (1000000 / 1372903) := by
    rw [show ((1372903 / 1000000) : ℝ) = ((1000000 / 1372903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93330809 / 200000000) ≤ -Real.log (627097 / 1000000) ∧
    -Real.log (627097 / 1000000) ≤ (233327023 / 500000000) := by
  have h := checkLog_sound (w := (372903 / 1627097)) (n := 12)
    (lo := (93330809 / 200000000)) (hi := (233327023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 627097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 627097) = 1/(627097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-233327023 / 500000000) (-93330809 / 200000000) (Real.log (627097 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12090139 / 50000000) ≤ -Real.log (1000000 / 1273543) ∧
    -Real.log (1000000 / 1273543) ≤ (241802781 / 1000000000) := by
  have h := checkLog_sound (w := (273543 / 2273543)) (n := 12)
    (lo := (12090139 / 50000000)) (hi := (241802781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273543 / 1000000) = 1/(1000000 / 1273543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12090139 / 50000000) (241802781 / 1000000000) (Real.log (1273543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1273543 / 1000000) = -Real.log (1000000 / 1273543) := by
    rw [show ((1273543 / 1000000) : ℝ) = ((1000000 / 1273543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63915197 / 200000000) ≤ -Real.log (726457 / 1000000) ∧
    -Real.log (726457 / 1000000) ≤ (159787993 / 500000000) := by
  have h := checkLog_sound (w := (273543 / 1726457)) (n := 12)
    (lo := (63915197 / 200000000)) (hi := (159787993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 726457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 726457) = 1/(726457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-159787993 / 500000000) (-63915197 / 200000000) (Real.log (726457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (121171037 / 500000000) ≤ -Real.log (100000 / 127423) ∧
    -Real.log (100000 / 127423) ≤ (9693683 / 40000000) := by
  have h := checkLog_sound (w := (27423 / 227423)) (n := 12)
    (lo := (121171037 / 500000000)) (hi := (9693683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127423 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127423 / 100000) = 1/(100000 / 127423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121171037 / 500000000) (9693683 / 40000000) (Real.log (127423 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (127423 / 100000) = -Real.log (100000 / 127423) := by
    rw [show ((127423 / 100000) : ℝ) = ((100000 / 127423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (160261059 / 500000000) ≤ -Real.log (72577 / 100000) ∧
    -Real.log (72577 / 100000) ≤ (320522119 / 1000000000) := by
  have h := checkLog_sound (w := (27423 / 172577)) (n := 12)
    (lo := (160261059 / 500000000)) (hi := (320522119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72577) = 1/(72577 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-320522119 / 1000000000) (-160261059 / 500000000) (Real.log (72577 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (78157517 / 100000000) ≤ -Real.log (15625000000 / 34139236951) ∧
    -Real.log (15625000000 / 34139236951) ≤ (195393793 / 250000000) := by
  have h := checkLog_sound (w := (2889236951 / 65389236951)) (n := 12)
    (lo := (8842799 / 100000000)) (hi := (88427991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34139236951 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34139236951 / 31250000000) = 1/(15625000000 / 34139236951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78157517 / 100000000) (195393793 / 250000000) (Real.log (34139236951 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (34139236951 / 15625000000) = -Real.log (15625000000 / 34139236951) := by
    rw [show ((34139236951 / 15625000000) : ℝ) = ((15625000000 / 34139236951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (9794769 / 12500000) ≤ -Real.log (500000000000 / 1094649631557) ∧
    -Real.log (500000000000 / 1094649631557) ≤ (391790761 / 500000000) := by
  have h := checkLog_sound (w := (94649631557 / 2094649631557)) (n := 12)
    (lo := (4521717 / 50000000)) (hi := (90434341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094649631557 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1094649631557 / 1000000000000) = 1/(500000000000 / 1094649631557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (9794769 / 12500000) (391790761 / 500000000) (Real.log (1094649631557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1094649631557 / 500000000000) = -Real.log (500000000000 / 1094649631557) := by
    rw [show ((1094649631557 / 500000000000) : ℝ) = ((500000000000 / 1094649631557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112275753 / 200000000) ≤ -Real.log (250000000000 / 438271983063) ∧
    -Real.log (250000000000 / 438271983063) ≤ (280689383 / 500000000) := by
  have h := checkLog_sound (w := (188271983063 / 688271983063)) (n := 12)
    (lo := (112275753 / 200000000)) (hi := (280689383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438271983063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438271983063 / 250000000000) = 1/(250000000000 / 438271983063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112275753 / 200000000) (280689383 / 500000000) (Real.log (438271983063 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (438271983063 / 250000000000) = -Real.log (250000000000 / 438271983063) := by
    rw [show ((438271983063 / 250000000000) : ℝ) = ((250000000000 / 438271983063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (562864193 / 1000000000) ≤ -Real.log (100000000000 / 175569395263) ∧
    -Real.log (100000000000 / 175569395263) ≤ (281432097 / 500000000) := by
  have h := checkLog_sound (w := (75569395263 / 275569395263)) (n := 12)
    (lo := (562864193 / 1000000000)) (hi := (281432097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175569395263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175569395263 / 100000000000) = 1/(100000000000 / 175569395263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (562864193 / 1000000000) (281432097 / 500000000) (Real.log (175569395263 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (175569395263 / 100000000000) = -Real.log (100000000000 / 175569395263) := by
    rw [show ((175569395263 / 100000000000) : ℝ) = ((100000000000 / 175569395263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0275
