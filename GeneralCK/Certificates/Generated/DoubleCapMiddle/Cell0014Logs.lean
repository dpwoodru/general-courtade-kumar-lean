import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0014
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

theorem reflection_log_1_neg : (403118607 / 1000000000) ≤ -Real.log (2560 / 3831) ∧
    -Real.log (2560 / 3831) ≤ (25194913 / 62500000) := by
  have h := checkLog_sound (w := (1271 / 6391)) (n := 12)
    (lo := (403118607 / 1000000000)) (hi := (25194913 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3831 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3831 / 2560) = 1/(2560 / 3831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (403118607 / 1000000000) (25194913 / 62500000) (Real.log (3831 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3831 / 2560) = -Real.log (2560 / 3831) := by
    rw [show ((3831 / 2560) : ℝ) = ((2560 / 3831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (343070267 / 500000000) ≤ -Real.log (1289 / 2560) ∧
    -Real.log (1289 / 2560) ≤ (137228107 / 200000000) := by
  have h := checkLog_sound (w := (1271 / 3849)) (n := 12)
    (lo := (343070267 / 500000000)) (hi := (137228107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1289) = 1/(1289 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137228107 / 200000000) (-343070267 / 500000000) (Real.log (1289 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80467043 / 200000000) ≤ -Real.log (640 / 957) ∧
    -Real.log (640 / 957) ≤ (25145951 / 62500000) := by
  have h := checkLog_sound (w := (317 / 1597)) (n := 12)
    (lo := (80467043 / 200000000)) (hi := (25145951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 640) = 1/(640 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80467043 / 200000000) (25145951 / 62500000) (Real.log (957 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (957 / 640) = -Real.log (640 / 957) := by
    rw [show ((957 / 640) : ℝ) = ((640 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (683815853 / 1000000000) ≤ -Real.log (323 / 640) ∧
    -Real.log (323 / 640) ≤ (341907927 / 500000000) := by
  have h := checkLog_sound (w := (317 / 963)) (n := 12)
    (lo := (683815853 / 1000000000)) (hi := (341907927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 323) = 1/(323 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341907927 / 500000000) (-683815853 / 1000000000) (Real.log (323 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (689625361 / 1000000000) ≤ -Real.log (1280 / 2551) ∧
    -Real.log (1280 / 2551) ≤ (344812681 / 500000000) := by
  have h := checkLog_sound (w := (1271 / 3831)) (n := 12)
    (lo := (689625361 / 1000000000)) (hi := (344812681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2551 / 1280) = 1/(1280 / 2551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (689625361 / 1000000000) (344812681 / 500000000) (Real.log (2551 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2551 / 1280) = -Real.log (1280 / 2551) := by
    rw [show ((2551 / 1280) : ℝ) = ((1280 / 2551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (198295631 / 40000000) ≤ -Real.log (9 / 1280) ∧
    -Real.log (9 / 1280) ≤ (4957390783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10 / 9) = 1/(9 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4957390783 / 1000000000) (-198295631 / 40000000) (Real.log (9 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (688448659 / 1000000000) ≤ -Real.log (320 / 637) ∧
    -Real.log (320 / 637) ≤ (34422433 / 50000000) := by
  have h := checkLog_sound (w := (317 / 957)) (n := 12)
    (lo := (688448659 / 1000000000)) (hi := (34422433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 320) = 1/(320 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (688448659 / 1000000000) (34422433 / 50000000) (Real.log (637 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (637 / 320) = -Real.log (320 / 637) := by
    rw [show ((637 / 320) : ℝ) = ((320 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4669708703 / 1000000000) ≤ -Real.log (3 / 320) ∧
    -Real.log (3 / 320) ≤ (466970871 / 100000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5 / 3) = 1/(3 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-466970871 / 100000000) (-4669708703 / 1000000000) (Real.log (3 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14209843 / 25000000) ≤ -Real.log (1000000 / 1765429) ∧
    -Real.log (1000000 / 1765429) ≤ (568393721 / 1000000000) := by
  have h := checkLog_sound (w := (765429 / 2765429)) (n := 12)
    (lo := (14209843 / 25000000)) (hi := (568393721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1765429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1765429 / 1000000) = 1/(1000000 / 1765429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14209843 / 25000000) (568393721 / 1000000000) (Real.log (1765429 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1765429 / 1000000) = -Real.log (1000000 / 1765429) := by
    rw [show ((1765429 / 1000000) : ℝ) = ((1000000 / 1765429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1449996963 / 1000000000) ≤ -Real.log (234571 / 1000000) ∧
    -Real.log (234571 / 1000000) ≤ (724998483 / 500000000) := by
  have h := checkLog_sound (w := (15429 / 484571)) (n := 12)
    (lo := (63702603 / 1000000000)) (hi := (15925651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 234571) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 234571) = 1/(234571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-724998483 / 500000000) (-1449996963 / 1000000000) (Real.log (234571 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (570193361 / 1000000000) ≤ -Real.log (1000000 / 1768609) ∧
    -Real.log (1000000 / 1768609) ≤ (285096681 / 500000000) := by
  have h := checkLog_sound (w := (768609 / 2768609)) (n := 12)
    (lo := (570193361 / 1000000000)) (hi := (285096681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1768609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1768609 / 1000000) = 1/(1000000 / 1768609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (570193361 / 1000000000) (285096681 / 500000000) (Real.log (1768609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1768609 / 1000000) = -Real.log (1000000 / 1768609) := by
    rw [show ((1768609 / 1000000) : ℝ) = ((1000000 / 1768609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1463646357 / 1000000000) ≤ -Real.log (231391 / 1000000) ∧
    -Real.log (231391 / 1000000) ≤ (36591159 / 25000000) := by
  have h := checkLog_sound (w := (18609 / 481391)) (n := 12)
    (lo := (77351997 / 1000000000)) (hi := (38675999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231391) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 231391) = 1/(231391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36591159 / 25000000) (-1463646357 / 1000000000) (Real.log (231391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (248230573 / 500000000) ≤ -Real.log (1000000 / 1642897) ∧
    -Real.log (1000000 / 1642897) ≤ (496461147 / 1000000000) := by
  have h := checkLog_sound (w := (642897 / 2642897)) (n := 12)
    (lo := (248230573 / 500000000)) (hi := (496461147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642897 / 1000000) = 1/(1000000 / 1642897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (248230573 / 500000000) (496461147 / 1000000000) (Real.log (1642897 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1642897 / 1000000) = -Real.log (1000000 / 1642897) := by
    rw [show ((1642897 / 1000000) : ℝ) = ((1000000 / 1642897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (514865511 / 500000000) ≤ -Real.log (357103 / 1000000) ∧
    -Real.log (357103 / 1000000) ≤ (64358189 / 62500000) := by
  have h := checkLog_sound (w := (142897 / 857103)) (n := 12)
    (lo := (168291921 / 500000000)) (hi := (336583843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357103) = 1/(357103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-64358189 / 62500000) (-514865511 / 500000000) (Real.log (357103 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (249309209 / 500000000) ≤ -Real.log (200000 / 329289) ∧
    -Real.log (200000 / 329289) ≤ (498618419 / 1000000000) := by
  have h := checkLog_sound (w := (129289 / 529289)) (n := 12)
    (lo := (249309209 / 500000000)) (hi := (498618419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329289 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329289 / 200000) = 1/(200000 / 329289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (249309209 / 500000000) (498618419 / 1000000000) (Real.log (329289 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (329289 / 200000) = -Real.log (200000 / 329289) := by
    rw [show ((329289 / 200000) : ℝ) = ((200000 / 329289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (519858109 / 500000000) ≤ -Real.log (70711 / 200000) ∧
    -Real.log (70711 / 200000) ≤ (51985811 / 50000000) := by
  have h := checkLog_sound (w := (29289 / 170711)) (n := 12)
    (lo := (173284519 / 500000000)) (hi := (346569039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70711) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70711) = 1/(70711 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-51985811 / 50000000) (-519858109 / 500000000) (Real.log (70711 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (504597671 / 250000000) ≤ -Real.log (500000000000 / 3763101576921) ∧
    -Real.log (500000000000 / 3763101576921) ≤ (2018390687 / 1000000000) := by
  have h := checkLog_sound (w := (1763101576921 / 5763101576921)) (n := 12)
    (lo := (158024081 / 250000000)) (hi := (25283853 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3763101576921 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3763101576921 / 2000000000000) = 1/(500000000000 / 3763101576921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (504597671 / 250000000) (2018390687 / 1000000000) (Real.log (3763101576921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3763101576921 / 500000000000) = -Real.log (500000000000 / 3763101576921) := by
    rw [show ((3763101576921 / 500000000000) : ℝ) = ((500000000000 / 3763101576921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2033839719 / 1000000000) ≤ -Real.log (500000000000 / 3821689261899) ∧
    -Real.log (500000000000 / 3821689261899) ≤ (1016919861 / 500000000) := by
  have h := checkLog_sound (w := (1821689261899 / 5821689261899)) (n := 12)
    (lo := (647545359 / 1000000000)) (hi := (8094317 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821689261899 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3821689261899 / 2000000000000) = 1/(500000000000 / 3821689261899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2033839719 / 1000000000) (1016919861 / 500000000) (Real.log (3821689261899 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3821689261899 / 500000000000) = -Real.log (500000000000 / 3821689261899) := by
    rw [show ((3821689261899 / 500000000000) : ℝ) = ((500000000000 / 3821689261899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1526192169 / 1000000000) ≤ -Real.log (125000000000 / 575078128719) ∧
    -Real.log (125000000000 / 575078128719) ≤ (381548043 / 250000000) := by
  have h := checkLog_sound (w := (75078128719 / 1075078128719)) (n := 12)
    (lo := (139897809 / 1000000000)) (hi := (13989781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575078128719 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575078128719 / 500000000000) = 1/(125000000000 / 575078128719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1526192169 / 1000000000) (381548043 / 250000000) (Real.log (575078128719 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (575078128719 / 125000000000) = -Real.log (125000000000 / 575078128719) := by
    rw [show ((575078128719 / 125000000000) : ℝ) = ((125000000000 / 575078128719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (307666927 / 200000000) ≤ -Real.log (500000000000 / 2328414249551) ∧
    -Real.log (500000000000 / 2328414249551) ≤ (769167319 / 500000000) := by
  have h := checkLog_sound (w := (328414249551 / 4328414249551)) (n := 12)
    (lo := (6081611 / 40000000)) (hi := (38010069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2328414249551 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2328414249551 / 2000000000000) = 1/(500000000000 / 2328414249551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (307666927 / 200000000) (769167319 / 500000000) (Real.log (2328414249551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2328414249551 / 500000000000) = -Real.log (500000000000 / 2328414249551) := by
    rw [show ((2328414249551 / 500000000000) : ℝ) = ((500000000000 / 2328414249551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0014
