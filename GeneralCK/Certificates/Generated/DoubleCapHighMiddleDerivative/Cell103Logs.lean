import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell103
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (27074253 / 100000000) ≤ -Real.log (640 / 839) ∧
    -Real.log (640 / 839) ≤ (270742531 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1479)) (n := 12)
    (lo := (27074253 / 100000000)) (hi := (270742531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839 / 640) = 1/(640 / 839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27074253 / 100000000) (270742531 / 1000000000) (Real.log (839 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (839 / 640) = -Real.log (640 / 839) := by
    rw [show ((839 / 640) : ℝ) = ((640 / 839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3724233 / 10000000) ≤ -Real.log (441 / 640) ∧
    -Real.log (441 / 640) ≤ (372423301 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 441) = 1/(441 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-372423301 / 1000000000) (-3724233 / 10000000) (Real.log (441 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (270295469 / 1000000000) ≤ -Real.log (5120 / 6709) ∧
    -Real.log (5120 / 6709) ≤ (27029547 / 100000000) := by
  have h := checkLog_sound (w := (1589 / 11829)) (n := 12)
    (lo := (270295469 / 1000000000)) (hi := (27029547 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6709 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6709 / 5120) = 1/(5120 / 6709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (270295469 / 1000000000) (27029547 / 100000000) (Real.log (6709 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6709 / 5120) = -Real.log (5120 / 6709) := by
    rw [show ((6709 / 5120) : ℝ) = ((5120 / 6709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (185786661 / 500000000) ≤ -Real.log (3531 / 5120) ∧
    -Real.log (3531 / 5120) ≤ (371573323 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 8651)) (n := 12)
    (lo := (185786661 / 500000000)) (hi := (371573323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3531) = 1/(3531 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-371573323 / 1000000000) (-185786661 / 500000000) (Real.log (3531 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24894159 / 125000000) ≤ -Real.log (1000000 / 1220369) ∧
    -Real.log (1000000 / 1220369) ≤ (199153273 / 1000000000) := by
  have h := checkLog_sound (w := (220369 / 2220369)) (n := 12)
    (lo := (24894159 / 125000000)) (hi := (199153273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220369 / 1000000) = 1/(1000000 / 1220369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24894159 / 125000000) (199153273 / 1000000000) (Real.log (1220369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1220369 / 1000000) = -Real.log (1000000 / 1220369) := by
    rw [show ((1220369 / 1000000) : ℝ) = ((1000000 / 1220369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (62233637 / 250000000) ≤ -Real.log (779631 / 1000000) ∧
    -Real.log (779631 / 1000000) ≤ (248934549 / 1000000000) := by
  have h := checkLog_sound (w := (220369 / 1779631)) (n := 12)
    (lo := (62233637 / 250000000)) (hi := (248934549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779631) = 1/(779631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248934549 / 1000000000) (-62233637 / 250000000) (Real.log (779631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19949819 / 100000000) ≤ -Real.log (100000 / 122079) ∧
    -Real.log (100000 / 122079) ≤ (199498191 / 1000000000) := by
  have h := checkLog_sound (w := (22079 / 222079)) (n := 12)
    (lo := (19949819 / 100000000)) (hi := (199498191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122079 / 100000) = 1/(100000 / 122079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19949819 / 100000000) (199498191 / 1000000000) (Real.log (122079 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (122079 / 100000) = -Real.log (100000 / 122079) := by
    rw [show ((122079 / 100000) : ℝ) = ((100000 / 122079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (249474693 / 1000000000) ≤ -Real.log (77921 / 100000) ∧
    -Real.log (77921 / 100000) ≤ (124737347 / 500000000) := by
  have h := checkLog_sound (w := (22079 / 177921)) (n := 12)
    (lo := (249474693 / 1000000000)) (hi := (124737347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77921) = 1/(77921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124737347 / 500000000) (-249474693 / 1000000000) (Real.log (77921 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91657 / 625000) ≤ -Real.log (20000 / 23159) ∧
    -Real.log (20000 / 23159) ≤ (146651201 / 1000000000) := by
  have h := checkLog_sound (w := (3159 / 43159)) (n := 12)
    (lo := (91657 / 625000)) (hi := (146651201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23159 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23159 / 20000) = 1/(20000 / 23159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91657 / 625000) (146651201 / 1000000000) (Real.log (23159 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (23159 / 20000) = -Real.log (20000 / 23159) := by
    rw [show ((23159 / 20000) : ℝ) = ((20000 / 23159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42978971 / 250000000) ≤ -Real.log (16841 / 20000) ∧
    -Real.log (16841 / 20000) ≤ (34383177 / 200000000) := by
  have h := checkLog_sound (w := (3159 / 36841)) (n := 12)
    (lo := (42978971 / 250000000)) (hi := (34383177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16841) = 1/(16841 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34383177 / 200000000) (-42978971 / 250000000) (Real.log (16841 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73459439 / 500000000) ≤ -Real.log (50000 / 57913) ∧
    -Real.log (50000 / 57913) ≤ (146918879 / 1000000000) := by
  have h := checkLog_sound (w := (7913 / 107913)) (n := 12)
    (lo := (73459439 / 500000000)) (hi := (146918879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57913 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57913 / 50000) = 1/(50000 / 57913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73459439 / 500000000) (146918879 / 1000000000) (Real.log (57913 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (57913 / 50000) = -Real.log (50000 / 57913) := by
    rw [show ((57913 / 50000) : ℝ) = ((50000 / 57913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (172284101 / 1000000000) ≤ -Real.log (42087 / 50000) ∧
    -Real.log (42087 / 50000) ≤ (86142051 / 500000000) := by
  have h := checkLog_sound (w := (7913 / 92087)) (n := 12)
    (lo := (172284101 / 1000000000)) (hi := (86142051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42087) = 1/(42087 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86142051 / 500000000) (-172284101 / 1000000000) (Real.log (42087 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (641868791 / 1000000000) ≤ -Real.log (250000000000 / 475007080147) ∧
    -Real.log (250000000000 / 475007080147) ≤ (80233599 / 125000000) := by
  have h := checkLog_sound (w := (225007080147 / 725007080147)) (n := 12)
    (lo := (641868791 / 1000000000)) (hi := (80233599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475007080147 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475007080147 / 250000000000) = 1/(250000000000 / 475007080147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (641868791 / 1000000000) (80233599 / 125000000) (Real.log (475007080147 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (475007080147 / 250000000000) = -Real.log (250000000000 / 475007080147) := by
    rw [show ((475007080147 / 250000000000) : ℝ) = ((250000000000 / 475007080147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (643165831 / 1000000000) ≤ -Real.log (500000000000 / 951247165533) ∧
    -Real.log (500000000000 / 951247165533) ≤ (80395729 / 125000000) := by
  have h := checkLog_sound (w := (451247165533 / 1451247165533)) (n := 12)
    (lo := (643165831 / 1000000000)) (hi := (80395729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951247165533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951247165533 / 500000000000) = 1/(500000000000 / 951247165533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (643165831 / 1000000000) (80395729 / 125000000) (Real.log (951247165533 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (951247165533 / 500000000000) = -Real.log (500000000000 / 951247165533) := by
    rw [show ((951247165533 / 500000000000) : ℝ) = ((500000000000 / 951247165533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22404391 / 50000000) ≤ -Real.log (125000000000 / 195664519497) ∧
    -Real.log (125000000000 / 195664519497) ≤ (448087821 / 1000000000) := by
  have h := checkLog_sound (w := (70664519497 / 320664519497)) (n := 12)
    (lo := (22404391 / 50000000)) (hi := (448087821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195664519497 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195664519497 / 125000000000) = 1/(125000000000 / 195664519497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22404391 / 50000000) (448087821 / 1000000000) (Real.log (195664519497 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (195664519497 / 125000000000) = -Real.log (125000000000 / 195664519497) := by
    rw [show ((195664519497 / 125000000000) : ℝ) = ((125000000000 / 195664519497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (448972883 / 1000000000) ≤ -Real.log (500000000000 / 783351086357) ∧
    -Real.log (500000000000 / 783351086357) ≤ (112243221 / 250000000) := by
  have h := checkLog_sound (w := (283351086357 / 1283351086357)) (n := 12)
    (lo := (448972883 / 1000000000)) (hi := (112243221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783351086357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783351086357 / 500000000000) = 1/(500000000000 / 783351086357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (448972883 / 1000000000) (112243221 / 250000000) (Real.log (783351086357 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (783351086357 / 500000000000) = -Real.log (500000000000 / 783351086357) := by
    rw [show ((783351086357 / 500000000000) : ℝ) = ((500000000000 / 783351086357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79641771 / 250000000) ≤ -Real.log (500000000000 / 687577934801) ∧
    -Real.log (500000000000 / 687577934801) ≤ (63713417 / 200000000) := by
  have h := checkLog_sound (w := (187577934801 / 1187577934801)) (n := 12)
    (lo := (79641771 / 250000000)) (hi := (63713417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687577934801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687577934801 / 500000000000) = 1/(500000000000 / 687577934801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79641771 / 250000000) (63713417 / 200000000) (Real.log (687577934801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (687577934801 / 500000000000) = -Real.log (500000000000 / 687577934801) := by
    rw [show ((687577934801 / 500000000000) : ℝ) = ((500000000000 / 687577934801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (15960149 / 50000000) ≤ -Real.log (250000000000 / 344007650819) ∧
    -Real.log (250000000000 / 344007650819) ≤ (319202981 / 1000000000) := by
  have h := checkLog_sound (w := (94007650819 / 594007650819)) (n := 12)
    (lo := (15960149 / 50000000)) (hi := (319202981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344007650819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344007650819 / 250000000000) = 1/(250000000000 / 344007650819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (15960149 / 50000000) (319202981 / 1000000000) (Real.log (344007650819 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (344007650819 / 250000000000) = -Real.log (250000000000 / 344007650819) := by
    rw [show ((344007650819 / 250000000000) : ℝ) = ((250000000000 / 344007650819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12682611 / 500000000) ≤ -Real.log (2437384431 / 2500000000) ∧
    -Real.log (2437384431 / 2500000000) ≤ (25365223 / 1000000000) := by
  have h := checkLog_sound (w := (62615569 / 4937384431)) (n := 12)
    (lo := (12682611 / 500000000)) (hi := (25365223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2437384431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2437384431) = 1/(2437384431 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25365223 / 1000000000) (-12682611 / 500000000) (Real.log (2437384431 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25264683 / 1000000000) ≤ -Real.log (390020719 / 400000000) ∧
    -Real.log (390020719 / 400000000) ≤ (6316171 / 250000000) := by
  have h := checkLog_sound (w := (9979281 / 790020719)) (n := 12)
    (lo := (25264683 / 1000000000)) (hi := (6316171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 390020719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 390020719) = 1/(390020719 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6316171 / 250000000) (-25264683 / 1000000000) (Real.log (390020719 / 400000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell103
