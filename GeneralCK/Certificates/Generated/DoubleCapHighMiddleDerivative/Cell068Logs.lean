import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell068
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

theorem reflection_log_1_neg : (254975253 / 1000000000) ≤ -Real.log (5120 / 6607) ∧
    -Real.log (5120 / 6607) ≤ (127487627 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 11727)) (n := 12)
    (lo := (254975253 / 1000000000)) (hi := (127487627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6607 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6607 / 5120) = 1/(5120 / 6607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254975253 / 1000000000) (127487627 / 500000000) (Real.log (6607 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6607 / 5120) = -Real.log (5120 / 6607) := by
    rw [show ((6607 / 5120) : ℝ) = ((5120 / 6607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (68619137 / 200000000) ≤ -Real.log (3633 / 5120) ∧
    -Real.log (3633 / 5120) ≤ (171547843 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 8753)) (n := 12)
    (lo := (68619137 / 200000000)) (hi := (171547843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3633) = 1/(3633 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-171547843 / 500000000) (-68619137 / 200000000) (Real.log (3633 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254521087 / 1000000000) ≤ -Real.log (1280 / 1651) ∧
    -Real.log (1280 / 1651) ≤ (994223 / 3906250) := by
  have h := checkLog_sound (w := (371 / 2931)) (n := 12)
    (lo := (254521087 / 1000000000)) (hi := (994223 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651 / 1280) = 1/(1280 / 1651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254521087 / 1000000000) (994223 / 3906250) (Real.log (1651 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1651 / 1280) = -Real.log (1280 / 1651) := by
    rw [show ((1651 / 1280) : ℝ) = ((1280 / 1651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (171135131 / 500000000) ≤ -Real.log (909 / 1280) ∧
    -Real.log (909 / 1280) ≤ (342270263 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 909) = 1/(909 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-342270263 / 1000000000) (-171135131 / 500000000) (Real.log (909 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (37410901 / 200000000) ≤ -Real.log (1000000 / 1205693) ∧
    -Real.log (1000000 / 1205693) ≤ (93527253 / 500000000) := by
  have h := checkLog_sound (w := (205693 / 2205693)) (n := 12)
    (lo := (37410901 / 200000000)) (hi := (93527253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205693 / 1000000) = 1/(1000000 / 1205693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (37410901 / 200000000) (93527253 / 500000000) (Real.log (1205693 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1205693 / 1000000) = -Real.log (1000000 / 1205693) := by
    rw [show ((1205693 / 1000000) : ℝ) = ((1000000 / 1205693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (115142621 / 500000000) ≤ -Real.log (794307 / 1000000) ∧
    -Real.log (794307 / 1000000) ≤ (230285243 / 1000000000) := by
  have h := checkLog_sound (w := (205693 / 1794307)) (n := 12)
    (lo := (115142621 / 500000000)) (hi := (230285243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794307) = 1/(794307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-230285243 / 1000000000) (-115142621 / 500000000) (Real.log (794307 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23425349 / 125000000) ≤ -Real.log (1000000 / 1206113) ∧
    -Real.log (1000000 / 1206113) ≤ (187402793 / 1000000000) := by
  have h := checkLog_sound (w := (206113 / 2206113)) (n := 12)
    (lo := (23425349 / 125000000)) (hi := (187402793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206113 / 1000000) = 1/(1000000 / 1206113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23425349 / 125000000) (187402793 / 1000000000) (Real.log (1206113 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1206113 / 1000000) = -Real.log (1000000 / 1206113) := by
    rw [show ((1206113 / 1000000) : ℝ) = ((1000000 / 1206113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (46162829 / 200000000) ≤ -Real.log (793887 / 1000000) ∧
    -Real.log (793887 / 1000000) ≤ (115407073 / 500000000) := by
  have h := checkLog_sound (w := (206113 / 1793887)) (n := 12)
    (lo := (46162829 / 200000000)) (hi := (115407073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793887) = 1/(793887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115407073 / 500000000) (-46162829 / 200000000) (Real.log (793887 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27460131 / 200000000) ≤ -Real.log (1000000 / 1147173) ∧
    -Real.log (1000000 / 1147173) ≤ (8581291 / 62500000) := by
  have h := checkLog_sound (w := (147173 / 2147173)) (n := 12)
    (lo := (27460131 / 200000000)) (hi := (8581291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147173 / 1000000) = 1/(1000000 / 1147173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27460131 / 200000000) (8581291 / 62500000) (Real.log (1147173 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1147173 / 1000000) = -Real.log (1000000 / 1147173) := by
    rw [show ((1147173 / 1000000) : ℝ) = ((1000000 / 1147173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31839713 / 200000000) ≤ -Real.log (852827 / 1000000) ∧
    -Real.log (852827 / 1000000) ≤ (79599283 / 500000000) := by
  have h := checkLog_sound (w := (147173 / 1852827)) (n := 12)
    (lo := (31839713 / 200000000)) (hi := (79599283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852827) = 1/(852827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-79599283 / 500000000) (-31839713 / 200000000) (Real.log (852827 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27513821 / 200000000) ≤ -Real.log (1000000 / 1147481) ∧
    -Real.log (1000000 / 1147481) ≤ (68784553 / 500000000) := by
  have h := checkLog_sound (w := (147481 / 2147481)) (n := 12)
    (lo := (27513821 / 200000000)) (hi := (68784553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147481 / 1000000) = 1/(1000000 / 1147481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27513821 / 200000000) (68784553 / 500000000) (Real.log (1147481 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1147481 / 1000000) = -Real.log (1000000 / 1147481) := by
    rw [show ((1147481 / 1000000) : ℝ) = ((1000000 / 1147481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79779891 / 500000000) ≤ -Real.log (852519 / 1000000) ∧
    -Real.log (852519 / 1000000) ≤ (159559783 / 1000000000) := by
  have h := checkLog_sound (w := (147481 / 1852519)) (n := 12)
    (lo := (79779891 / 500000000)) (hi := (159559783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852519) = 1/(852519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159559783 / 1000000000) (-79779891 / 500000000) (Real.log (852519 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (596791349 / 1000000000) ≤ -Real.log (500000000000 / 908140814081) ∧
    -Real.log (500000000000 / 908140814081) ≤ (11935827 / 20000000) := by
  have h := checkLog_sound (w := (408140814081 / 1408140814081)) (n := 12)
    (lo := (596791349 / 1000000000)) (hi := (11935827 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908140814081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908140814081 / 500000000000) = 1/(500000000000 / 908140814081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (596791349 / 1000000000) (11935827 / 20000000) (Real.log (908140814081 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (908140814081 / 500000000000) = -Real.log (500000000000 / 908140814081) := by
    rw [show ((908140814081 / 500000000000) : ℝ) = ((500000000000 / 908140814081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (598070939 / 1000000000) ≤ -Real.log (125000000000 / 227325901459) ∧
    -Real.log (125000000000 / 227325901459) ≤ (29903547 / 50000000) := by
  have h := checkLog_sound (w := (102325901459 / 352325901459)) (n := 12)
    (lo := (598070939 / 1000000000)) (hi := (29903547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227325901459 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227325901459 / 125000000000) = 1/(125000000000 / 227325901459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (598070939 / 1000000000) (29903547 / 50000000) (Real.log (227325901459 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (227325901459 / 125000000000) = -Real.log (125000000000 / 227325901459) := by
    rw [show ((227325901459 / 125000000000) : ℝ) = ((125000000000 / 227325901459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (417339747 / 1000000000) ≤ -Real.log (500000000000 / 758959067463) ∧
    -Real.log (500000000000 / 758959067463) ≤ (104334937 / 250000000) := by
  have h := checkLog_sound (w := (258959067463 / 1258959067463)) (n := 12)
    (lo := (417339747 / 1000000000)) (hi := (104334937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758959067463 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758959067463 / 500000000000) = 1/(500000000000 / 758959067463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (417339747 / 1000000000) (104334937 / 250000000) (Real.log (758959067463 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (758959067463 / 500000000000) = -Real.log (500000000000 / 758959067463) := by
    rw [show ((758959067463 / 500000000000) : ℝ) = ((500000000000 / 758959067463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (418216937 / 1000000000) ≤ -Real.log (4000000000 / 6077000883) ∧
    -Real.log (4000000000 / 6077000883) ≤ (209108469 / 500000000) := by
  have h := checkLog_sound (w := (2077000883 / 10077000883)) (n := 12)
    (lo := (418216937 / 1000000000)) (hi := (209108469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6077000883 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6077000883 / 4000000000) = 1/(4000000000 / 6077000883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (418216937 / 1000000000) (209108469 / 500000000) (Real.log (6077000883 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6077000883 / 4000000000) = -Real.log (4000000000 / 6077000883) := by
    rw [show ((6077000883 / 4000000000) : ℝ) = ((4000000000 / 6077000883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14824961 / 50000000) ≤ -Real.log (10000000000 / 13451415117) ∧
    -Real.log (10000000000 / 13451415117) ≤ (296499221 / 1000000000) := by
  have h := checkLog_sound (w := (3451415117 / 23451415117)) (n := 12)
    (lo := (14824961 / 50000000)) (hi := (296499221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13451415117 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13451415117 / 10000000000) = 1/(10000000000 / 13451415117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14824961 / 50000000) (296499221 / 1000000000) (Real.log (13451415117 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13451415117 / 10000000000) = -Real.log (10000000000 / 13451415117) := by
    rw [show ((13451415117 / 10000000000) : ℝ) = ((10000000000 / 13451415117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (297128887 / 1000000000) ≤ -Real.log (125000000000 / 168248596219) ∧
    -Real.log (125000000000 / 168248596219) ≤ (37141111 / 125000000) := by
  have h := checkLog_sound (w := (43248596219 / 293248596219)) (n := 12)
    (lo := (297128887 / 1000000000)) (hi := (37141111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168248596219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168248596219 / 125000000000) = 1/(125000000000 / 168248596219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (297128887 / 1000000000) (37141111 / 125000000) (Real.log (168248596219 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (168248596219 / 125000000000) = -Real.log (125000000000 / 168248596219) := by
    rw [show ((168248596219 / 125000000000) : ℝ) = ((125000000000 / 168248596219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21990677 / 1000000000) ≤ -Real.log (978249354639 / 1000000000000) ∧
    -Real.log (978249354639 / 1000000000000) ≤ (10995339 / 500000000) := by
  have h := checkLog_sound (w := (21750645361 / 1978249354639)) (n := 12)
    (lo := (21990677 / 1000000000)) (hi := (10995339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978249354639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978249354639) = 1/(978249354639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10995339 / 500000000) (-21990677 / 1000000000) (Real.log (978249354639 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2189791 / 100000000) ≤ -Real.log (978340108071 / 1000000000000) ∧
    -Real.log (978340108071 / 1000000000000) ≤ (21897911 / 1000000000) := by
  have h := checkLog_sound (w := (21659891929 / 1978340108071)) (n := 12)
    (lo := (2189791 / 100000000)) (hi := (21897911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978340108071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978340108071) = 1/(978340108071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21897911 / 1000000000) (-2189791 / 100000000) (Real.log (978340108071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell068
