import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0363
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

theorem reflection_log_1_neg : (209060473 / 1000000000) ≤ -Real.log (10240 / 12621) ∧
    -Real.log (10240 / 12621) ≤ (104530237 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 22861)) (n := 12)
    (lo := (209060473 / 1000000000)) (hi := (104530237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12621 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12621 / 10240) = 1/(10240 / 12621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (209060473 / 1000000000) (104530237 / 500000000) (Real.log (12621 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12621 / 10240) = -Real.log (10240 / 12621) := by
    rw [show ((12621 / 10240) : ℝ) = ((10240 / 12621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (264642247 / 1000000000) ≤ -Real.log (7859 / 10240) ∧
    -Real.log (7859 / 10240) ≤ (33080281 / 125000000) := by
  have h := checkLog_sound (w := (2381 / 18099)) (n := 12)
    (lo := (264642247 / 1000000000)) (hi := (33080281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7859) = 1/(7859 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-33080281 / 125000000) (-264642247 / 1000000000) (Real.log (7859 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104411373 / 500000000) ≤ -Real.log (5120 / 6309) ∧
    -Real.log (5120 / 6309) ≤ (208822747 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 11429)) (n := 12)
    (lo := (104411373 / 500000000)) (hi := (208822747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6309 / 5120) = 1/(5120 / 6309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104411373 / 500000000) (208822747 / 1000000000) (Real.log (6309 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6309 / 5120) = -Real.log (5120 / 6309) := by
    rw [show ((6309 / 5120) : ℝ) = ((5120 / 6309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16516287 / 62500000) ≤ -Real.log (3931 / 5120) ∧
    -Real.log (3931 / 5120) ≤ (264260593 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 9051)) (n := 12)
    (lo := (16516287 / 62500000)) (hi := (264260593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3931) = 1/(3931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-264260593 / 1000000000) (-16516287 / 62500000) (Real.log (3931 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76376381 / 200000000) ≤ -Real.log (5120 / 7501) ∧
    -Real.log (5120 / 7501) ≤ (190940953 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 12621)) (n := 12)
    (lo := (76376381 / 200000000)) (hi := (190940953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7501 / 5120) = 1/(5120 / 7501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76376381 / 200000000) (190940953 / 500000000) (Real.log (7501 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7501 / 5120) = -Real.log (5120 / 7501) := by
    rw [show ((7501 / 5120) : ℝ) = ((5120 / 7501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156390387 / 250000000) ≤ -Real.log (2739 / 5120) ∧
    -Real.log (2739 / 5120) ≤ (625561549 / 1000000000) := by
  have h := checkLog_sound (w := (2381 / 7859)) (n := 12)
    (lo := (156390387 / 250000000)) (hi := (625561549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2739) = 1/(2739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-625561549 / 1000000000) (-156390387 / 250000000) (Real.log (2739 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (381481879 / 1000000000) ≤ -Real.log (2560 / 3749) ∧
    -Real.log (2560 / 3749) ≤ (9537047 / 25000000) := by
  have h := checkLog_sound (w := (1189 / 6309)) (n := 12)
    (lo := (381481879 / 1000000000)) (hi := (9537047 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3749 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3749 / 2560) = 1/(2560 / 3749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (381481879 / 1000000000) (9537047 / 25000000) (Real.log (3749 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3749 / 2560) = -Real.log (2560 / 3749) := by
    rw [show ((3749 / 2560) : ℝ) = ((2560 / 3749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (624466857 / 1000000000) ≤ -Real.log (1371 / 2560) ∧
    -Real.log (1371 / 2560) ≤ (312233429 / 500000000) := by
  have h := checkLog_sound (w := (1189 / 3931)) (n := 12)
    (lo := (624466857 / 1000000000)) (hi := (312233429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1371) = 1/(1371 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-312233429 / 500000000) (-624466857 / 1000000000) (Real.log (1371 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (143216521 / 500000000) ≤ -Real.log (1000000 / 1331669) ∧
    -Real.log (1000000 / 1331669) ≤ (286433043 / 1000000000) := by
  have h := checkLog_sound (w := (331669 / 2331669)) (n := 12)
    (lo := (143216521 / 500000000)) (hi := (286433043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331669 / 1000000) = 1/(1000000 / 1331669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (143216521 / 500000000) (286433043 / 1000000000) (Real.log (1331669 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1331669 / 1000000) = -Real.log (1000000 / 1331669) := by
    rw [show ((1331669 / 1000000) : ℝ) = ((1000000 / 1331669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (402971719 / 1000000000) ≤ -Real.log (668331 / 1000000) ∧
    -Real.log (668331 / 1000000) ≤ (10074293 / 25000000) := by
  have h := checkLog_sound (w := (331669 / 1668331)) (n := 12)
    (lo := (402971719 / 1000000000)) (hi := (10074293 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668331) = 1/(668331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10074293 / 25000000) (-402971719 / 1000000000) (Real.log (668331 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35844299 / 125000000) ≤ -Real.log (1000000 / 1332097) ∧
    -Real.log (1000000 / 1332097) ≤ (286754393 / 1000000000) := by
  have h := checkLog_sound (w := (332097 / 2332097)) (n := 12)
    (lo := (35844299 / 125000000)) (hi := (286754393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332097 / 1000000) = 1/(1000000 / 1332097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35844299 / 125000000) (286754393 / 1000000000) (Real.log (1332097 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1332097 / 1000000) = -Real.log (1000000 / 1332097) := by
    rw [show ((1332097 / 1000000) : ℝ) = ((1000000 / 1332097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16144493 / 40000000) ≤ -Real.log (667903 / 1000000) ∧
    -Real.log (667903 / 1000000) ≤ (201806163 / 500000000) := by
  have h := checkLog_sound (w := (332097 / 1667903)) (n := 12)
    (lo := (16144493 / 40000000)) (hi := (201806163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667903) = 1/(667903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201806163 / 500000000) (-16144493 / 40000000) (Real.log (667903 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (216633607 / 1000000000) ≤ -Real.log (1000000 / 1241889) ∧
    -Real.log (1000000 / 1241889) ≤ (27079201 / 125000000) := by
  have h := checkLog_sound (w := (241889 / 2241889)) (n := 12)
    (lo := (216633607 / 1000000000)) (hi := (27079201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241889 / 1000000) = 1/(1000000 / 1241889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (216633607 / 1000000000) (27079201 / 125000000) (Real.log (1241889 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1241889 / 1000000) = -Real.log (1000000 / 1241889) := by
    rw [show ((1241889 / 1000000) : ℝ) = ((1000000 / 1241889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138462733 / 500000000) ≤ -Real.log (758111 / 1000000) ∧
    -Real.log (758111 / 1000000) ≤ (276925467 / 1000000000) := by
  have h := checkLog_sound (w := (241889 / 1758111)) (n := 12)
    (lo := (138462733 / 500000000)) (hi := (276925467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758111) = 1/(758111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-276925467 / 1000000000) (-138462733 / 500000000) (Real.log (758111 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (216901711 / 1000000000) ≤ -Real.log (500000 / 621111) ∧
    -Real.log (500000 / 621111) ≤ (13556357 / 62500000) := by
  have h := checkLog_sound (w := (121111 / 1121111)) (n := 12)
    (lo := (216901711 / 1000000000)) (hi := (13556357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621111 / 500000) = 1/(500000 / 621111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (216901711 / 1000000000) (13556357 / 62500000) (Real.log (621111 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (621111 / 500000) = -Real.log (500000 / 621111) := by
    rw [show ((621111 / 500000) : ℝ) = ((500000 / 621111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (69341203 / 250000000) ≤ -Real.log (378889 / 500000) ∧
    -Real.log (378889 / 500000) ≤ (277364813 / 1000000000) := by
  have h := checkLog_sound (w := (121111 / 878889)) (n := 12)
    (lo := (69341203 / 250000000)) (hi := (277364813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378889) = 1/(378889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-277364813 / 1000000000) (-69341203 / 250000000) (Real.log (378889 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (689404761 / 1000000000) ≤ -Real.log (500000000000 / 996264575487) ∧
    -Real.log (500000000000 / 996264575487) ≤ (344702381 / 500000000) := by
  have h := checkLog_sound (w := (496264575487 / 1496264575487)) (n := 12)
    (lo := (689404761 / 1000000000)) (hi := (344702381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996264575487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996264575487 / 500000000000) = 1/(500000000000 / 996264575487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (689404761 / 1000000000) (344702381 / 500000000) (Real.log (996264575487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (996264575487 / 500000000000) = -Real.log (500000000000 / 996264575487) := by
    rw [show ((996264575487 / 500000000000) : ℝ) = ((500000000000 / 996264575487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (690366717 / 1000000000) ≤ -Real.log (500000000000 / 997223399207) ∧
    -Real.log (500000000000 / 997223399207) ≤ (345183359 / 500000000) := by
  have h := checkLog_sound (w := (497223399207 / 1497223399207)) (n := 12)
    (lo := (690366717 / 1000000000)) (hi := (345183359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997223399207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997223399207 / 500000000000) = 1/(500000000000 / 997223399207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (690366717 / 1000000000) (345183359 / 500000000) (Real.log (997223399207 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (997223399207 / 500000000000) = -Real.log (500000000000 / 997223399207) := by
    rw [show ((997223399207 / 500000000000) : ℝ) = ((500000000000 / 997223399207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (493559073 / 1000000000) ≤ -Real.log (500000000000 / 819068052039) ∧
    -Real.log (500000000000 / 819068052039) ≤ (246779537 / 500000000) := by
  have h := checkLog_sound (w := (319068052039 / 1319068052039)) (n := 12)
    (lo := (493559073 / 1000000000)) (hi := (246779537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819068052039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819068052039 / 500000000000) = 1/(500000000000 / 819068052039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (493559073 / 1000000000) (246779537 / 500000000) (Real.log (819068052039 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (819068052039 / 500000000000) = -Real.log (500000000000 / 819068052039) := by
    rw [show ((819068052039 / 500000000000) : ℝ) = ((500000000000 / 819068052039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (494266523 / 1000000000) ≤ -Real.log (500000000000 / 819647706849) ∧
    -Real.log (500000000000 / 819647706849) ≤ (123566631 / 250000000) := by
  have h := checkLog_sound (w := (319647706849 / 1319647706849)) (n := 12)
    (lo := (494266523 / 1000000000)) (hi := (123566631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819647706849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819647706849 / 500000000000) = 1/(500000000000 / 819647706849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (494266523 / 1000000000) (123566631 / 250000000) (Real.log (819647706849 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (819647706849 / 500000000000) = -Real.log (500000000000 / 819647706849) := by
    rw [show ((819647706849 / 500000000000) : ℝ) = ((500000000000 / 819647706849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0363
