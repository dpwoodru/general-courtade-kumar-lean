import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0166
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

theorem reflection_log_1_neg : (320495013 / 500000000) ≤ -Real.log (12800 / 24299) ∧
    -Real.log (12800 / 24299) ≤ (640990027 / 1000000000) := by
  have h := checkLog_sound (w := (11499 / 37099)) (n := 12)
    (lo := (320495013 / 500000000)) (hi := (640990027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24299 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24299 / 12800) = 1/(12800 / 24299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320495013 / 500000000) (640990027 / 1000000000) (Real.log (24299 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24299 / 12800) = -Real.log (12800 / 24299) := by
    rw [show ((24299 / 12800) : ℝ) = ((12800 / 24299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2286311969 / 1000000000) ≤ -Real.log (1301 / 12800) ∧
    -Real.log (1301 / 12800) ≤ (2286311973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1301) = 1/(1301 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2286311973 / 1000000000) (-2286311969 / 1000000000) (Real.log (1301 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
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


theorem reflection_log_3 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
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


theorem reflection_log_4 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (146490521 / 250000000) ≤ -Real.log (6400 / 11499) ∧
    -Real.log (6400 / 11499) ≤ (117192417 / 200000000) := by
  have h := checkLog_sound (w := (5099 / 17899)) (n := 12)
    (lo := (146490521 / 250000000)) (hi := (117192417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11499 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11499 / 6400) = 1/(6400 / 11499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (146490521 / 250000000) (117192417 / 200000000) (Real.log (11499 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11499 / 6400) = -Real.log (6400 / 11499) := by
    rw [show ((11499 / 6400) : ℝ) = ((6400 / 11499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1593164789 / 1000000000) ≤ -Real.log (1301 / 6400) ∧
    -Real.log (1301 / 6400) ≤ (199145599 / 125000000) := by
  have h := checkLog_sound (w := (299 / 2901)) (n := 12)
    (lo := (206870429 / 1000000000)) (hi := (20687043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1301) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1301) = 1/(1301 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-199145599 / 125000000) (-1593164789 / 1000000000) (Real.log (1301 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
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


theorem reflection_log_7 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
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


theorem reflection_log_8 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (652977577 / 1000000000) ≤ -Real.log (1000000 / 1921253) ∧
    -Real.log (1000000 / 1921253) ≤ (326488789 / 500000000) := by
  have h := checkLog_sound (w := (921253 / 2921253)) (n := 12)
    (lo := (652977577 / 1000000000)) (hi := (326488789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921253 / 1000000) = 1/(1000000 / 1921253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (652977577 / 1000000000) (326488789 / 500000000) (Real.log (1921253 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1921253 / 1000000) = -Real.log (1000000 / 1921253) := by
    rw [show ((1921253 / 1000000) : ℝ) = ((1000000 / 1921253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (508303019 / 200000000) ≤ -Real.log (78747 / 1000000) ∧
    -Real.log (78747 / 1000000) ≤ (2541515099 / 1000000000) := by
  have h := checkLog_sound (w := (46253 / 203747)) (n := 12)
    (lo := (92414711 / 200000000)) (hi := (115518389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 78747) = 1/(78747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2541515099 / 1000000000) (-508303019 / 200000000) (Real.log (78747 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (653501577 / 1000000000) ≤ -Real.log (50000 / 96113) ∧
    -Real.log (50000 / 96113) ≤ (326750789 / 500000000) := by
  have h := checkLog_sound (w := (46113 / 146113)) (n := 12)
    (lo := (653501577 / 1000000000)) (hi := (326750789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96113 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96113 / 50000) = 1/(50000 / 96113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (653501577 / 1000000000) (326750789 / 500000000) (Real.log (96113 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (96113 / 50000) = -Real.log (50000 / 96113) := by
    rw [show ((96113 / 50000) : ℝ) = ((50000 / 96113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2554385351 / 1000000000) ≤ -Real.log (3887 / 50000) ∧
    -Real.log (3887 / 50000) ≤ (510877071 / 200000000) := by
  have h := checkLog_sound (w := (2363 / 10137)) (n := 12)
    (lo := (474943811 / 1000000000)) (hi := (118735953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 3887) = 1/(3887 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-510877071 / 200000000) (-2554385351 / 1000000000) (Real.log (3887 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (130330617 / 200000000) ≤ -Real.log (100000 / 191871) ∧
    -Real.log (100000 / 191871) ≤ (325826543 / 500000000) := by
  have h := checkLog_sound (w := (91871 / 291871)) (n := 12)
    (lo := (130330617 / 200000000)) (hi := (325826543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191871 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191871 / 100000) = 1/(100000 / 191871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (130330617 / 200000000) (325826543 / 500000000) (Real.log (191871 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (191871 / 100000) = -Real.log (100000 / 191871) := by
    rw [show ((191871 / 100000) : ℝ) = ((100000 / 191871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2509732269 / 1000000000) ≤ -Real.log (8129 / 100000) ∧
    -Real.log (8129 / 100000) ≤ (2509732273 / 1000000000) := by
  have h := checkLog_sound (w := (4371 / 20629)) (n := 12)
    (lo := (430290729 / 1000000000)) (hi := (43029073 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 8129) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 8129) = 1/(8129 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2509732273 / 1000000000) (-2509732269 / 1000000000) (Real.log (8129 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (130444411 / 200000000) ≤ -Real.log (500000 / 959901) ∧
    -Real.log (500000 / 959901) ≤ (81527757 / 125000000) := by
  have h := checkLog_sound (w := (459901 / 1459901)) (n := 12)
    (lo := (130444411 / 200000000)) (hi := (81527757 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959901 / 500000) = 1/(500000 / 959901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130444411 / 200000000) (81527757 / 125000000) (Real.log (959901 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (959901 / 500000) = -Real.log (500000 / 959901) := by
    rw [show ((959901 / 500000) : ℝ) = ((500000 / 959901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25232567 / 10000000) ≤ -Real.log (40099 / 500000) ∧
    -Real.log (40099 / 500000) ≤ (19712943 / 7812500) := by
  have h := checkLog_sound (w := (22401 / 102599)) (n := 12)
    (lo := (11095379 / 25000000)) (hi := (443815161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40099) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 40099) = 1/(40099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-19712943 / 7812500) (-25232567 / 10000000) (Real.log (40099 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (12478487 / 3906250) ≤ -Real.log (500000000000 / 12198896465897) ∧
    -Real.log (500000000000 / 12198896465897) ≤ (3194492677 / 1000000000) := by
  have h := checkLog_sound (w := (4198896465897 / 20198896465897)) (n := 12)
    (lo := (26368997 / 62500000)) (hi := (421903953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12198896465897 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12198896465897 / 8000000000000) = 1/(500000000000 / 12198896465897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (12478487 / 3906250) (3194492677 / 1000000000) (Real.log (12198896465897 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12198896465897 / 500000000000) = -Real.log (500000000000 / 12198896465897) := by
    rw [show ((12198896465897 / 500000000000) : ℝ) = ((500000000000 / 12198896465897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200492933 / 62500000) ≤ -Real.log (500000000000 / 12363390789813) ∧
    -Real.log (500000000000 / 12363390789813) ≤ (3207886933 / 1000000000) := by
  have h := checkLog_sound (w := (4363390789813 / 20363390789813)) (n := 12)
    (lo := (13603069 / 31250000)) (hi := (435298209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12363390789813 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12363390789813 / 8000000000000) = 1/(500000000000 / 12363390789813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200492933 / 62500000) (3207886933 / 1000000000) (Real.log (12363390789813 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12363390789813 / 500000000000) = -Real.log (500000000000 / 12363390789813) := by
    rw [show ((12363390789813 / 500000000000) : ℝ) = ((500000000000 / 12363390789813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1580692677 / 500000000) ≤ -Real.log (500000000000 / 11801636117603) ∧
    -Real.log (500000000000 / 11801636117603) ≤ (3161385359 / 1000000000) := by
  have h := checkLog_sound (w := (3801636117603 / 19801636117603)) (n := 12)
    (lo := (194398317 / 500000000)) (hi := (77759327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801636117603 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11801636117603 / 8000000000000) = 1/(500000000000 / 11801636117603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1580692677 / 500000000) (3161385359 / 1000000000) (Real.log (11801636117603 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11801636117603 / 500000000000) = -Real.log (500000000000 / 11801636117603) := by
    rw [show ((11801636117603 / 500000000000) : ℝ) = ((500000000000 / 11801636117603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (635095751 / 200000000) ≤ -Real.log (500000000000 / 11969138881269) ∧
    -Real.log (500000000000 / 11969138881269) ≤ (79386969 / 25000000) := by
  have h := checkLog_sound (w := (3969138881269 / 19969138881269)) (n := 12)
    (lo := (80578007 / 200000000)) (hi := (100722509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969138881269 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11969138881269 / 8000000000000) = 1/(500000000000 / 11969138881269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (635095751 / 200000000) (79386969 / 25000000) (Real.log (11969138881269 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11969138881269 / 500000000000) = -Real.log (500000000000 / 11969138881269) := by
    rw [show ((11969138881269 / 500000000000) : ℝ) = ((500000000000 / 11969138881269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0166
