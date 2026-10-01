import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0370
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

theorem reflection_log_1_neg : (103697597 / 500000000) ≤ -Real.log (256 / 315) ∧
    -Real.log (256 / 315) ≤ (41479039 / 200000000) := by
  have h := checkLog_sound (w := (59 / 571)) (n := 12)
    (lo := (103697597 / 500000000)) (hi := (41479039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315 / 256) = 1/(256 / 315) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (103697597 / 500000000) (41479039 / 200000000) (Real.log (315 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (315 / 256) = -Real.log (256 / 315) := by
    rw [show ((315 / 256) : ℝ) = ((256 / 315) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (52394743 / 200000000) ≤ -Real.log (197 / 256) ∧
    -Real.log (197 / 256) ≤ (65493429 / 250000000) := by
  have h := checkLog_sound (w := (59 / 453)) (n := 12)
    (lo := (52394743 / 200000000)) (hi := (65493429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 197) = 1/(197 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65493429 / 250000000) (-52394743 / 200000000) (Real.log (197 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20715707 / 100000000) ≤ -Real.log (10240 / 12597) ∧
    -Real.log (10240 / 12597) ≤ (207157071 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 22837)) (n := 12)
    (lo := (20715707 / 100000000)) (hi := (207157071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12597 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12597 / 10240) = 1/(10240 / 12597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20715707 / 100000000) (207157071 / 1000000000) (Real.log (12597 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12597 / 10240) = -Real.log (10240 / 12597) := by
    rw [show ((12597 / 10240) : ℝ) = ((10240 / 12597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (261593077 / 1000000000) ≤ -Real.log (7883 / 10240) ∧
    -Real.log (7883 / 10240) ≤ (130796539 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 18123)) (n := 12)
    (lo := (261593077 / 1000000000)) (hi := (130796539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7883) = 1/(7883 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-130796539 / 500000000) (-261593077 / 1000000000) (Real.log (7883 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23692397 / 62500000) ≤ -Real.log (128 / 187) ∧
    -Real.log (128 / 187) ≤ (379078353 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 315)) (n := 12)
    (lo := (23692397 / 62500000)) (hi := (379078353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187 / 128) = 1/(128 / 187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23692397 / 62500000) (379078353 / 1000000000) (Real.log (187 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (187 / 128) = -Real.log (128 / 187) := by
    rw [show ((187 / 128) : ℝ) = ((128 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617923759 / 1000000000) ≤ -Real.log (69 / 128) ∧
    -Real.log (69 / 128) ≤ (7724047 / 12500000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 69) = 1/(69 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-7724047 / 12500000) (-617923759 / 1000000000) (Real.log (69 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189338601 / 500000000) ≤ -Real.log (5120 / 7477) ∧
    -Real.log (5120 / 7477) ≤ (378677203 / 1000000000) := by
  have h := checkLog_sound (w := (2357 / 12597)) (n := 12)
    (lo := (189338601 / 500000000)) (hi := (378677203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7477 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7477 / 5120) = 1/(5120 / 7477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189338601 / 500000000) (378677203 / 1000000000) (Real.log (7477 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7477 / 5120) = -Real.log (5120 / 7477) := by
    rw [show ((7477 / 5120) : ℝ) = ((5120 / 7477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (616837393 / 1000000000) ≤ -Real.log (2763 / 5120) ∧
    -Real.log (2763 / 5120) ≤ (308418697 / 500000000) := by
  have h := checkLog_sound (w := (2357 / 7883)) (n := 12)
    (lo := (616837393 / 1000000000)) (hi := (308418697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2763) = 1/(2763 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-308418697 / 500000000) (-616837393 / 1000000000) (Real.log (2763 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28418371 / 100000000) ≤ -Real.log (1000000 / 1328677) ∧
    -Real.log (1000000 / 1328677) ≤ (284183711 / 1000000000) := by
  have h := checkLog_sound (w := (328677 / 2328677)) (n := 12)
    (lo := (28418371 / 100000000)) (hi := (284183711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328677 / 1000000) = 1/(1000000 / 1328677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28418371 / 100000000) (284183711 / 1000000000) (Real.log (1328677 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1328677 / 1000000) = -Real.log (1000000 / 1328677) := by
    rw [show ((1328677 / 1000000) : ℝ) = ((1000000 / 1328677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199252443 / 500000000) ≤ -Real.log (671323 / 1000000) ∧
    -Real.log (671323 / 1000000) ≤ (398504887 / 1000000000) := by
  have h := checkLog_sound (w := (328677 / 1671323)) (n := 12)
    (lo := (199252443 / 500000000)) (hi := (398504887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671323) = 1/(671323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-398504887 / 1000000000) (-199252443 / 500000000) (Real.log (671323 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (284505783 / 1000000000) ≤ -Real.log (200000 / 265821) ∧
    -Real.log (200000 / 265821) ≤ (35563223 / 125000000) := by
  have h := checkLog_sound (w := (65821 / 465821)) (n := 12)
    (lo := (284505783 / 1000000000)) (hi := (35563223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265821 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(265821 / 200000) = 1/(200000 / 265821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (284505783 / 1000000000) (35563223 / 125000000) (Real.log (265821 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (265821 / 200000) = -Real.log (200000 / 265821) := by
    rw [show ((265821 / 200000) : ℝ) = ((200000 / 265821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (399142637 / 1000000000) ≤ -Real.log (134179 / 200000) ∧
    -Real.log (134179 / 200000) ≤ (199571319 / 500000000) := by
  have h := checkLog_sound (w := (65821 / 334179)) (n := 12)
    (lo := (399142637 / 1000000000)) (hi := (199571319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 134179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 134179) = 1/(134179 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-199571319 / 500000000) (-399142637 / 1000000000) (Real.log (134179 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42953393 / 200000000) ≤ -Real.log (1000000 / 1239573) ∧
    -Real.log (1000000 / 1239573) ≤ (107383483 / 500000000) := by
  have h := checkLog_sound (w := (239573 / 2239573)) (n := 12)
    (lo := (42953393 / 200000000)) (hi := (107383483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239573 / 1000000) = 1/(1000000 / 1239573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42953393 / 200000000) (107383483 / 500000000) (Real.log (1239573 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1239573 / 1000000) = -Real.log (1000000 / 1239573) := by
    rw [show ((1239573 / 1000000) : ℝ) = ((1000000 / 1239573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273875161 / 1000000000) ≤ -Real.log (760427 / 1000000) ∧
    -Real.log (760427 / 1000000) ≤ (136937581 / 500000000) := by
  have h := checkLog_sound (w := (239573 / 1760427)) (n := 12)
    (lo := (273875161 / 1000000000)) (hi := (136937581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760427) = 1/(760427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-136937581 / 500000000) (-273875161 / 1000000000) (Real.log (760427 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215033957 / 1000000000) ≤ -Real.log (31250 / 38747) ∧
    -Real.log (31250 / 38747) ≤ (107516979 / 500000000) := by
  have h := checkLog_sound (w := (7497 / 69997)) (n := 12)
    (lo := (215033957 / 1000000000)) (hi := (107516979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38747 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38747 / 31250) = 1/(31250 / 38747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215033957 / 1000000000) (107516979 / 500000000) (Real.log (38747 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (38747 / 31250) = -Real.log (31250 / 38747) := by
    rw [show ((38747 / 31250) : ℝ) = ((31250 / 38747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (274310537 / 1000000000) ≤ -Real.log (23753 / 31250) ∧
    -Real.log (23753 / 31250) ≤ (137155269 / 500000000) := by
  have h := checkLog_sound (w := (7497 / 55003)) (n := 12)
    (lo := (274310537 / 1000000000)) (hi := (137155269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23753) = 1/(23753 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-137155269 / 500000000) (-274310537 / 1000000000) (Real.log (23753 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (682688597 / 1000000000) ≤ -Real.log (100000000000 / 197919183463) ∧
    -Real.log (100000000000 / 197919183463) ≤ (341344299 / 500000000) := by
  have h := checkLog_sound (w := (97919183463 / 297919183463)) (n := 12)
    (lo := (682688597 / 1000000000)) (hi := (341344299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197919183463 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197919183463 / 100000000000) = 1/(100000000000 / 197919183463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (682688597 / 1000000000) (341344299 / 500000000) (Real.log (197919183463 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (197919183463 / 100000000000) = -Real.log (100000000000 / 197919183463) := by
    rw [show ((197919183463 / 100000000000) : ℝ) = ((100000000000 / 197919183463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34182421 / 50000000) ≤ -Real.log (500000000000 / 990546210659) ∧
    -Real.log (500000000000 / 990546210659) ≤ (683648421 / 1000000000) := by
  have h := checkLog_sound (w := (490546210659 / 1490546210659)) (n := 12)
    (lo := (34182421 / 50000000)) (hi := (683648421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990546210659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990546210659 / 500000000000) = 1/(500000000000 / 990546210659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34182421 / 50000000) (683648421 / 1000000000) (Real.log (990546210659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (990546210659 / 500000000000) = -Real.log (500000000000 / 990546210659) := by
    rw [show ((990546210659 / 500000000000) : ℝ) = ((500000000000 / 990546210659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (244321063 / 500000000) ≤ -Real.log (500000000000 / 815050622873) ∧
    -Real.log (500000000000 / 815050622873) ≤ (488642127 / 1000000000) := by
  have h := checkLog_sound (w := (315050622873 / 1315050622873)) (n := 12)
    (lo := (244321063 / 500000000)) (hi := (488642127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815050622873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815050622873 / 500000000000) = 1/(500000000000 / 815050622873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (244321063 / 500000000) (488642127 / 1000000000) (Real.log (815050622873 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (815050622873 / 500000000000) = -Real.log (500000000000 / 815050622873) := by
    rw [show ((815050622873 / 500000000000) : ℝ) = ((500000000000 / 815050622873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (97868899 / 200000000) ≤ -Real.log (50000000000 / 81562328969) ∧
    -Real.log (50000000000 / 81562328969) ≤ (30584031 / 62500000) := by
  have h := checkLog_sound (w := (31562328969 / 131562328969)) (n := 12)
    (lo := (97868899 / 200000000)) (hi := (30584031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81562328969 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81562328969 / 50000000000) = 1/(50000000000 / 81562328969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (97868899 / 200000000) (30584031 / 62500000) (Real.log (81562328969 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (81562328969 / 50000000000) = -Real.log (50000000000 / 81562328969) := by
    rw [show ((81562328969 / 50000000000) : ℝ) = ((50000000000 / 81562328969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0370
