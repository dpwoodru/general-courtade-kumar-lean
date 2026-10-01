import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0369
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

theorem reflection_log_1_neg : (207633261 / 1000000000) ≤ -Real.log (10240 / 12603) ∧
    -Real.log (10240 / 12603) ≤ (103816631 / 500000000) := by
  have h := checkLog_sound (w := (2363 / 22843)) (n := 12)
    (lo := (207633261 / 1000000000)) (hi := (103816631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12603 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12603 / 10240) = 1/(10240 / 12603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (207633261 / 1000000000) (103816631 / 500000000) (Real.log (12603 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12603 / 10240) = -Real.log (10240 / 12603) := by
    rw [show ((12603 / 10240) : ℝ) = ((10240 / 12603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (131177249 / 500000000) ≤ -Real.log (7877 / 10240) ∧
    -Real.log (7877 / 10240) ≤ (262354499 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 18117)) (n := 12)
    (lo := (131177249 / 500000000)) (hi := (262354499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7877) = 1/(7877 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-262354499 / 1000000000) (-131177249 / 500000000) (Real.log (7877 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (103697597 / 500000000) ≤ -Real.log (256 / 315) ∧
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


theorem reflection_log_3 : Bounds (103697597 / 500000000) (41479039 / 200000000) (Real.log (315 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (315 / 256) = -Real.log (256 / 315) := by
    rw [show ((315 / 256) : ℝ) = ((256 / 315) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52394743 / 200000000) ≤ -Real.log (197 / 256) ∧
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


theorem reflection_log_4 : Bounds (-65493429 / 250000000) (-52394743 / 200000000) (Real.log (197 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189739671 / 500000000) ≤ -Real.log (5120 / 7483) ∧
    -Real.log (5120 / 7483) ≤ (379479343 / 1000000000) := by
  have h := checkLog_sound (w := (2363 / 12603)) (n := 12)
    (lo := (189739671 / 500000000)) (hi := (379479343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7483 / 5120) = 1/(5120 / 7483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189739671 / 500000000) (379479343 / 1000000000) (Real.log (7483 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7483 / 5120) = -Real.log (5120 / 7483) := by
    rw [show ((7483 / 5120) : ℝ) = ((5120 / 7483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (619011307 / 1000000000) ≤ -Real.log (2757 / 5120) ∧
    -Real.log (2757 / 5120) ≤ (154752827 / 250000000) := by
  have h := checkLog_sound (w := (2363 / 7877)) (n := 12)
    (lo := (619011307 / 1000000000)) (hi := (154752827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2757) = 1/(2757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-154752827 / 250000000) (-619011307 / 1000000000) (Real.log (2757 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23692397 / 62500000) ≤ -Real.log (128 / 187) ∧
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


theorem reflection_log_7 : Bounds (23692397 / 62500000) (379078353 / 1000000000) (Real.log (187 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (187 / 128) = -Real.log (128 / 187) := by
    rw [show ((187 / 128) : ℝ) = ((128 / 187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617923759 / 1000000000) ≤ -Real.log (69 / 128) ∧
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


theorem reflection_log_8 : Bounds (-7724047 / 12500000) (-617923759 / 1000000000) (Real.log (69 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28450503 / 100000000) ≤ -Real.log (62500 / 83069) ∧
    -Real.log (62500 / 83069) ≤ (284505031 / 1000000000) := by
  have h := checkLog_sound (w := (20569 / 145569)) (n := 12)
    (lo := (28450503 / 100000000)) (hi := (284505031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83069 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83069 / 62500) = 1/(62500 / 83069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28450503 / 100000000) (284505031 / 1000000000) (Real.log (83069 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (83069 / 62500) = -Real.log (62500 / 83069) := by
    rw [show ((83069 / 62500) : ℝ) = ((62500 / 83069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199570573 / 500000000) ≤ -Real.log (41931 / 62500) ∧
    -Real.log (41931 / 62500) ≤ (399141147 / 1000000000) := by
  have h := checkLog_sound (w := (20569 / 104431)) (n := 12)
    (lo := (199570573 / 500000000)) (hi := (399141147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41931) = 1/(41931 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-399141147 / 1000000000) (-199570573 / 500000000) (Real.log (41931 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35603469 / 125000000) ≤ -Real.log (1000000 / 1329533) ∧
    -Real.log (1000000 / 1329533) ≤ (284827753 / 1000000000) := by
  have h := checkLog_sound (w := (329533 / 2329533)) (n := 12)
    (lo := (35603469 / 125000000)) (hi := (284827753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329533 / 1000000) = 1/(1000000 / 1329533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35603469 / 125000000) (284827753 / 1000000000) (Real.log (1329533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1329533 / 1000000) = -Real.log (1000000 / 1329533) := by
    rw [show ((1329533 / 1000000) : ℝ) = ((1000000 / 1329533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (199890397 / 500000000) ≤ -Real.log (670467 / 1000000) ∧
    -Real.log (670467 / 1000000) ≤ (79956159 / 200000000) := by
  have h := checkLog_sound (w := (329533 / 1670467)) (n := 12)
    (lo := (199890397 / 500000000)) (hi := (79956159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670467) = 1/(670467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-79956159 / 200000000) (-199890397 / 500000000) (Real.log (670467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4300663 / 20000000) ≤ -Real.log (1000000 / 1239903) ∧
    -Real.log (1000000 / 1239903) ≤ (215033151 / 1000000000) := by
  have h := checkLog_sound (w := (239903 / 2239903)) (n := 12)
    (lo := (4300663 / 20000000)) (hi := (215033151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239903 / 1000000) = 1/(1000000 / 1239903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4300663 / 20000000) (215033151 / 1000000000) (Real.log (1239903 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1239903 / 1000000) = -Real.log (1000000 / 1239903) := by
    rw [show ((1239903 / 1000000) : ℝ) = ((1000000 / 1239903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (137154611 / 500000000) ≤ -Real.log (760097 / 1000000) ∧
    -Real.log (760097 / 1000000) ≤ (274309223 / 1000000000) := by
  have h := checkLog_sound (w := (239903 / 1760097)) (n := 12)
    (lo := (137154611 / 500000000)) (hi := (274309223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760097) = 1/(760097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-274309223 / 1000000000) (-137154611 / 500000000) (Real.log (760097 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (215300877 / 1000000000) ≤ -Real.log (200000 / 248047) ∧
    -Real.log (200000 / 248047) ≤ (107650439 / 500000000) := by
  have h := checkLog_sound (w := (48047 / 448047)) (n := 12)
    (lo := (215300877 / 1000000000)) (hi := (107650439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248047 / 200000) = 1/(200000 / 248047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215300877 / 1000000000) (107650439 / 500000000) (Real.log (248047 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (248047 / 200000) = -Real.log (200000 / 248047) := by
    rw [show ((248047 / 200000) : ℝ) = ((200000 / 248047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (34343263 / 125000000) ≤ -Real.log (151953 / 200000) ∧
    -Real.log (151953 / 200000) ≤ (54949221 / 200000000) := by
  have h := checkLog_sound (w := (48047 / 351953)) (n := 12)
    (lo := (34343263 / 125000000)) (hi := (54949221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151953) = 1/(151953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-54949221 / 200000000) (-34343263 / 125000000) (Real.log (151953 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (683646177 / 1000000000) ≤ -Real.log (250000000000 / 495271994467) ∧
    -Real.log (250000000000 / 495271994467) ≤ (341823089 / 500000000) := by
  have h := checkLog_sound (w := (245271994467 / 745271994467)) (n := 12)
    (lo := (683646177 / 1000000000)) (hi := (341823089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495271994467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495271994467 / 250000000000) = 1/(250000000000 / 495271994467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (683646177 / 1000000000) (341823089 / 500000000) (Real.log (495271994467 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (495271994467 / 250000000000) = -Real.log (250000000000 / 495271994467) := by
    rw [show ((495271994467 / 250000000000) : ℝ) = ((250000000000 / 495271994467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (684608547 / 1000000000) ≤ -Real.log (500000000000 / 991497717263) ∧
    -Real.log (500000000000 / 991497717263) ≤ (171152137 / 250000000) := by
  have h := checkLog_sound (w := (491497717263 / 1491497717263)) (n := 12)
    (lo := (684608547 / 1000000000)) (hi := (171152137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991497717263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991497717263 / 500000000000) = 1/(500000000000 / 991497717263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (684608547 / 1000000000) (171152137 / 250000000) (Real.log (991497717263 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (991497717263 / 500000000000) = -Real.log (500000000000 / 991497717263) := by
    rw [show ((991497717263 / 500000000000) : ℝ) = ((500000000000 / 991497717263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (489342373 / 1000000000) ≤ -Real.log (500000000000 / 815621558827) ∧
    -Real.log (500000000000 / 815621558827) ≤ (244671187 / 500000000) := by
  have h := checkLog_sound (w := (315621558827 / 1315621558827)) (n := 12)
    (lo := (489342373 / 1000000000)) (hi := (244671187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815621558827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815621558827 / 500000000000) = 1/(500000000000 / 815621558827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (489342373 / 1000000000) (244671187 / 500000000) (Real.log (815621558827 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (815621558827 / 500000000000) = -Real.log (500000000000 / 815621558827) := by
    rw [show ((815621558827 / 500000000000) : ℝ) = ((500000000000 / 815621558827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (490046981 / 1000000000) ≤ -Real.log (500000000000 / 816196455483) ∧
    -Real.log (500000000000 / 816196455483) ≤ (245023491 / 500000000) := by
  have h := checkLog_sound (w := (316196455483 / 1316196455483)) (n := 12)
    (lo := (490046981 / 1000000000)) (hi := (245023491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816196455483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816196455483 / 500000000000) = 1/(500000000000 / 816196455483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (490046981 / 1000000000) (245023491 / 500000000) (Real.log (816196455483 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (816196455483 / 500000000000) = -Real.log (500000000000 / 816196455483) := by
    rw [show ((816196455483 / 500000000000) : ℝ) = ((500000000000 / 816196455483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0369
