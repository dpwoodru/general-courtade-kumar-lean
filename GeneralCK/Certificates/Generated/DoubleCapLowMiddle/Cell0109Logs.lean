import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0109
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

theorem reflection_log_1_neg : (669700617 / 1000000000) ≤ -Real.log (51200 / 100027) ∧
    -Real.log (51200 / 100027) ≤ (334850309 / 500000000) := by
  have h := checkLog_sound (w := (48827 / 151227)) (n := 12)
    (lo := (669700617 / 1000000000)) (hi := (334850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 51200) = 1/(51200 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (669700617 / 1000000000) (334850309 / 500000000) (Real.log (100027 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100027 / 51200) = -Real.log (51200 / 100027) := by
    rw [show ((100027 / 51200) : ℝ) = ((51200 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (383948069 / 125000000) ≤ -Real.log (2373 / 51200) ∧
    -Real.log (2373 / 51200) ≤ (3071584557 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2373) = 1/(2373 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3071584557 / 1000000000) (-383948069 / 125000000) (Real.log (2373 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13390213 / 20000000) ≤ -Real.log (6400 / 12501) ∧
    -Real.log (6400 / 12501) ≤ (669510651 / 1000000000) := by
  have h := checkLog_sound (w := (6101 / 18901)) (n := 12)
    (lo := (13390213 / 20000000)) (hi := (669510651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 6400) = 1/(6400 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13390213 / 20000000) (669510651 / 1000000000) (Real.log (12501 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12501 / 6400) = -Real.log (6400 / 12501) := by
    rw [show ((12501 / 6400) : ℝ) = ((6400 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3063609693 / 1000000000) ≤ -Real.log (299 / 6400) ∧
    -Real.log (299 / 6400) ≤ (1531804849 / 500000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 299) = 1/(299 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1531804849 / 500000000) (-3063609693 / 1000000000) (Real.log (299 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (645691087 / 1000000000) ≤ -Real.log (25600 / 48827) ∧
    -Real.log (25600 / 48827) ≤ (40355693 / 62500000) := by
  have h := checkLog_sound (w := (23227 / 74427)) (n := 12)
    (lo := (645691087 / 1000000000)) (hi := (40355693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48827 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48827 / 25600) = 1/(25600 / 48827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (645691087 / 1000000000) (40355693 / 62500000) (Real.log (48827 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48827 / 25600) = -Real.log (25600 / 48827) := by
    rw [show ((48827 / 25600) : ℝ) = ((25600 / 48827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (594609343 / 250000000) ≤ -Real.log (2373 / 25600) ∧
    -Real.log (2373 / 25600) ≤ (9290771 / 3906250) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2373) = 1/(2373 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-9290771 / 3906250) (-594609343 / 250000000) (Real.log (2373 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322650941 / 500000000) ≤ -Real.log (3200 / 6101) ∧
    -Real.log (3200 / 6101) ≤ (645301883 / 1000000000) := by
  have h := checkLog_sound (w := (2901 / 9301)) (n := 12)
    (lo := (322650941 / 500000000)) (hi := (645301883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6101 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6101 / 3200) = 1/(3200 / 6101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322650941 / 500000000) (645301883 / 1000000000) (Real.log (6101 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6101 / 3200) = -Real.log (3200 / 6101) := by
    rw [show ((6101 / 3200) : ℝ) = ((3200 / 6101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2370462513 / 1000000000) ≤ -Real.log (299 / 3200) ∧
    -Real.log (299 / 3200) ≤ (2370462517 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 299) = 1/(299 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2370462517 / 1000000000) (-2370462513 / 1000000000) (Real.log (299 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (336950069 / 500000000) ≤ -Real.log (500000 / 980937) ∧
    -Real.log (500000 / 980937) ≤ (673900139 / 1000000000) := by
  have h := checkLog_sound (w := (480937 / 1480937)) (n := 12)
    (lo := (336950069 / 500000000)) (hi := (673900139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980937 / 500000) = 1/(500000 / 980937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (336950069 / 500000000) (673900139 / 1000000000) (Real.log (980937 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980937 / 500000) = -Real.log (500000 / 980937) := by
    rw [show ((980937 / 500000) : ℝ) = ((500000 / 980937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (816714703 / 250000000) ≤ -Real.log (19063 / 500000) ∧
    -Real.log (19063 / 500000) ≤ (3266858817 / 1000000000) := by
  have h := checkLog_sound (w := (12187 / 50313)) (n := 12)
    (lo := (123567523 / 250000000)) (hi := (494270093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19063) = 1/(19063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3266858817 / 1000000000) (-816714703 / 250000000) (Real.log (19063 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674045397 / 1000000000) ≤ -Real.log (1000000 / 1962159) ∧
    -Real.log (1000000 / 1962159) ≤ (337022699 / 500000000) := by
  have h := checkLog_sound (w := (962159 / 2962159)) (n := 12)
    (lo := (674045397 / 1000000000)) (hi := (337022699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962159 / 1000000) = 1/(1000000 / 1962159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674045397 / 1000000000) (337022699 / 500000000) (Real.log (1962159 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1962159 / 1000000) = -Real.log (1000000 / 1962159) := by
    rw [show ((1962159 / 1000000) : ℝ) = ((1000000 / 1962159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (654872421 / 200000000) ≤ -Real.log (37841 / 1000000) ∧
    -Real.log (37841 / 1000000) ≤ (327436211 / 100000000) := by
  have h := checkLog_sound (w := (24659 / 100341)) (n := 12)
    (lo := (100354677 / 200000000)) (hi := (250886693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37841) = 1/(37841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-327436211 / 100000000) (-654872421 / 200000000) (Real.log (37841 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673690113 / 1000000000) ≤ -Real.log (500000 / 980731) ∧
    -Real.log (500000 / 980731) ≤ (336845057 / 500000000) := by
  have h := checkLog_sound (w := (480731 / 1480731)) (n := 12)
    (lo := (673690113 / 1000000000)) (hi := (336845057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980731 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980731 / 500000) = 1/(500000 / 980731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673690113 / 1000000000) (336845057 / 500000000) (Real.log (980731 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980731 / 500000) = -Real.log (500000 / 980731) := by
    rw [show ((980731 / 500000) : ℝ) = ((500000 / 980731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3256110509 / 1000000000) ≤ -Real.log (19269 / 500000) ∧
    -Real.log (19269 / 500000) ≤ (1628055257 / 500000000) := by
  have h := checkLog_sound (w := (11981 / 50519)) (n := 12)
    (lo := (483521789 / 1000000000)) (hi := (48352179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19269) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19269) = 1/(19269 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1628055257 / 500000000) (-3256110509 / 1000000000) (Real.log (19269 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (16845987 / 25000000) ≤ -Real.log (200000 / 392351) ∧
    -Real.log (200000 / 392351) ≤ (673839481 / 1000000000) := by
  have h := checkLog_sound (w := (192351 / 592351)) (n := 12)
    (lo := (16845987 / 25000000)) (hi := (673839481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392351 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392351 / 200000) = 1/(200000 / 392351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (16845987 / 25000000) (673839481 / 1000000000) (Real.log (392351 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (392351 / 200000) = -Real.log (200000 / 392351) := by
    rw [show ((392351 / 200000) : ℝ) = ((200000 / 392351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3263742443 / 1000000000) ≤ -Real.log (7649 / 200000) ∧
    -Real.log (7649 / 200000) ≤ (203983903 / 62500000) := by
  have h := checkLog_sound (w := (4851 / 20149)) (n := 12)
    (lo := (491153723 / 1000000000)) (hi := (122788431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7649) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 7649) = 1/(7649 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-203983903 / 62500000) (-3263742443 / 1000000000) (Real.log (7649 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (78815179 / 20000000) ≤ -Real.log (250000000000 / 12864410113833) ∧
    -Real.log (250000000000 / 12864410113833) ≤ (985189739 / 250000000) := by
  have h := checkLog_sound (w := (4864410113833 / 20864410113833)) (n := 12)
    (lo := (9500461 / 20000000)) (hi := (475023051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12864410113833 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12864410113833 / 8000000000000) = 1/(250000000000 / 12864410113833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78815179 / 20000000) (985189739 / 250000000) (Real.log (12864410113833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12864410113833 / 250000000000) = -Real.log (250000000000 / 12864410113833) := by
    rw [show ((12864410113833 / 250000000000) : ℝ) = ((250000000000 / 12864410113833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1974203751 / 500000000) ≤ -Real.log (500000000000 / 25926362939669) ∧
    -Real.log (500000000000 / 25926362939669) ≤ (987101877 / 250000000) := by
  have h := checkLog_sound (w := (9926362939669 / 41926362939669)) (n := 12)
    (lo := (241335801 / 500000000)) (hi := (482671603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25926362939669 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25926362939669 / 16000000000000) = 1/(500000000000 / 25926362939669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1974203751 / 500000000) (987101877 / 250000000) (Real.log (25926362939669 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25926362939669 / 500000000000) = -Real.log (500000000000 / 25926362939669) := by
    rw [show ((25926362939669 / 500000000000) : ℝ) = ((500000000000 / 25926362939669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1964900311 / 500000000) ≤ -Real.log (50000000000 / 2544841455187) ∧
    -Real.log (50000000000 / 2544841455187) ≤ (982450157 / 250000000) := by
  have h := checkLog_sound (w := (944841455187 / 4144841455187)) (n := 12)
    (lo := (232032361 / 500000000)) (hi := (464064723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2544841455187 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2544841455187 / 1600000000000) = 1/(50000000000 / 2544841455187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1964900311 / 500000000) (982450157 / 250000000) (Real.log (2544841455187 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2544841455187 / 50000000000) = -Real.log (50000000000 / 2544841455187) := by
    rw [show ((2544841455187 / 50000000000) : ℝ) = ((50000000000 / 2544841455187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (984395481 / 250000000) ≤ -Real.log (500000000000 / 25647208785463) ∧
    -Real.log (500000000000 / 25647208785463) ≤ (393758193 / 100000000) := by
  have h := checkLog_sound (w := (9647208785463 / 41647208785463)) (n := 12)
    (lo := (58980753 / 125000000)) (hi := (18873841 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25647208785463 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25647208785463 / 16000000000000) = 1/(500000000000 / 25647208785463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (984395481 / 250000000) (393758193 / 100000000) (Real.log (25647208785463 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25647208785463 / 500000000000) = -Real.log (500000000000 / 25647208785463) := by
    rw [show ((25647208785463 / 500000000000) : ℝ) = ((500000000000 / 25647208785463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0109
