import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0005
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

theorem reflection_log_1_neg : (10753943 / 25000000) ≤ -Real.log (80 / 123) ∧
    -Real.log (80 / 123) ≤ (430157721 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 203)) (n := 12)
    (lo := (10753943 / 25000000)) (hi := (430157721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 80) = 1/(80 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10753943 / 25000000) (430157721 / 1000000000) (Real.log (123 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (123 / 80) = -Real.log (80 / 123) := by
    rw [show ((123 / 80) : ℝ) = ((80 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (771108721 / 1000000000) ≤ -Real.log (37 / 80) ∧
    -Real.log (37 / 80) ≤ (771108723 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 37) = 1/(37 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-771108723 / 1000000000) (-771108721 / 1000000000) (Real.log (37 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42199441 / 100000000) ≤ -Real.log (40 / 61) ∧
    -Real.log (40 / 61) ≤ (421994411 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 101)) (n := 12)
    (lo := (42199441 / 100000000)) (hi := (421994411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 40) = 1/(40 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42199441 / 100000000) (421994411 / 1000000000) (Real.log (61 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (61 / 40) = -Real.log (40 / 61) := by
    rw [show ((61 / 40) : ℝ) = ((40 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (372220237 / 500000000) ≤ -Real.log (19 / 40) ∧
    -Real.log (19 / 40) ≤ (186110119 / 250000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 19) = 1/(19 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-186110119 / 250000000) (-372220237 / 500000000) (Real.log (19 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (72320661 / 1000000000) ≤ -Real.log (40 / 43) ∧
    -Real.log (40 / 43) ≤ (36160331 / 500000000) := by
  have h := checkLog_sound (w := (3 / 83)) (n := 12)
    (lo := (72320661 / 1000000000)) (hi := (36160331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 40) = 1/(40 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (72320661 / 1000000000) (36160331 / 500000000) (Real.log (43 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (43 / 40) = -Real.log (40 / 43) := by
    rw [show ((43 / 40) : ℝ) = ((40 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77961541 / 1000000000) ≤ -Real.log (37 / 40) ∧
    -Real.log (37 / 40) ≤ (38980771 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 37) = 1/(37 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38980771 / 500000000) (-77961541 / 1000000000) (Real.log (37 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12197541 / 250000000) ≤ -Real.log (20 / 21) ∧
    -Real.log (20 / 21) ≤ (9758033 / 200000000) := by
  have h := checkLog_sound (w := (1 / 41)) (n := 12)
    (lo := (12197541 / 250000000)) (hi := (9758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 20) = 1/(20 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12197541 / 250000000) (9758033 / 200000000) (Real.log (21 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (21 / 20) = -Real.log (20 / 21) := by
    rw [show ((21 / 20) : ℝ) = ((20 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25646647 / 500000000) ≤ -Real.log (19 / 20) ∧
    -Real.log (19 / 20) ≤ (10258659 / 200000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 19) = 1/(19 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10258659 / 200000000) (-25646647 / 500000000) (Real.log (19 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (144229453 / 250000000) ≤ -Real.log (500000 / 890271) ∧
    -Real.log (500000 / 890271) ≤ (576917813 / 1000000000) := by
  have h := checkLog_sound (w := (390271 / 1390271)) (n := 12)
    (lo := (144229453 / 250000000)) (hi := (576917813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890271 / 500000) = 1/(500000 / 890271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (144229453 / 250000000) (576917813 / 1000000000) (Real.log (890271 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (890271 / 500000) = -Real.log (500000 / 890271) := by
    rw [show ((890271 / 500000) : ℝ) = ((500000 / 890271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1516594407 / 1000000000) ≤ -Real.log (109729 / 500000) ∧
    -Real.log (109729 / 500000) ≤ (151659441 / 100000000) := by
  have h := checkLog_sound (w := (15271 / 234729)) (n := 12)
    (lo := (130300047 / 1000000000)) (hi := (8143753 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 109729) = 1/(109729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151659441 / 100000000) (-1516594407 / 1000000000) (Real.log (109729 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (577337259 / 1000000000) ≤ -Real.log (1000000 / 1781289) ∧
    -Real.log (1000000 / 1781289) ≤ (28866863 / 50000000) := by
  have h := checkLog_sound (w := (781289 / 2781289)) (n := 12)
    (lo := (577337259 / 1000000000)) (hi := (28866863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1781289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1781289 / 1000000) = 1/(1000000 / 1781289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (577337259 / 1000000000) (28866863 / 50000000) (Real.log (1781289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1781289 / 1000000) = -Real.log (1000000 / 1781289) := by
    rw [show ((1781289 / 1000000) : ℝ) = ((1000000 / 1781289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (760002027 / 500000000) ≤ -Real.log (218711 / 1000000) ∧
    -Real.log (218711 / 1000000) ≤ (1520004057 / 1000000000) := by
  have h := checkLog_sound (w := (31289 / 468711)) (n := 12)
    (lo := (66854847 / 500000000)) (hi := (26741939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218711) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 218711) = 1/(218711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1520004057 / 1000000000) (-760002027 / 500000000) (Real.log (218711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (515409501 / 1000000000) ≤ -Real.log (250000 / 418581) ∧
    -Real.log (250000 / 418581) ≤ (257704751 / 500000000) := by
  have h := checkLog_sound (w := (168581 / 668581)) (n := 12)
    (lo := (515409501 / 1000000000)) (hi := (257704751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418581 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418581 / 250000) = 1/(250000 / 418581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (515409501 / 1000000000) (257704751 / 500000000) (Real.log (418581 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (418581 / 250000) = -Real.log (250000 / 418581) := by
    rw [show ((418581 / 250000) : ℝ) = ((250000 / 418581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35057883 / 31250000) ≤ -Real.log (81419 / 250000) ∧
    -Real.log (81419 / 250000) ≤ (560926129 / 500000000) := by
  have h := checkLog_sound (w := (43581 / 206419)) (n := 12)
    (lo := (107176269 / 250000000)) (hi := (428705077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 81419) = 1/(81419 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-560926129 / 500000000) (-35057883 / 31250000) (Real.log (81419 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (26000159 / 50000000) ≤ -Real.log (1000000 / 1682033) ∧
    -Real.log (1000000 / 1682033) ≤ (520003181 / 1000000000) := by
  have h := checkLog_sound (w := (682033 / 2682033)) (n := 12)
    (lo := (26000159 / 50000000)) (hi := (520003181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1682033 / 1000000) = 1/(1000000 / 1682033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (26000159 / 50000000) (520003181 / 1000000000) (Real.log (1682033 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1682033 / 1000000) = -Real.log (1000000 / 1682033) := by
    rw [show ((1682033 / 1000000) : ℝ) = ((1000000 / 1682033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (572903837 / 500000000) ≤ -Real.log (317967 / 1000000) ∧
    -Real.log (317967 / 1000000) ≤ (286451919 / 250000000) := by
  have h := checkLog_sound (w := (182033 / 817967)) (n := 12)
    (lo := (226330247 / 500000000)) (hi := (90532099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 317967) = 1/(317967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-286451919 / 250000000) (-572903837 / 500000000) (Real.log (317967 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2093512219 / 1000000000) ≤ -Real.log (500000000000 / 4056680549353) ∧
    -Real.log (500000000000 / 4056680549353) ≤ (2093512223 / 1000000000) := by
  have h := checkLog_sound (w := (56680549353 / 8056680549353)) (n := 12)
    (lo := (14070679 / 1000000000)) (hi := (351767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4056680549353 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4056680549353 / 4000000000000) = 1/(500000000000 / 4056680549353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2093512219 / 1000000000) (2093512223 / 1000000000) (Real.log (4056680549353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4056680549353 / 500000000000) = -Real.log (500000000000 / 4056680549353) := by
    rw [show ((4056680549353 / 500000000000) : ℝ) = ((500000000000 / 4056680549353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2097341313 / 1000000000) ≤ -Real.log (50000000000 / 407224373717) ∧
    -Real.log (50000000000 / 407224373717) ≤ (2097341317 / 1000000000) := by
  have h := checkLog_sound (w := (7224373717 / 807224373717)) (n := 12)
    (lo := (17899773 / 1000000000)) (hi := (8949887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407224373717 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(407224373717 / 400000000000) = 1/(50000000000 / 407224373717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2097341313 / 1000000000) (2097341317 / 1000000000) (Real.log (407224373717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (407224373717 / 50000000000) = -Real.log (50000000000 / 407224373717) := by
    rw [show ((407224373717 / 50000000000) : ℝ) = ((50000000000 / 407224373717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1637261757 / 1000000000) ≤ -Real.log (500000000000 / 2570536361291) ∧
    -Real.log (500000000000 / 2570536361291) ≤ (5116443 / 3125000) := by
  have h := checkLog_sound (w := (570536361291 / 4570536361291)) (n := 12)
    (lo := (250967397 / 1000000000)) (hi := (125483699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2570536361291 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2570536361291 / 2000000000000) = 1/(500000000000 / 2570536361291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1637261757 / 1000000000) (5116443 / 3125000) (Real.log (2570536361291 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2570536361291 / 500000000000) = -Real.log (500000000000 / 2570536361291) := by
    rw [show ((2570536361291 / 500000000000) : ℝ) = ((500000000000 / 2570536361291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (832905427 / 500000000) ≤ -Real.log (500000000000 / 2644980453947) ∧
    -Real.log (500000000000 / 2644980453947) ≤ (1665810857 / 1000000000) := by
  have h := checkLog_sound (w := (644980453947 / 4644980453947)) (n := 12)
    (lo := (139758247 / 500000000)) (hi := (55903299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2644980453947 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2644980453947 / 2000000000000) = 1/(500000000000 / 2644980453947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (832905427 / 500000000) (1665810857 / 1000000000) (Real.log (2644980453947 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2644980453947 / 500000000000) = -Real.log (500000000000 / 2644980453947) := by
    rw [show ((2644980453947 / 500000000000) : ℝ) = ((500000000000 / 2644980453947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0005
