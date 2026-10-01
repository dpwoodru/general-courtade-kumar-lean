import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0150
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

theorem reflection_log_1_neg : (290510101 / 1000000000) ≤ -Real.log (2560 / 3423) ∧
    -Real.log (2560 / 3423) ≤ (145255051 / 500000000) := by
  have h := checkLog_sound (w := (863 / 5983)) (n := 12)
    (lo := (290510101 / 1000000000)) (hi := (145255051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3423 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3423 / 2560) = 1/(2560 / 3423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (290510101 / 1000000000) (145255051 / 500000000) (Real.log (3423 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3423 / 2560) = -Real.log (2560 / 3423) := by
    rw [show ((3423 / 2560) : ℝ) = ((2560 / 3423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (51393159 / 125000000) ≤ -Real.log (1697 / 2560) ∧
    -Real.log (1697 / 2560) ≤ (411145273 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 4257)) (n := 12)
    (lo := (51393159 / 125000000)) (hi := (411145273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1697) = 1/(1697 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-411145273 / 1000000000) (-51393159 / 125000000) (Real.log (1697 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72408323 / 250000000) ≤ -Real.log (128 / 171) ∧
    -Real.log (128 / 171) ≤ (289633293 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 299)) (n := 12)
    (lo := (72408323 / 250000000)) (hi := (289633293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 128) = 1/(128 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72408323 / 250000000) (289633293 / 1000000000) (Real.log (171 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (171 / 128) = -Real.log (128 / 171) := by
    rw [show ((171 / 128) : ℝ) = ((128 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (409379007 / 1000000000) ≤ -Real.log (85 / 128) ∧
    -Real.log (85 / 128) ≤ (6396547 / 15625000) := by
  have h := checkLog_sound (w := (43 / 213)) (n := 12)
    (lo := (409379007 / 1000000000)) (hi := (6396547 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 85) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 85) = 1/(85 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6396547 / 15625000) (-409379007 / 1000000000) (Real.log (85 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (257673319 / 500000000) ≤ -Real.log (1280 / 2143) ∧
    -Real.log (1280 / 2143) ≤ (515346639 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 3423)) (n := 12)
    (lo := (257673319 / 500000000)) (hi := (515346639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2143 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2143 / 1280) = 1/(1280 / 2143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (257673319 / 500000000) (515346639 / 1000000000) (Real.log (2143 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2143 / 1280) = -Real.log (1280 / 2143) := by
    rw [show ((2143 / 1280) : ℝ) = ((1280 / 2143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (560764567 / 500000000) ≤ -Real.log (417 / 1280) ∧
    -Real.log (417 / 1280) ≤ (70095571 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 417) = 1/(417 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70095571 / 62500000) (-560764567 / 500000000) (Real.log (417 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (513945751 / 1000000000) ≤ -Real.log (64 / 107) ∧
    -Real.log (64 / 107) ≤ (64243219 / 125000000) := by
  have h := checkLog_sound (w := (43 / 171)) (n := 12)
    (lo := (513945751 / 1000000000)) (hi := (64243219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107 / 64) = 1/(64 / 107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (513945751 / 1000000000) (64243219 / 125000000) (Real.log (107 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (107 / 64) = -Real.log (64 / 107) := by
    rw [show ((107 / 64) : ℝ) = ((64 / 107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222872129 / 200000000) ≤ -Real.log (21 / 64) ∧
    -Real.log (21 / 64) ≤ (1114360647 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 21) = 1/(21 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1114360647 / 1000000000) (-222872129 / 200000000) (Real.log (21 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (198138513 / 500000000) ≤ -Real.log (1000000 / 1486281) ∧
    -Real.log (1000000 / 1486281) ≤ (396277027 / 1000000000) := by
  have h := checkLog_sound (w := (486281 / 2486281)) (n := 12)
    (lo := (198138513 / 500000000)) (hi := (396277027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1486281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1486281 / 1000000) = 1/(1000000 / 1486281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (198138513 / 500000000) (396277027 / 1000000000) (Real.log (1486281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1486281 / 1000000) = -Real.log (1000000 / 1486281) := by
    rw [show ((1486281 / 1000000) : ℝ) = ((1000000 / 1486281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133215771 / 200000000) ≤ -Real.log (513719 / 1000000) ∧
    -Real.log (513719 / 1000000) ≤ (83259857 / 125000000) := by
  have h := checkLog_sound (w := (486281 / 1513719)) (n := 12)
    (lo := (133215771 / 200000000)) (hi := (83259857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 513719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 513719) = 1/(513719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83259857 / 125000000) (-133215771 / 200000000) (Real.log (513719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (198742677 / 500000000) ≤ -Real.log (500000 / 744039) ∧
    -Real.log (500000 / 744039) ≤ (79497071 / 200000000) := by
  have h := checkLog_sound (w := (244039 / 1244039)) (n := 12)
    (lo := (198742677 / 500000000)) (hi := (79497071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744039 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744039 / 500000) = 1/(500000 / 744039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (198742677 / 500000000) (79497071 / 200000000) (Real.log (744039 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (744039 / 500000) = -Real.log (500000 / 744039) := by
    rw [show ((744039 / 500000) : ℝ) = ((500000 / 744039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (669583009 / 1000000000) ≤ -Real.log (255961 / 500000) ∧
    -Real.log (255961 / 500000) ≤ (66958301 / 100000000) := by
  have h := checkLog_sound (w := (244039 / 755961)) (n := 12)
    (lo := (669583009 / 1000000000)) (hi := (66958301 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 255961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 255961) = 1/(255961 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-66958301 / 100000000) (-669583009 / 1000000000) (Real.log (255961 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (156620813 / 500000000) ≤ -Real.log (250000 / 341963) ∧
    -Real.log (250000 / 341963) ≤ (313241627 / 1000000000) := by
  have h := checkLog_sound (w := (91963 / 591963)) (n := 12)
    (lo := (156620813 / 500000000)) (hi := (313241627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341963 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341963 / 250000) = 1/(250000 / 341963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (156620813 / 500000000) (313241627 / 1000000000) (Real.log (341963 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (341963 / 250000) = -Real.log (250000 / 341963) := by
    rw [show ((341963 / 250000) : ℝ) = ((250000 / 341963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91726347 / 200000000) ≤ -Real.log (158037 / 250000) ∧
    -Real.log (158037 / 250000) ≤ (57328967 / 125000000) := by
  have h := checkLog_sound (w := (91963 / 408037)) (n := 12)
    (lo := (91726347 / 200000000)) (hi := (57328967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158037) = 1/(158037 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-57328967 / 125000000) (-91726347 / 200000000) (Real.log (158037 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (78593537 / 250000000) ≤ -Real.log (500000 / 684701) ∧
    -Real.log (500000 / 684701) ≤ (314374149 / 1000000000) := by
  have h := checkLog_sound (w := (184701 / 1184701)) (n := 12)
    (lo := (78593537 / 250000000)) (hi := (314374149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684701 / 500000) = 1/(500000 / 684701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (78593537 / 250000000) (314374149 / 1000000000) (Real.log (684701 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (684701 / 500000) = -Real.log (500000 / 684701) := by
    rw [show ((684701 / 500000) : ℝ) = ((500000 / 684701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (461086703 / 1000000000) ≤ -Real.log (315299 / 500000) ∧
    -Real.log (315299 / 500000) ≤ (28817919 / 62500000) := by
  have h := checkLog_sound (w := (184701 / 815299)) (n := 12)
    (lo := (461086703 / 1000000000)) (hi := (28817919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 315299) = 1/(315299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28817919 / 62500000) (-461086703 / 1000000000) (Real.log (315299 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1062355881 / 1000000000) ≤ -Real.log (100000000000 / 289317895581) ∧
    -Real.log (100000000000 / 289317895581) ≤ (1062355883 / 1000000000) := by
  have h := checkLog_sound (w := (89317895581 / 489317895581)) (n := 12)
    (lo := (369208701 / 1000000000)) (hi := (184604351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289317895581 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(289317895581 / 200000000000) = 1/(100000000000 / 289317895581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1062355881 / 1000000000) (1062355883 / 1000000000) (Real.log (289317895581 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (289317895581 / 100000000000) = -Real.log (100000000000 / 289317895581) := by
    rw [show ((289317895581 / 100000000000) : ℝ) = ((100000000000 / 289317895581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1067068363 / 1000000000) ≤ -Real.log (500000000000 / 1453422591723) ∧
    -Real.log (500000000000 / 1453422591723) ≤ (213413673 / 200000000) := by
  have h := checkLog_sound (w := (453422591723 / 2453422591723)) (n := 12)
    (lo := (373921183 / 1000000000)) (hi := (11685037 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453422591723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1453422591723 / 1000000000000) = 1/(500000000000 / 1453422591723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1067068363 / 1000000000) (213413673 / 200000000) (Real.log (1453422591723 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1453422591723 / 500000000000) = -Real.log (500000000000 / 1453422591723) := by
    rw [show ((1453422591723 / 500000000000) : ℝ) = ((500000000000 / 1453422591723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9648417 / 12500000) ≤ -Real.log (250000000000 / 540954017097) ∧
    -Real.log (250000000000 / 540954017097) ≤ (385936681 / 500000000) := by
  have h := checkLog_sound (w := (40954017097 / 1040954017097)) (n := 12)
    (lo := (3936309 / 50000000)) (hi := (78726181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540954017097 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(540954017097 / 500000000000) = 1/(250000000000 / 540954017097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9648417 / 12500000) (385936681 / 500000000) (Real.log (540954017097 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (540954017097 / 250000000000) = -Real.log (250000000000 / 540954017097) := by
    rw [show ((540954017097 / 250000000000) : ℝ) = ((250000000000 / 540954017097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (775460851 / 1000000000) ≤ -Real.log (125000000000 / 271449084837) ∧
    -Real.log (125000000000 / 271449084837) ≤ (775460853 / 1000000000) := by
  have h := checkLog_sound (w := (21449084837 / 521449084837)) (n := 12)
    (lo := (82313671 / 1000000000)) (hi := (10289209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271449084837 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(271449084837 / 250000000000) = 1/(125000000000 / 271449084837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (775460851 / 1000000000) (775460853 / 1000000000) (Real.log (271449084837 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (271449084837 / 125000000000) = -Real.log (125000000000 / 271449084837) := by
    rw [show ((271449084837 / 125000000000) : ℝ) = ((125000000000 / 271449084837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0150
