import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0258
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

theorem reflection_log_1_neg : (239262933 / 1000000000) ≤ -Real.log (640 / 813) ∧
    -Real.log (640 / 813) ≤ (119631467 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1453)) (n := 12)
    (lo := (239262933 / 1000000000)) (hi := (119631467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 640) = 1/(640 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (239262933 / 1000000000) (119631467 / 500000000) (Real.log (813 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (813 / 640) = -Real.log (640 / 813) := by
    rw [show ((813 / 640) : ℝ) = ((640 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (157569459 / 500000000) ≤ -Real.log (467 / 640) ∧
    -Real.log (467 / 640) ≤ (315138919 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 467) = 1/(467 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-315138919 / 1000000000) (-157569459 / 500000000) (Real.log (467 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (59700393 / 250000000) ≤ -Real.log (5120 / 6501) ∧
    -Real.log (5120 / 6501) ≤ (238801573 / 1000000000) := by
  have h := checkLog_sound (w := (1381 / 11621)) (n := 12)
    (lo := (59700393 / 250000000)) (hi := (238801573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6501 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6501 / 5120) = 1/(5120 / 6501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (59700393 / 250000000) (238801573 / 1000000000) (Real.log (6501 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6501 / 5120) = -Real.log (5120 / 6501) := by
    rw [show ((6501 / 5120) : ℝ) = ((5120 / 6501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (314336243 / 1000000000) ≤ -Real.log (3739 / 5120) ∧
    -Real.log (3739 / 5120) ≤ (78584061 / 250000000) := by
  have h := checkLog_sound (w := (1381 / 8859)) (n := 12)
    (lo := (314336243 / 1000000000)) (hi := (78584061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3739) = 1/(3739 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78584061 / 250000000) (-314336243 / 1000000000) (Real.log (3739 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216094089 / 500000000) ≤ -Real.log (320 / 493) ∧
    -Real.log (320 / 493) ≤ (432188179 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 813)) (n := 12)
    (lo := (216094089 / 500000000)) (hi := (432188179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 320) = 1/(320 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216094089 / 500000000) (432188179 / 1000000000) (Real.log (493 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (493 / 320) = -Real.log (320 / 493) := by
    rw [show ((493 / 320) : ℝ) = ((320 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (97236051 / 125000000) ≤ -Real.log (147 / 320) ∧
    -Real.log (147 / 320) ≤ (77788841 / 100000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 147) = 1/(147 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77788841 / 100000000) (-97236051 / 125000000) (Real.log (147 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (431427239 / 1000000000) ≤ -Real.log (2560 / 3941) ∧
    -Real.log (2560 / 3941) ≤ (10785681 / 25000000) := by
  have h := checkLog_sound (w := (1381 / 6501)) (n := 12)
    (lo := (431427239 / 1000000000)) (hi := (10785681 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3941 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3941 / 2560) = 1/(2560 / 3941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (431427239 / 1000000000) (10785681 / 25000000) (Real.log (3941 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3941 / 2560) = -Real.log (2560 / 3941) := by
    rw [show ((3941 / 2560) : ℝ) = ((2560 / 3941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (193835159 / 250000000) ≤ -Real.log (1179 / 2560) ∧
    -Real.log (1179 / 2560) ≤ (387670319 / 500000000) := by
  have h := checkLog_sound (w := (101 / 2459)) (n := 12)
    (lo := (5137091 / 62500000)) (hi := (82193457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1179) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1179) = 1/(1179 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-387670319 / 500000000) (-193835159 / 250000000) (Real.log (1179 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (326956389 / 1000000000) ≤ -Real.log (1000000 / 1386741) ∧
    -Real.log (1000000 / 1386741) ≤ (32695639 / 100000000) := by
  have h := checkLog_sound (w := (386741 / 2386741)) (n := 12)
    (lo := (326956389 / 1000000000)) (hi := (32695639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1386741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1386741 / 1000000) = 1/(1000000 / 1386741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (326956389 / 1000000000) (32695639 / 100000000) (Real.log (1386741 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1386741 / 1000000) = -Real.log (1000000 / 1386741) := by
    rw [show ((1386741 / 1000000) : ℝ) = ((1000000 / 1386741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6112099 / 12500000) ≤ -Real.log (613259 / 1000000) ∧
    -Real.log (613259 / 1000000) ≤ (488967921 / 1000000000) := by
  have h := checkLog_sound (w := (386741 / 1613259)) (n := 12)
    (lo := (6112099 / 12500000)) (hi := (488967921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 613259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 613259) = 1/(613259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-488967921 / 1000000000) (-6112099 / 12500000) (Real.log (613259 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163791061 / 500000000) ≤ -Real.log (1000000 / 1387609) ∧
    -Real.log (1000000 / 1387609) ≤ (327582123 / 1000000000) := by
  have h := checkLog_sound (w := (387609 / 2387609)) (n := 12)
    (lo := (163791061 / 500000000)) (hi := (327582123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1387609 / 1000000) = 1/(1000000 / 1387609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163791061 / 500000000) (327582123 / 1000000000) (Real.log (1387609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1387609 / 1000000) = -Real.log (1000000 / 1387609) := by
    rw [show ((1387609 / 1000000) : ℝ) = ((1000000 / 1387609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (490384311 / 1000000000) ≤ -Real.log (612391 / 1000000) ∧
    -Real.log (612391 / 1000000) ≤ (61298039 / 125000000) := by
  have h := checkLog_sound (w := (387609 / 1612391)) (n := 12)
    (lo := (490384311 / 1000000000)) (hi := (61298039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 612391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 612391) = 1/(612391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-61298039 / 125000000) (-490384311 / 1000000000) (Real.log (612391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2509657 / 10000000) ≤ -Real.log (500000 / 642633) ∧
    -Real.log (500000 / 642633) ≤ (250965701 / 1000000000) := by
  have h := checkLog_sound (w := (142633 / 1142633)) (n := 12)
    (lo := (2509657 / 10000000)) (hi := (250965701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642633 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642633 / 500000) = 1/(500000 / 642633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2509657 / 10000000) (250965701 / 1000000000) (Real.log (642633 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (642633 / 500000) = -Real.log (500000 / 642633) := by
    rw [show ((642633 / 500000) : ℝ) = ((500000 / 642633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (335844833 / 1000000000) ≤ -Real.log (357367 / 500000) ∧
    -Real.log (357367 / 500000) ≤ (167922417 / 500000000) := by
  have h := checkLog_sound (w := (142633 / 857367)) (n := 12)
    (lo := (335844833 / 1000000000)) (hi := (167922417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357367) = 1/(357367 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-167922417 / 500000000) (-335844833 / 1000000000) (Real.log (357367 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125753149 / 500000000) ≤ -Real.log (1000000 / 1285961) ∧
    -Real.log (1000000 / 1285961) ≤ (251506299 / 1000000000) := by
  have h := checkLog_sound (w := (285961 / 2285961)) (n := 12)
    (lo := (125753149 / 500000000)) (hi := (251506299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285961 / 1000000) = 1/(1000000 / 1285961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125753149 / 500000000) (251506299 / 1000000000) (Real.log (1285961 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1285961 / 1000000) = -Real.log (1000000 / 1285961) := by
    rw [show ((1285961 / 1000000) : ℝ) = ((1000000 / 1285961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10525553 / 31250000) ≤ -Real.log (714039 / 1000000) ∧
    -Real.log (714039 / 1000000) ≤ (336817697 / 1000000000) := by
  have h := checkLog_sound (w := (285961 / 1714039)) (n := 12)
    (lo := (10525553 / 31250000)) (hi := (336817697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714039) = 1/(714039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-336817697 / 1000000000) (-10525553 / 31250000) (Real.log (714039 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (815924309 / 1000000000) ≤ -Real.log (250000000000 / 565316204083) ∧
    -Real.log (250000000000 / 565316204083) ≤ (815924311 / 1000000000) := by
  have h := checkLog_sound (w := (65316204083 / 1065316204083)) (n := 12)
    (lo := (122777129 / 1000000000)) (hi := (12277713 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565316204083 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565316204083 / 500000000000) = 1/(250000000000 / 565316204083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (815924309 / 1000000000) (815924311 / 1000000000) (Real.log (565316204083 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (565316204083 / 250000000000) = -Real.log (250000000000 / 565316204083) := by
    rw [show ((565316204083 / 250000000000) : ℝ) = ((250000000000 / 565316204083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (817966433 / 1000000000) ≤ -Real.log (100000000000 / 226588731709) ∧
    -Real.log (100000000000 / 226588731709) ≤ (163593287 / 200000000) := by
  have h := checkLog_sound (w := (26588731709 / 426588731709)) (n := 12)
    (lo := (124819253 / 1000000000)) (hi := (62409627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226588731709 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226588731709 / 200000000000) = 1/(100000000000 / 226588731709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (817966433 / 1000000000) (163593287 / 200000000) (Real.log (226588731709 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (226588731709 / 100000000000) = -Real.log (100000000000 / 226588731709) := by
    rw [show ((226588731709 / 100000000000) : ℝ) = ((100000000000 / 226588731709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (293405267 / 500000000) ≤ -Real.log (31250000000 / 56195119443) ∧
    -Real.log (31250000000 / 56195119443) ≤ (117362107 / 200000000) := by
  have h := checkLog_sound (w := (24945119443 / 87445119443)) (n := 12)
    (lo := (293405267 / 500000000)) (hi := (117362107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56195119443 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56195119443 / 31250000000) = 1/(31250000000 / 56195119443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (293405267 / 500000000) (117362107 / 200000000) (Real.log (56195119443 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56195119443 / 31250000000) = -Real.log (31250000000 / 56195119443) := by
    rw [show ((56195119443 / 31250000000) : ℝ) = ((31250000000 / 56195119443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117664799 / 200000000) ≤ -Real.log (12500000000 / 22512093177) ∧
    -Real.log (12500000000 / 22512093177) ≤ (147080999 / 250000000) := by
  have h := checkLog_sound (w := (10012093177 / 35012093177)) (n := 12)
    (lo := (117664799 / 200000000)) (hi := (147080999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22512093177 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22512093177 / 12500000000) = 1/(12500000000 / 22512093177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117664799 / 200000000) (147080999 / 250000000) (Real.log (22512093177 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22512093177 / 12500000000) = -Real.log (12500000000 / 22512093177) := by
    rw [show ((22512093177 / 12500000000) : ℝ) = ((12500000000 / 22512093177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0258
