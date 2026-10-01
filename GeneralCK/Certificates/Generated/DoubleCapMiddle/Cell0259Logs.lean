import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0259
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

theorem reflection_log_1_neg : (59700393 / 250000000) ≤ -Real.log (5120 / 6501) ∧
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


theorem reflection_log_1 : Bounds (59700393 / 250000000) (238801573 / 1000000000) (Real.log (6501 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6501 / 5120) = -Real.log (5120 / 6501) := by
    rw [show ((6501 / 5120) : ℝ) = ((5120 / 6501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (314336243 / 1000000000) ≤ -Real.log (3739 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-78584061 / 250000000) (-314336243 / 1000000000) (Real.log (3739 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (119169999 / 500000000) ≤ -Real.log (2560 / 3249) ∧
    -Real.log (2560 / 3249) ≤ (238339999 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 5809)) (n := 12)
    (lo := (119169999 / 500000000)) (hi := (238339999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3249 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3249 / 2560) = 1/(2560 / 3249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (119169999 / 500000000) (238339999 / 1000000000) (Real.log (3249 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3249 / 2560) = -Real.log (2560 / 3249) := by
    rw [show ((3249 / 2560) : ℝ) = ((2560 / 3249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (313534211 / 1000000000) ≤ -Real.log (1871 / 2560) ∧
    -Real.log (1871 / 2560) ≤ (78383553 / 250000000) := by
  have h := checkLog_sound (w := (689 / 4431)) (n := 12)
    (lo := (313534211 / 1000000000)) (hi := (78383553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1871) = 1/(1871 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) (Real.log (1871 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (431427239 / 1000000000) ≤ -Real.log (2560 / 3941) ∧
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


theorem reflection_log_5 : Bounds (431427239 / 1000000000) (10785681 / 25000000) (Real.log (3941 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3941 / 2560) = -Real.log (2560 / 3941) := by
    rw [show ((3941 / 2560) : ℝ) = ((2560 / 3941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (193835159 / 250000000) ≤ -Real.log (1179 / 2560) ∧
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


theorem reflection_log_6 : Bounds (-387670319 / 500000000) (-193835159 / 250000000) (Real.log (1179 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (430665721 / 1000000000) ≤ -Real.log (1280 / 1969) ∧
    -Real.log (1280 / 1969) ≤ (215332861 / 500000000) := by
  have h := checkLog_sound (w := (689 / 3249)) (n := 12)
    (lo := (430665721 / 1000000000)) (hi := (215332861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1280) = 1/(1280 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (430665721 / 1000000000) (215332861 / 500000000) (Real.log (1969 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1969 / 1280) = -Real.log (1280 / 1969) := by
    rw [show ((1969 / 1280) : ℝ) = ((1280 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (386399669 / 500000000) ≤ -Real.log (591 / 1280) ∧
    -Real.log (591 / 1280) ≤ (38639967 / 50000000) := by
  have h := checkLog_sound (w := (49 / 1231)) (n := 12)
    (lo := (39826079 / 500000000)) (hi := (79652159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 591) = 1/(591 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) (Real.log (591 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (326331709 / 1000000000) ≤ -Real.log (8000 / 11087) ∧
    -Real.log (8000 / 11087) ≤ (32633171 / 100000000) := by
  have h := checkLog_sound (w := (3087 / 19087)) (n := 12)
    (lo := (326331709 / 1000000000)) (hi := (32633171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11087 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11087 / 8000) = 1/(8000 / 11087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (326331709 / 1000000000) (32633171 / 100000000) (Real.log (11087 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11087 / 8000) = -Real.log (8000 / 11087) := by
    rw [show ((11087 / 8000) : ℝ) = ((8000 / 11087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (121889197 / 250000000) ≤ -Real.log (4913 / 8000) ∧
    -Real.log (4913 / 8000) ≤ (487556789 / 1000000000) := by
  have h := checkLog_sound (w := (3087 / 12913)) (n := 12)
    (lo := (121889197 / 250000000)) (hi := (487556789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 4913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 4913) = 1/(4913 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487556789 / 1000000000) (-121889197 / 250000000) (Real.log (4913 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (326957111 / 1000000000) ≤ -Real.log (500000 / 693371) ∧
    -Real.log (500000 / 693371) ≤ (40869639 / 125000000) := by
  have h := checkLog_sound (w := (193371 / 1193371)) (n := 12)
    (lo := (326957111 / 1000000000)) (hi := (40869639 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693371 / 500000) = 1/(500000 / 693371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (326957111 / 1000000000) (40869639 / 125000000) (Real.log (693371 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (693371 / 500000) = -Real.log (500000 / 693371) := by
    rw [show ((693371 / 500000) : ℝ) = ((500000 / 693371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9779391 / 20000000) ≤ -Real.log (306629 / 500000) ∧
    -Real.log (306629 / 500000) ≤ (488969551 / 1000000000) := by
  have h := checkLog_sound (w := (193371 / 806629)) (n := 12)
    (lo := (9779391 / 20000000)) (hi := (488969551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 306629) = 1/(306629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-488969551 / 1000000000) (-9779391 / 20000000) (Real.log (306629 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (62606397 / 250000000) ≤ -Real.log (250000 / 321143) ∧
    -Real.log (250000 / 321143) ≤ (250425589 / 1000000000) := by
  have h := checkLog_sound (w := (71143 / 571143)) (n := 12)
    (lo := (62606397 / 250000000)) (hi := (250425589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321143 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321143 / 250000) = 1/(250000 / 321143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (62606397 / 250000000) (250425589 / 1000000000) (Real.log (321143 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (321143 / 250000) = -Real.log (250000 / 321143) := by
    rw [show ((321143 / 250000) : ℝ) = ((250000 / 321143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (334874313 / 1000000000) ≤ -Real.log (178857 / 250000) ∧
    -Real.log (178857 / 250000) ≤ (167437157 / 500000000) := by
  have h := checkLog_sound (w := (71143 / 428857)) (n := 12)
    (lo := (334874313 / 1000000000)) (hi := (167437157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178857) = 1/(178857 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-167437157 / 500000000) (-334874313 / 1000000000) (Real.log (178857 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125483239 / 500000000) ≤ -Real.log (1000000 / 1285267) ∧
    -Real.log (1000000 / 1285267) ≤ (250966479 / 1000000000) := by
  have h := checkLog_sound (w := (285267 / 2285267)) (n := 12)
    (lo := (125483239 / 500000000)) (hi := (250966479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285267 / 1000000) = 1/(1000000 / 1285267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125483239 / 500000000) (250966479 / 1000000000) (Real.log (1285267 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1285267 / 1000000) = -Real.log (1000000 / 1285267) := by
    rw [show ((1285267 / 1000000) : ℝ) = ((1000000 / 1285267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41980779 / 125000000) ≤ -Real.log (714733 / 1000000) ∧
    -Real.log (714733 / 1000000) ≤ (335846233 / 1000000000) := by
  have h := checkLog_sound (w := (285267 / 1714733)) (n := 12)
    (lo := (41980779 / 125000000)) (hi := (335846233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714733) = 1/(714733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-335846233 / 1000000000) (-41980779 / 125000000) (Real.log (714733 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (813888497 / 1000000000) ≤ -Real.log (500000000000 / 1128332994097) ∧
    -Real.log (500000000000 / 1128332994097) ≤ (813888499 / 1000000000) := by
  have h := checkLog_sound (w := (128332994097 / 2128332994097)) (n := 12)
    (lo := (120741317 / 1000000000)) (hi := (60370659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128332994097 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1128332994097 / 1000000000000) = 1/(500000000000 / 1128332994097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (813888497 / 1000000000) (813888499 / 1000000000) (Real.log (1128332994097 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1128332994097 / 500000000000) = -Real.log (500000000000 / 1128332994097) := by
    rw [show ((1128332994097 / 500000000000) : ℝ) = ((500000000000 / 1128332994097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (815926661 / 1000000000) ≤ -Real.log (250000000000 / 565317533567) ∧
    -Real.log (250000000000 / 565317533567) ≤ (815926663 / 1000000000) := by
  have h := checkLog_sound (w := (65317533567 / 1065317533567)) (n := 12)
    (lo := (122779481 / 1000000000)) (hi := (61389741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565317533567 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(565317533567 / 500000000000) = 1/(250000000000 / 565317533567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (815926661 / 1000000000) (815926663 / 1000000000) (Real.log (565317533567 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (565317533567 / 250000000000) = -Real.log (250000000000 / 565317533567) := by
    rw [show ((565317533567 / 250000000000) : ℝ) = ((250000000000 / 565317533567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (292649951 / 500000000) ≤ -Real.log (5000000000 / 8977646947) ∧
    -Real.log (5000000000 / 8977646947) ≤ (585299903 / 1000000000) := by
  have h := checkLog_sound (w := (3977646947 / 13977646947)) (n := 12)
    (lo := (292649951 / 500000000)) (hi := (585299903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8977646947 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8977646947 / 5000000000) = 1/(5000000000 / 8977646947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (292649951 / 500000000) (585299903 / 1000000000) (Real.log (8977646947 / 5000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8977646947 / 5000000000) = -Real.log (5000000000 / 8977646947) := by
    rw [show ((8977646947 / 5000000000) : ℝ) = ((5000000000 / 8977646947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (586812711 / 1000000000) ≤ -Real.log (250000000000 / 449561934317) ∧
    -Real.log (250000000000 / 449561934317) ≤ (73351589 / 125000000) := by
  have h := checkLog_sound (w := (199561934317 / 699561934317)) (n := 12)
    (lo := (586812711 / 1000000000)) (hi := (73351589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449561934317 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449561934317 / 250000000000) = 1/(250000000000 / 449561934317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (586812711 / 1000000000) (73351589 / 125000000) (Real.log (449561934317 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (449561934317 / 250000000000) = -Real.log (250000000000 / 449561934317) := by
    rw [show ((449561934317 / 250000000000) : ℝ) = ((250000000000 / 449561934317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0259
