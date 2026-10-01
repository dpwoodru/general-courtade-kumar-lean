import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042
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

theorem reflection_log_1_neg : (135962317 / 200000000) ≤ -Real.log (102400 / 202087) ∧
    -Real.log (102400 / 202087) ≤ (339905793 / 500000000) := by
  have h := checkLog_sound (w := (99687 / 304487)) (n := 12)
    (lo := (135962317 / 200000000)) (hi := (339905793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202087 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202087 / 102400) = 1/(102400 / 202087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135962317 / 200000000) (339905793 / 500000000) (Real.log (202087 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202087 / 102400) = -Real.log (102400 / 202087) := by
    rw [show ((202087 / 102400) : ℝ) = ((102400 / 202087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (907707919 / 250000000) ≤ -Real.log (2713 / 102400) ∧
    -Real.log (2713 / 102400) ≤ (1815415841 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2713) = 1/(2713 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) (Real.log (2713 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679717561 / 1000000000) ≤ -Real.log (25600 / 50517) ∧
    -Real.log (25600 / 50517) ≤ (339858781 / 500000000) := by
  have h := checkLog_sound (w := (24917 / 76117)) (n := 12)
    (lo := (679717561 / 1000000000)) (hi := (339858781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50517 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50517 / 25600) = 1/(25600 / 50517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679717561 / 1000000000) (339858781 / 500000000) (Real.log (50517 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50517 / 25600) = -Real.log (25600 / 50517) := by
    rw [show ((50517 / 25600) : ℝ) = ((25600 / 50517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113245399 / 31250000) ≤ -Real.log (683 / 25600) ∧
    -Real.log (683 / 25600) ≤ (1811926387 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 683) = 1/(683 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) (Real.log (683 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (133259149 / 200000000) ≤ -Real.log (51200 / 99687) ∧
    -Real.log (51200 / 99687) ≤ (333147873 / 500000000) := by
  have h := checkLog_sound (w := (48487 / 150887)) (n := 12)
    (lo := (133259149 / 200000000)) (hi := (333147873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99687 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99687 / 51200) = 1/(51200 / 99687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (133259149 / 200000000) (333147873 / 500000000) (Real.log (99687 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99687 / 51200) = -Real.log (51200 / 99687) := by
    rw [show ((99687 / 51200) : ℝ) = ((51200 / 99687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (183605281 / 62500000) ≤ -Real.log (2713 / 51200) ∧
    -Real.log (2713 / 51200) ≤ (2937684501 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2713) = 1/(2713 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) (Real.log (2713 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (66610513 / 100000000) ≤ -Real.log (12800 / 24917) ∧
    -Real.log (12800 / 24917) ≤ (666105131 / 1000000000) := by
  have h := checkLog_sound (w := (12117 / 37717)) (n := 12)
    (lo := (66610513 / 100000000)) (hi := (666105131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24917 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24917 / 12800) = 1/(12800 / 24917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (66610513 / 100000000) (666105131 / 1000000000) (Real.log (24917 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24917 / 12800) = -Real.log (12800 / 24917) := by
    rw [show ((24917 / 12800) : ℝ) = ((12800 / 24917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (732676397 / 250000000) ≤ -Real.log (683 / 12800) ∧
    -Real.log (683 / 12800) ≤ (2930705593 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 683) = 1/(683 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) (Real.log (683 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17046771 / 25000000) ≤ -Real.log (500000 / 988787) ∧
    -Real.log (500000 / 988787) ≤ (681870841 / 1000000000) := by
  have h := checkLog_sound (w := (488787 / 1488787)) (n := 12)
    (lo := (17046771 / 25000000)) (hi := (681870841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988787 / 500000) = 1/(500000 / 988787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17046771 / 25000000) (681870841 / 1000000000) (Real.log (988787 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (988787 / 500000) = -Real.log (500000 / 988787) := by
    rw [show ((988787 / 500000) : ℝ) = ((500000 / 988787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (949383569 / 250000000) ≤ -Real.log (11213 / 500000) ∧
    -Real.log (11213 / 500000) ≤ (1898767141 / 500000000) := by
  have h := checkLog_sound (w := (2206 / 13419)) (n := 12)
    (lo := (41474797 / 125000000)) (hi := (331798377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11213) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11213) = 1/(11213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1898767141 / 500000000) (-949383569 / 250000000) (Real.log (11213 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10655417 / 15625000) ≤ -Real.log (250000 / 494431) ∧
    -Real.log (250000 / 494431) ≤ (681946689 / 1000000000) := by
  have h := checkLog_sound (w := (244431 / 744431)) (n := 12)
    (lo := (10655417 / 15625000)) (hi := (681946689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494431 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494431 / 250000) = 1/(250000 / 494431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10655417 / 15625000) (681946689 / 1000000000) (Real.log (494431 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494431 / 250000) = -Real.log (250000 / 494431) := by
    rw [show ((494431 / 250000) : ℝ) = ((250000 / 494431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (380424541 / 100000000) ≤ -Real.log (5569 / 250000) ∧
    -Real.log (5569 / 250000) ≤ (475530677 / 125000000) := by
  have h := checkLog_sound (w := (4487 / 26763)) (n := 12)
    (lo := (33850951 / 100000000)) (hi := (338509511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11138) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11138) = 1/(5569 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-475530677 / 125000000) (-380424541 / 100000000) (Real.log (5569 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681812181 / 1000000000) ≤ -Real.log (500000 / 988729) ∧
    -Real.log (500000 / 988729) ≤ (340906091 / 500000000) := by
  have h := checkLog_sound (w := (488729 / 1488729)) (n := 12)
    (lo := (681812181 / 1000000000)) (hi := (340906091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988729 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988729 / 500000) = 1/(500000 / 988729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681812181 / 1000000000) (340906091 / 500000000) (Real.log (988729 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (988729 / 500000) = -Real.log (500000 / 988729) := by
    rw [show ((988729 / 500000) : ℝ) = ((500000 / 988729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2962793 / 781250) ≤ -Real.log (11271 / 500000) ∧
    -Real.log (11271 / 500000) ≤ (1896187523 / 500000000) := by
  have h := checkLog_sound (w := (2177 / 13448)) (n := 12)
    (lo := (16331957 / 50000000)) (hi := (326639141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11271) = 1/(11271 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1896187523 / 500000000) (-2962793 / 781250) (Real.log (11271 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681888539 / 1000000000) ≤ -Real.log (1000000 / 1977609) ∧
    -Real.log (1000000 / 1977609) ≤ (34094427 / 50000000) := by
  have h := checkLog_sound (w := (977609 / 2977609)) (n := 12)
    (lo := (681888539 / 1000000000)) (hi := (34094427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977609 / 1000000) = 1/(1000000 / 1977609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681888539 / 1000000000) (34094427 / 50000000) (Real.log (1977609 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977609 / 1000000) = -Real.log (1000000 / 1977609) := by
    rw [show ((1977609 / 1000000) : ℝ) = ((1000000 / 1977609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3799096183 / 1000000000) ≤ -Real.log (22391 / 1000000) ∧
    -Real.log (22391 / 1000000) ≤ (3799096189 / 1000000000) := by
  have h := checkLog_sound (w := (8859 / 53641)) (n := 12)
    (lo := (333360283 / 1000000000)) (hi := (83340071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22391) = 1/(22391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3799096189 / 1000000000) (-3799096183 / 1000000000) (Real.log (22391 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1119851279 / 250000000) ≤ -Real.log (125000000000 / 11022774904129) ∧
    -Real.log (125000000000 / 11022774904129) ≤ (4479405123 / 1000000000) := by
  have h := checkLog_sound (w := (3022774904129 / 19022774904129)) (n := 12)
    (lo := (80130509 / 250000000)) (hi := (320522037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11022774904129 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11022774904129 / 8000000000000) = 1/(125000000000 / 11022774904129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1119851279 / 250000000) (4479405123 / 1000000000) (Real.log (11022774904129 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11022774904129 / 125000000000) = -Real.log (125000000000 / 11022774904129) := by
    rw [show ((11022774904129 / 125000000000) : ℝ) = ((125000000000 / 11022774904129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2243096049 / 500000000) ≤ -Real.log (250000000000 / 22195681450889) ∧
    -Real.log (250000000000 / 22195681450889) ≤ (897238421 / 200000000) := by
  have h := checkLog_sound (w := (6195681450889 / 38195681450889)) (n := 12)
    (lo := (163654509 / 500000000)) (hi := (327309019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22195681450889 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22195681450889 / 16000000000000) = 1/(250000000000 / 22195681450889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2243096049 / 500000000) (897238421 / 200000000) (Real.log (22195681450889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (22195681450889 / 250000000000) = -Real.log (250000000000 / 22195681450889) := by
    rw [show ((22195681450889 / 250000000000) : ℝ) = ((250000000000 / 22195681450889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4474187221 / 1000000000) ≤ -Real.log (500000000000 / 43861636057137) ∧
    -Real.log (500000000000 / 43861636057137) ≤ (1118546807 / 250000000) := by
  have h := checkLog_sound (w := (11861636057137 / 75861636057137)) (n := 12)
    (lo := (315304141 / 1000000000)) (hi := (157652071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43861636057137 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43861636057137 / 32000000000000) = 1/(500000000000 / 43861636057137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4474187221 / 1000000000) (1118546807 / 250000000) (Real.log (43861636057137 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (43861636057137 / 500000000000) = -Real.log (500000000000 / 43861636057137) := by
    rw [show ((43861636057137 / 500000000000) : ℝ) = ((500000000000 / 43861636057137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2240492361 / 500000000) ≤ -Real.log (250000000000 / 22080400607387) ∧
    -Real.log (250000000000 / 22080400607387) ≤ (4480984729 / 1000000000) := by
  have h := checkLog_sound (w := (6080400607387 / 38080400607387)) (n := 12)
    (lo := (161050821 / 500000000)) (hi := (322101643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22080400607387 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22080400607387 / 16000000000000) = 1/(250000000000 / 22080400607387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2240492361 / 500000000) (4480984729 / 1000000000) (Real.log (22080400607387 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22080400607387 / 250000000000) = -Real.log (250000000000 / 22080400607387) := by
    rw [show ((22080400607387 / 250000000000) : ℝ) = ((250000000000 / 22080400607387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042
