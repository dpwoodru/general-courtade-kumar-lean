import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0194
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

theorem reflection_log_1_neg : (134177947 / 500000000) ≤ -Real.log (640 / 837) ∧
    -Real.log (640 / 837) ≤ (53671179 / 200000000) := by
  have h := checkLog_sound (w := (197 / 1477)) (n := 12)
    (lo := (134177947 / 500000000)) (hi := (53671179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 640) = 1/(640 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134177947 / 500000000) (53671179 / 200000000) (Real.log (837 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (837 / 640) = -Real.log (640 / 837) := by
    rw [show ((837 / 640) : ℝ) = ((640 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (183949203 / 500000000) ≤ -Real.log (443 / 640) ∧
    -Real.log (443 / 640) ≤ (367898407 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1083)) (n := 12)
    (lo := (183949203 / 500000000)) (hi := (367898407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 443) = 1/(443 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-367898407 / 1000000000) (-183949203 / 500000000) (Real.log (443 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53581553 / 200000000) ≤ -Real.log (5120 / 6693) ∧
    -Real.log (5120 / 6693) ≤ (133953883 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 11813)) (n := 12)
    (lo := (53581553 / 200000000)) (hi := (133953883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6693 / 5120) = 1/(5120 / 6693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53581553 / 200000000) (133953883 / 500000000) (Real.log (6693 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6693 / 5120) = -Real.log (5120 / 6693) := by
    rw [show ((6693 / 5120) : ℝ) = ((5120 / 6693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (367052263 / 1000000000) ≤ -Real.log (3547 / 5120) ∧
    -Real.log (3547 / 5120) ≤ (45881533 / 125000000) := by
  have h := checkLog_sound (w := (1573 / 8667)) (n := 12)
    (lo := (367052263 / 1000000000)) (hi := (45881533 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3547) = 1/(3547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45881533 / 125000000) (-367052263 / 1000000000) (Real.log (3547 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (478996277 / 1000000000) ≤ -Real.log (2560 / 4133) ∧
    -Real.log (2560 / 4133) ≤ (239498139 / 500000000) := by
  have h := checkLog_sound (w := (1573 / 6693)) (n := 12)
    (lo := (478996277 / 1000000000)) (hi := (239498139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4133 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4133 / 2560) = 1/(2560 / 4133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (478996277 / 1000000000) (239498139 / 500000000) (Real.log (4133 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4133 / 2560) = -Real.log (2560 / 4133) := by
    rw [show ((4133 / 2560) : ℝ) = ((2560 / 4133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (953092497 / 1000000000) ≤ -Real.log (987 / 2560) ∧
    -Real.log (987 / 2560) ≤ (953092499 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2267)) (n := 12)
    (lo := (259945317 / 1000000000)) (hi := (129972659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 987) = 1/(987 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-953092499 / 1000000000) (-953092497 / 1000000000) (Real.log (987 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (366501801 / 1000000000) ≤ -Real.log (1000000 / 1442679) ∧
    -Real.log (1000000 / 1442679) ≤ (183250901 / 500000000) := by
  have h := checkLog_sound (w := (442679 / 2442679)) (n := 12)
    (lo := (366501801 / 1000000000)) (hi := (183250901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1442679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1442679 / 1000000) = 1/(1000000 / 1442679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (366501801 / 1000000000) (183250901 / 500000000) (Real.log (1442679 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1442679 / 1000000) = -Real.log (1000000 / 1442679) := by
    rw [show ((1442679 / 1000000) : ℝ) = ((1000000 / 1442679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (584613903 / 1000000000) ≤ -Real.log (557321 / 1000000) ∧
    -Real.log (557321 / 1000000) ≤ (36538369 / 62500000) := by
  have h := checkLog_sound (w := (442679 / 1557321)) (n := 12)
    (lo := (584613903 / 1000000000)) (hi := (36538369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 557321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 557321) = 1/(557321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36538369 / 62500000) (-584613903 / 1000000000) (Real.log (557321 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (367114363 / 1000000000) ≤ -Real.log (1000000 / 1443563) ∧
    -Real.log (1000000 / 1443563) ≤ (91778591 / 250000000) := by
  have h := checkLog_sound (w := (443563 / 2443563)) (n := 12)
    (lo := (367114363 / 1000000000)) (hi := (91778591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443563 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443563 / 1000000) = 1/(1000000 / 1443563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (367114363 / 1000000000) (91778591 / 250000000) (Real.log (1443563 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1443563 / 1000000) = -Real.log (1000000 / 1443563) := by
    rw [show ((1443563 / 1000000) : ℝ) = ((1000000 / 1443563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (293100661 / 500000000) ≤ -Real.log (556437 / 1000000) ∧
    -Real.log (556437 / 1000000) ≤ (586201323 / 1000000000) := by
  have h := checkLog_sound (w := (443563 / 1556437)) (n := 12)
    (lo := (293100661 / 500000000)) (hi := (586201323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 556437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 556437) = 1/(556437 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-586201323 / 1000000000) (-293100661 / 500000000) (Real.log (556437 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (285880951 / 1000000000) ≤ -Real.log (500000 / 665467) ∧
    -Real.log (500000 / 665467) ≤ (35735119 / 125000000) := by
  have h := checkLog_sound (w := (165467 / 1165467)) (n := 12)
    (lo := (285880951 / 1000000000)) (hi := (35735119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665467 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665467 / 500000) = 1/(500000 / 665467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (285880951 / 1000000000) (35735119 / 125000000) (Real.log (665467 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (665467 / 500000) = -Real.log (500000 / 665467) := by
    rw [show ((665467 / 500000) : ℝ) = ((500000 / 665467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (401872569 / 1000000000) ≤ -Real.log (334533 / 500000) ∧
    -Real.log (334533 / 500000) ≤ (40187257 / 100000000) := by
  have h := checkLog_sound (w := (165467 / 834533)) (n := 12)
    (lo := (401872569 / 1000000000)) (hi := (40187257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334533) = 1/(334533 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40187257 / 100000000) (-401872569 / 1000000000) (Real.log (334533 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (286433793 / 1000000000) ≤ -Real.log (100000 / 133167) ∧
    -Real.log (100000 / 133167) ≤ (143216897 / 500000000) := by
  have h := checkLog_sound (w := (33167 / 233167)) (n := 12)
    (lo := (286433793 / 1000000000)) (hi := (143216897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133167 / 100000) = 1/(100000 / 133167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286433793 / 1000000000) (143216897 / 500000000) (Real.log (133167 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (133167 / 100000) = -Real.log (100000 / 133167) := by
    rw [show ((133167 / 100000) : ℝ) = ((100000 / 133167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (80594643 / 200000000) ≤ -Real.log (66833 / 100000) ∧
    -Real.log (66833 / 100000) ≤ (12592913 / 31250000) := by
  have h := checkLog_sound (w := (33167 / 166833)) (n := 12)
    (lo := (80594643 / 200000000)) (hi := (12592913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66833) = 1/(66833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-12592913 / 31250000) (-80594643 / 200000000) (Real.log (66833 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118889463 / 125000000) ≤ -Real.log (250000000000 / 647149039781) ∧
    -Real.log (250000000000 / 647149039781) ≤ (475557853 / 500000000) := by
  have h := checkLog_sound (w := (147149039781 / 1147149039781)) (n := 12)
    (lo := (64492131 / 250000000)) (hi := (10318741 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647149039781 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(647149039781 / 500000000000) = 1/(250000000000 / 647149039781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118889463 / 125000000) (475557853 / 500000000) (Real.log (647149039781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (647149039781 / 250000000000) = -Real.log (250000000000 / 647149039781) := by
    rw [show ((647149039781 / 250000000000) : ℝ) = ((250000000000 / 647149039781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (238328921 / 250000000) ≤ -Real.log (250000000000 / 648574321981) ∧
    -Real.log (250000000000 / 648574321981) ≤ (476657843 / 500000000) := by
  have h := checkLog_sound (w := (148574321981 / 1148574321981)) (n := 12)
    (lo := (32521063 / 125000000)) (hi := (52033701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648574321981 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(648574321981 / 500000000000) = 1/(250000000000 / 648574321981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (238328921 / 250000000) (476657843 / 500000000) (Real.log (648574321981 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (648574321981 / 250000000000) = -Real.log (250000000000 / 648574321981) := by
    rw [show ((648574321981 / 250000000000) : ℝ) = ((250000000000 / 648574321981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8596919 / 12500000) ≤ -Real.log (250000000000 / 497310429763) ∧
    -Real.log (250000000000 / 497310429763) ≤ (687753521 / 1000000000) := by
  have h := checkLog_sound (w := (247310429763 / 747310429763)) (n := 12)
    (lo := (8596919 / 12500000)) (hi := (687753521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497310429763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497310429763 / 250000000000) = 1/(250000000000 / 497310429763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (8596919 / 12500000) (687753521 / 1000000000) (Real.log (497310429763 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (497310429763 / 250000000000) = -Real.log (250000000000 / 497310429763) := by
    rw [show ((497310429763 / 250000000000) : ℝ) = ((250000000000 / 497310429763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (689407009 / 1000000000) ≤ -Real.log (500000000000 / 996266814299) ∧
    -Real.log (500000000000 / 996266814299) ≤ (68940701 / 100000000) := by
  have h := checkLog_sound (w := (496266814299 / 1496266814299)) (n := 12)
    (lo := (689407009 / 1000000000)) (hi := (68940701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996266814299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996266814299 / 500000000000) = 1/(500000000000 / 996266814299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (689407009 / 1000000000) (68940701 / 100000000) (Real.log (996266814299 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (996266814299 / 500000000000) = -Real.log (500000000000 / 996266814299) := by
    rw [show ((996266814299 / 500000000000) : ℝ) = ((500000000000 / 996266814299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0194
