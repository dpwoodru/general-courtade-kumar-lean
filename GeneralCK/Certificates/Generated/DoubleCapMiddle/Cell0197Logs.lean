import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0197
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

theorem reflection_log_1_neg : (33376363 / 125000000) ≤ -Real.log (5120 / 6687) ∧
    -Real.log (5120 / 6687) ≤ (53402181 / 200000000) := by
  have h := checkLog_sound (w := (1567 / 11807)) (n := 12)
    (lo := (33376363 / 125000000)) (hi := (53402181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6687 / 5120) = 1/(5120 / 6687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33376363 / 125000000) (53402181 / 200000000) (Real.log (6687 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6687 / 5120) = -Real.log (5120 / 6687) := by
    rw [show ((6687 / 5120) : ℝ) = ((5120 / 6687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (182681061 / 500000000) ≤ -Real.log (3553 / 5120) ∧
    -Real.log (3553 / 5120) ≤ (365362123 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 8673)) (n := 12)
    (lo := (182681061 / 500000000)) (hi := (365362123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3553) = 1/(3553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-365362123 / 1000000000) (-182681061 / 500000000) (Real.log (3553 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (266562171 / 1000000000) ≤ -Real.log (1280 / 1671) ∧
    -Real.log (1280 / 1671) ≤ (66640543 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2951)) (n := 12)
    (lo := (266562171 / 1000000000)) (hi := (66640543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1280) = 1/(1280 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (266562171 / 1000000000) (66640543 / 250000000) (Real.log (1671 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1671 / 1280) = -Real.log (1280 / 1671) := by
    rw [show ((1671 / 1280) : ℝ) = ((1280 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (364518121 / 1000000000) ≤ -Real.log (889 / 1280) ∧
    -Real.log (889 / 1280) ≤ (182259061 / 500000000) := by
  have h := checkLog_sound (w := (391 / 2169)) (n := 12)
    (lo := (364518121 / 1000000000)) (hi := (182259061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 889) = 1/(889 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-182259061 / 500000000) (-364518121 / 1000000000) (Real.log (889 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119385873 / 250000000) ≤ -Real.log (2560 / 4127) ∧
    -Real.log (2560 / 4127) ≤ (477543493 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 6687)) (n := 12)
    (lo := (119385873 / 250000000)) (hi := (477543493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4127 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4127 / 2560) = 1/(2560 / 4127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119385873 / 250000000) (477543493 / 1000000000) (Real.log (4127 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4127 / 2560) = -Real.log (2560 / 4127) := by
    rw [show ((4127 / 2560) : ℝ) = ((2560 / 4127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14797373 / 15625000) ≤ -Real.log (993 / 2560) ∧
    -Real.log (993 / 2560) ≤ (473515937 / 500000000) := by
  have h := checkLog_sound (w := (287 / 2273)) (n := 12)
    (lo := (63471173 / 250000000)) (hi := (253884693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 993) = 1/(993 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-473515937 / 500000000) (-14797373 / 15625000) (Real.log (993 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (476816307 / 1000000000) ≤ -Real.log (640 / 1031) ∧
    -Real.log (640 / 1031) ≤ (119204077 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1671)) (n := 12)
    (lo := (476816307 / 1000000000)) (hi := (119204077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1031 / 640) = 1/(640 / 1031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (476816307 / 1000000000) (119204077 / 250000000) (Real.log (1031 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1031 / 640) = -Real.log (640 / 1031) := by
    rw [show ((1031 / 640) : ℝ) = ((640 / 1031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (944015279 / 1000000000) ≤ -Real.log (249 / 640) ∧
    -Real.log (249 / 640) ≤ (944015281 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 249) = 1/(249 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-944015281 / 1000000000) (-944015279 / 1000000000) (Real.log (249 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (91166681 / 250000000) ≤ -Real.log (500000 / 720017) ∧
    -Real.log (500000 / 720017) ≤ (14586669 / 40000000) := by
  have h := checkLog_sound (w := (220017 / 1220017)) (n := 12)
    (lo := (91166681 / 250000000)) (hi := (14586669 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720017 / 500000) = 1/(500000 / 720017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (91166681 / 250000000) (14586669 / 40000000) (Real.log (720017 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (720017 / 500000) = -Real.log (500000 / 720017) := by
    rw [show ((720017 / 500000) : ℝ) = ((500000 / 720017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (579879211 / 1000000000) ≤ -Real.log (279983 / 500000) ∧
    -Real.log (279983 / 500000) ≤ (144969803 / 250000000) := by
  have h := checkLog_sound (w := (220017 / 779983)) (n := 12)
    (lo := (579879211 / 1000000000)) (hi := (144969803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279983) = 1/(279983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-144969803 / 250000000) (-579879211 / 1000000000) (Real.log (279983 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (182639511 / 500000000) ≤ -Real.log (250000 / 360229) ∧
    -Real.log (250000 / 360229) ≤ (365279023 / 1000000000) := by
  have h := checkLog_sound (w := (110229 / 610229)) (n := 12)
    (lo := (182639511 / 500000000)) (hi := (365279023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360229 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360229 / 250000) = 1/(250000 / 360229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (182639511 / 500000000) (365279023 / 1000000000) (Real.log (360229 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (360229 / 250000) = -Real.log (250000 / 360229) := by
    rw [show ((360229 / 250000) : ℝ) = ((250000 / 360229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145363887 / 250000000) ≤ -Real.log (139771 / 250000) ∧
    -Real.log (139771 / 250000) ≤ (581455549 / 1000000000) := by
  have h := checkLog_sound (w := (110229 / 389771)) (n := 12)
    (lo := (145363887 / 250000000)) (hi := (581455549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 139771) = 1/(139771 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-581455549 / 1000000000) (-145363887 / 250000000) (Real.log (139771 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4441029 / 15625000) ≤ -Real.log (1000000 / 1328733) ∧
    -Real.log (1000000 / 1328733) ≤ (284225857 / 1000000000) := by
  have h := checkLog_sound (w := (328733 / 2328733)) (n := 12)
    (lo := (4441029 / 15625000)) (hi := (284225857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328733 / 1000000) = 1/(1000000 / 1328733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4441029 / 15625000) (284225857 / 1000000000) (Real.log (1328733 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1328733 / 1000000) = -Real.log (1000000 / 1328733) := by
    rw [show ((1328733 / 1000000) : ℝ) = ((1000000 / 1328733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (398588307 / 1000000000) ≤ -Real.log (671267 / 1000000) ∧
    -Real.log (671267 / 1000000) ≤ (99647077 / 250000000) := by
  have h := checkLog_sound (w := (328733 / 1671267)) (n := 12)
    (lo := (398588307 / 1000000000)) (hi := (99647077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671267) = 1/(671267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-99647077 / 250000000) (-398588307 / 1000000000) (Real.log (671267 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (28477811 / 100000000) ≤ -Real.log (1000000 / 1329467) ∧
    -Real.log (1000000 / 1329467) ≤ (284778111 / 1000000000) := by
  have h := checkLog_sound (w := (329467 / 2329467)) (n := 12)
    (lo := (28477811 / 100000000)) (hi := (284778111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329467 / 1000000) = 1/(1000000 / 1329467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28477811 / 100000000) (284778111 / 1000000000) (Real.log (1329467 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1329467 / 1000000) = -Real.log (1000000 / 1329467) := by
    rw [show ((1329467 / 1000000) : ℝ) = ((1000000 / 1329467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (9992059 / 25000000) ≤ -Real.log (670533 / 1000000) ∧
    -Real.log (670533 / 1000000) ≤ (399682361 / 1000000000) := by
  have h := checkLog_sound (w := (329467 / 1670533)) (n := 12)
    (lo := (9992059 / 25000000)) (hi := (399682361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670533) = 1/(670533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-399682361 / 1000000000) (-9992059 / 25000000) (Real.log (670533 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (188909187 / 200000000) ≤ -Real.log (62500000000 / 160727838833) ∧
    -Real.log (62500000000 / 160727838833) ≤ (944545937 / 1000000000) := by
  have h := checkLog_sound (w := (35727838833 / 285727838833)) (n := 12)
    (lo := (50279751 / 200000000)) (hi := (62849689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160727838833 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160727838833 / 125000000000) = 1/(62500000000 / 160727838833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (188909187 / 200000000) (944545937 / 1000000000) (Real.log (160727838833 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (160727838833 / 62500000000) = -Real.log (62500000000 / 160727838833) := by
    rw [show ((160727838833 / 62500000000) : ℝ) = ((62500000000 / 160727838833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (94673457 / 100000000) ≤ -Real.log (250000000000 / 644319994849) ∧
    -Real.log (250000000000 / 644319994849) ≤ (236683643 / 250000000) := by
  have h := checkLog_sound (w := (144319994849 / 1144319994849)) (n := 12)
    (lo := (25358739 / 100000000)) (hi := (253587391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644319994849 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(644319994849 / 500000000000) = 1/(250000000000 / 644319994849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (94673457 / 100000000) (236683643 / 250000000) (Real.log (644319994849 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (644319994849 / 250000000000) = -Real.log (250000000000 / 644319994849) := by
    rw [show ((644319994849 / 250000000000) : ℝ) = ((250000000000 / 644319994849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (170703541 / 250000000) ≤ -Real.log (500000000000 / 989720185857) ∧
    -Real.log (500000000000 / 989720185857) ≤ (136562833 / 200000000) := by
  have h := checkLog_sound (w := (489720185857 / 1489720185857)) (n := 12)
    (lo := (170703541 / 250000000)) (hi := (136562833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989720185857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989720185857 / 500000000000) = 1/(500000000000 / 989720185857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (170703541 / 250000000) (136562833 / 200000000) (Real.log (989720185857 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (989720185857 / 500000000000) = -Real.log (500000000000 / 989720185857) := by
    rw [show ((989720185857 / 500000000000) : ℝ) = ((500000000000 / 989720185857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68446047 / 100000000) ≤ -Real.log (125000000000 / 247837727599) ∧
    -Real.log (125000000000 / 247837727599) ≤ (684460471 / 1000000000) := by
  have h := checkLog_sound (w := (122837727599 / 372837727599)) (n := 12)
    (lo := (68446047 / 100000000)) (hi := (684460471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247837727599 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247837727599 / 125000000000) = 1/(125000000000 / 247837727599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68446047 / 100000000) (684460471 / 1000000000) (Real.log (247837727599 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (247837727599 / 125000000000) = -Real.log (125000000000 / 247837727599) := by
    rw [show ((247837727599 / 125000000000) : ℝ) = ((125000000000 / 247837727599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0197
