import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141
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

theorem reflection_log_1_neg : (131609219 / 200000000) ≤ -Real.log (12800 / 24717) ∧
    -Real.log (12800 / 24717) ≤ (41127881 / 62500000) := by
  have h := checkLog_sound (w := (11917 / 37517)) (n := 12)
    (lo := (131609219 / 200000000)) (hi := (41127881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24717 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24717 / 12800) = 1/(12800 / 24717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131609219 / 200000000) (41127881 / 62500000) (Real.log (24717 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24717 / 12800) = -Real.log (12800 / 24717) := by
    rw [show ((24717 / 12800) : ℝ) = ((12800 / 24717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2673875247 / 1000000000) ≤ -Real.log (883 / 12800) ∧
    -Real.log (883 / 12800) ≤ (2673875251 / 1000000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 883) = 1/(883 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) (Real.log (883 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65766167 / 100000000) ≤ -Real.log (5120 / 9883) ∧
    -Real.log (5120 / 9883) ≤ (657661671 / 1000000000) := by
  have h := checkLog_sound (w := (4763 / 15003)) (n := 12)
    (lo := (65766167 / 100000000)) (hi := (657661671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9883 / 5120) = 1/(5120 / 9883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65766167 / 100000000) (657661671 / 1000000000) (Real.log (9883 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9883 / 5120) = -Real.log (5120 / 9883) := by
    rw [show ((9883 / 5120) : ℝ) = ((5120 / 9883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1331586967 / 500000000) ≤ -Real.log (357 / 5120) ∧
    -Real.log (357 / 5120) ≤ (1331586969 / 500000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 357) = 1/(357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) (Real.log (357 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (621667961 / 1000000000) ≤ -Real.log (6400 / 11917) ∧
    -Real.log (6400 / 11917) ≤ (310833981 / 500000000) := by
  have h := checkLog_sound (w := (5517 / 18317)) (n := 12)
    (lo := (621667961 / 1000000000)) (hi := (310833981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 6400) = 1/(6400 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (621667961 / 1000000000) (310833981 / 500000000) (Real.log (11917 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11917 / 6400) = -Real.log (6400 / 11917) := by
    rw [show ((11917 / 6400) : ℝ) = ((6400 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1980728067 / 1000000000) ≤ -Real.log (883 / 6400) ∧
    -Real.log (883 / 6400) ≤ (198072807 / 100000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 883) = 1/(883 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) (Real.log (883 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (620870463 / 1000000000) ≤ -Real.log (2560 / 4763) ∧
    -Real.log (2560 / 4763) ≤ (9701101 / 15625000) := by
  have h := checkLog_sound (w := (2203 / 7323)) (n := 12)
    (lo := (620870463 / 1000000000)) (hi := (9701101 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4763 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4763 / 2560) = 1/(2560 / 4763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (620870463 / 1000000000) (9701101 / 15625000) (Real.log (4763 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4763 / 2560) = -Real.log (2560 / 4763) := by
    rw [show ((4763 / 2560) : ℝ) = ((2560 / 4763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (985013377 / 500000000) ≤ -Real.log (357 / 2560) ∧
    -Real.log (357 / 2560) ≤ (1970026757 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(640 / 357) = 1/(357 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) (Real.log (357 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (332555147 / 500000000) ≤ -Real.log (200000 / 388941) ∧
    -Real.log (200000 / 388941) ≤ (133022059 / 200000000) := by
  have h := checkLog_sound (w := (188941 / 588941)) (n := 12)
    (lo := (332555147 / 500000000)) (hi := (133022059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388941 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388941 / 200000) = 1/(200000 / 388941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (332555147 / 500000000) (133022059 / 200000000) (Real.log (388941 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (388941 / 200000) = -Real.log (200000 / 388941) := by
    rw [show ((388941 / 200000) : ℝ) = ((200000 / 388941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (723768197 / 250000000) ≤ -Real.log (11059 / 200000) ∧
    -Real.log (11059 / 200000) ≤ (2895072793 / 1000000000) := by
  have h := checkLog_sound (w := (1441 / 23559)) (n := 12)
    (lo := (30621017 / 250000000)) (hi := (122484069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11059) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11059) = 1/(11059 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2895072793 / 1000000000) (-723768197 / 250000000) (Real.log (11059 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (665388961 / 1000000000) ≤ -Real.log (1000000 / 1945247) ∧
    -Real.log (1000000 / 1945247) ≤ (332694481 / 500000000) := by
  have h := checkLog_sound (w := (945247 / 2945247)) (n := 12)
    (lo := (665388961 / 1000000000)) (hi := (332694481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1945247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1945247 / 1000000) = 1/(1000000 / 1945247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (665388961 / 1000000000) (332694481 / 500000000) (Real.log (1945247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1945247 / 1000000) = -Real.log (1000000 / 1945247) := by
    rw [show ((1945247 / 1000000) : ℝ) = ((1000000 / 1945247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (580984623 / 200000000) ≤ -Real.log (54753 / 1000000) ∧
    -Real.log (54753 / 1000000) ≤ (36311539 / 12500000) := by
  have h := checkLog_sound (w := (7747 / 117253)) (n := 12)
    (lo := (26466879 / 200000000)) (hi := (33083599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54753) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 54753) = 1/(54753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36311539 / 12500000) (-580984623 / 200000000) (Real.log (54753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (83072821 / 125000000) ≤ -Real.log (1000000 / 1943679) ∧
    -Real.log (1000000 / 1943679) ≤ (664582569 / 1000000000) := by
  have h := checkLog_sound (w := (943679 / 2943679)) (n := 12)
    (lo := (83072821 / 125000000)) (hi := (664582569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943679 / 1000000) = 1/(1000000 / 1943679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (83072821 / 125000000) (664582569 / 1000000000) (Real.log (1943679 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1943679 / 1000000) = -Real.log (1000000 / 1943679) := by
    rw [show ((1943679 / 1000000) : ℝ) = ((1000000 / 1943679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2876687809 / 1000000000) ≤ -Real.log (56321 / 1000000) ∧
    -Real.log (56321 / 1000000) ≤ (1438343907 / 500000000) := by
  have h := checkLog_sound (w := (6179 / 118821)) (n := 12)
    (lo := (104099089 / 1000000000)) (hi := (10409909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56321) = 1/(56321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1438343907 / 500000000) (-2876687809 / 1000000000) (Real.log (56321 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (332436863 / 500000000) ≤ -Real.log (200000 / 388849) ∧
    -Real.log (200000 / 388849) ≤ (664873727 / 1000000000) := by
  have h := checkLog_sound (w := (188849 / 588849)) (n := 12)
    (lo := (332436863 / 500000000)) (hi := (664873727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388849 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388849 / 200000) = 1/(200000 / 388849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (332436863 / 500000000) (664873727 / 1000000000) (Real.log (388849 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388849 / 200000) = -Real.log (200000 / 388849) := by
    rw [show ((388849 / 200000) : ℝ) = ((200000 / 388849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (360848523 / 125000000) ≤ -Real.log (11151 / 200000) ∧
    -Real.log (11151 / 200000) ≤ (2886788189 / 1000000000) := by
  have h := checkLog_sound (w := (1349 / 23651)) (n := 12)
    (lo := (14274933 / 125000000)) (hi := (22839893 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11151) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11151) = 1/(11151 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2886788189 / 1000000000) (-360848523 / 125000000) (Real.log (11151 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1780091541 / 500000000) ≤ -Real.log (25000000000 / 879240889773) ∧
    -Real.log (25000000000 / 879240889773) ≤ (222511443 / 62500000) := by
  have h := checkLog_sound (w := (79240889773 / 1679240889773)) (n := 12)
    (lo := (47223591 / 500000000)) (hi := (94447183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879240889773 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(879240889773 / 800000000000) = 1/(25000000000 / 879240889773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1780091541 / 500000000) (222511443 / 62500000) (Real.log (879240889773 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (879240889773 / 25000000000) = -Real.log (25000000000 / 879240889773) := by
    rw [show ((879240889773 / 25000000000) : ℝ) = ((25000000000 / 879240889773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142812483 / 40000000) ≤ -Real.log (125000000000 / 4440959856081) ∧
    -Real.log (125000000000 / 4440959856081) ≤ (3570312081 / 1000000000) := by
  have h := checkLog_sound (w := (440959856081 / 8440959856081)) (n := 12)
    (lo := (4183047 / 40000000)) (hi := (6536011 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4440959856081 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4440959856081 / 4000000000000) = 1/(125000000000 / 4440959856081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142812483 / 40000000) (3570312081 / 1000000000) (Real.log (4440959856081 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4440959856081 / 125000000000) = -Real.log (125000000000 / 4440959856081) := by
    rw [show ((4440959856081 / 125000000000) : ℝ) = ((125000000000 / 4440959856081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3541270377 / 1000000000) ≤ -Real.log (250000000000 / 8627683279771) ∧
    -Real.log (250000000000 / 8627683279771) ≤ (3541270383 / 1000000000) := by
  have h := checkLog_sound (w := (627683279771 / 16627683279771)) (n := 12)
    (lo := (75534477 / 1000000000)) (hi := (37767239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8627683279771 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8627683279771 / 8000000000000) = 1/(250000000000 / 8627683279771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3541270377 / 1000000000) (3541270383 / 1000000000) (Real.log (8627683279771 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8627683279771 / 250000000000) = -Real.log (250000000000 / 8627683279771) := by
    rw [show ((8627683279771 / 250000000000) : ℝ) = ((250000000000 / 8627683279771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (355166191 / 100000000) ≤ -Real.log (500000000000 / 17435611155951) ∧
    -Real.log (500000000000 / 17435611155951) ≤ (887915479 / 250000000) := by
  have h := checkLog_sound (w := (1435611155951 / 33435611155951)) (n := 12)
    (lo := (8592601 / 100000000)) (hi := (85926011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17435611155951 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17435611155951 / 16000000000000) = 1/(500000000000 / 17435611155951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (355166191 / 100000000) (887915479 / 250000000) (Real.log (17435611155951 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17435611155951 / 500000000000) = -Real.log (500000000000 / 17435611155951) := by
    rw [show ((17435611155951 / 500000000000) : ℝ) = ((500000000000 / 17435611155951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0141
