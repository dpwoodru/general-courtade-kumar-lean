import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142
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

theorem reflection_log_1_neg : (65766167 / 100000000) ≤ -Real.log (5120 / 9883) ∧
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


theorem reflection_log_1 : Bounds (65766167 / 100000000) (657661671 / 1000000000) (Real.log (9883 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9883 / 5120) = -Real.log (5120 / 9883) := by
    rw [show ((9883 / 5120) : ℝ) = ((5120 / 9883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1331586967 / 500000000) ≤ -Real.log (357 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-1331586969 / 500000000) (-1331586967 / 500000000) (Real.log (357 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (657277097 / 1000000000) ≤ -Real.log (6400 / 12349) ∧
    -Real.log (6400 / 12349) ≤ (328638549 / 500000000) := by
  have h := checkLog_sound (w := (5949 / 18749)) (n := 12)
    (lo := (657277097 / 1000000000)) (hi := (328638549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12349 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12349 / 6400) = 1/(6400 / 12349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (657277097 / 1000000000) (328638549 / 500000000) (Real.log (12349 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12349 / 6400) = -Real.log (6400 / 12349) := by
    rw [show ((12349 / 6400) : ℝ) = ((6400 / 12349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (331573241 / 125000000) ≤ -Real.log (451 / 6400) ∧
    -Real.log (451 / 6400) ≤ (663146483 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 451) = 1/(451 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-663146483 / 250000000) (-331573241 / 125000000) (Real.log (451 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (620870463 / 1000000000) ≤ -Real.log (2560 / 4763) ∧
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


theorem reflection_log_5 : Bounds (620870463 / 1000000000) (9701101 / 15625000) (Real.log (4763 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4763 / 2560) = -Real.log (2560 / 4763) := by
    rw [show ((4763 / 2560) : ℝ) = ((2560 / 4763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (985013377 / 500000000) ≤ -Real.log (357 / 2560) ∧
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


theorem reflection_log_6 : Bounds (-1970026757 / 1000000000) (-985013377 / 500000000) (Real.log (357 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77509041 / 125000000) ≤ -Real.log (3200 / 5949) ∧
    -Real.log (3200 / 5949) ≤ (620072329 / 1000000000) := by
  have h := checkLog_sound (w := (2749 / 9149)) (n := 12)
    (lo := (77509041 / 125000000)) (hi := (620072329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949 / 3200) = 1/(3200 / 5949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77509041 / 125000000) (620072329 / 1000000000) (Real.log (5949 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5949 / 3200) = -Real.log (3200 / 5949) := by
    rw [show ((5949 / 3200) : ℝ) = ((3200 / 5949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (489859687 / 250000000) ≤ -Real.log (451 / 3200) ∧
    -Real.log (451 / 3200) ≤ (1959438751 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 451) = 1/(451 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1959438751 / 1000000000) (-489859687 / 250000000) (Real.log (451 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (664833093 / 1000000000) ≤ -Real.log (500000 / 972083) ∧
    -Real.log (500000 / 972083) ≤ (332416547 / 500000000) := by
  have h := checkLog_sound (w := (472083 / 1472083)) (n := 12)
    (lo := (664833093 / 1000000000)) (hi := (332416547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972083 / 500000) = 1/(500000 / 972083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (664833093 / 1000000000) (332416547 / 500000000) (Real.log (972083 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (972083 / 500000) = -Real.log (500000 / 972083) := by
    rw [show ((972083 / 500000) : ℝ) = ((500000 / 972083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2885372273 / 1000000000) ≤ -Real.log (27917 / 500000) ∧
    -Real.log (27917 / 500000) ≤ (1442686139 / 500000000) := by
  have h := checkLog_sound (w := (3333 / 59167)) (n := 12)
    (lo := (112783553 / 1000000000)) (hi := (56391777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27917) = 1/(27917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1442686139 / 500000000) (-2885372273 / 1000000000) (Real.log (27917 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83138851 / 125000000) ≤ -Real.log (500000 / 972353) ∧
    -Real.log (500000 / 972353) ≤ (665110809 / 1000000000) := by
  have h := checkLog_sound (w := (472353 / 1472353)) (n := 12)
    (lo := (83138851 / 125000000)) (hi := (665110809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972353 / 500000) = 1/(500000 / 972353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83138851 / 125000000) (665110809 / 1000000000) (Real.log (972353 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (972353 / 500000) = -Real.log (500000 / 972353) := by
    rw [show ((972353 / 500000) : ℝ) = ((500000 / 972353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2895090873 / 1000000000) ≤ -Real.log (27647 / 500000) ∧
    -Real.log (27647 / 500000) ≤ (1447545439 / 500000000) := by
  have h := checkLog_sound (w := (3603 / 58897)) (n := 12)
    (lo := (122502153 / 1000000000)) (hi := (61251077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27647) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27647) = 1/(27647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1447545439 / 500000000) (-2895090873 / 1000000000) (Real.log (27647 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (259489 / 390625) ≤ -Real.log (500000 / 971557) ∧
    -Real.log (500000 / 971557) ≤ (664291841 / 1000000000) := by
  have h := checkLog_sound (w := (471557 / 1471557)) (n := 12)
    (lo := (259489 / 390625)) (hi := (664291841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971557 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971557 / 500000) = 1/(500000 / 971557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (259489 / 390625) (664291841 / 1000000000) (Real.log (971557 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (971557 / 500000) = -Real.log (500000 / 971557) := by
    rw [show ((971557 / 500000) : ℝ) = ((500000 / 971557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2866706011 / 1000000000) ≤ -Real.log (28443 / 500000) ∧
    -Real.log (28443 / 500000) ≤ (89584563 / 31250000) := by
  have h := checkLog_sound (w := (2807 / 59693)) (n := 12)
    (lo := (94117291 / 1000000000)) (hi := (23529323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 28443) = 1/(28443 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89584563 / 31250000) (-2866706011 / 1000000000) (Real.log (28443 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (664583083 / 1000000000) ≤ -Real.log (3125 / 6074) ∧
    -Real.log (3125 / 6074) ≤ (166145771 / 250000000) := by
  have h := checkLog_sound (w := (2949 / 9199)) (n := 12)
    (lo := (664583083 / 1000000000)) (hi := (166145771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6074 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6074 / 3125) = 1/(3125 / 6074) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (664583083 / 1000000000) (166145771 / 250000000) (Real.log (6074 / 3125)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6074 / 3125) = -Real.log (3125 / 6074) := by
    rw [show ((6074 / 3125) : ℝ) = ((3125 / 6074) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (719176391 / 250000000) ≤ -Real.log (176 / 3125) ∧
    -Real.log (176 / 3125) ≤ (2876705569 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 5941)) (n := 12)
    (lo := (26029211 / 250000000)) (hi := (20823369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2816) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2816) = 1/(176 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2876705569 / 1000000000) (-719176391 / 250000000) (Real.log (176 / 3125)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1775102683 / 500000000) ≤ -Real.log (250000000000 / 8705116953827) ∧
    -Real.log (250000000000 / 8705116953827) ≤ (887551343 / 250000000) := by
  have h := checkLog_sound (w := (705116953827 / 16705116953827)) (n := 12)
    (lo := (42234733 / 500000000)) (hi := (84469467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8705116953827 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8705116953827 / 8000000000000) = 1/(250000000000 / 8705116953827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1775102683 / 500000000) (887551343 / 250000000) (Real.log (8705116953827 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8705116953827 / 250000000000) = -Real.log (250000000000 / 8705116953827) := by
    rw [show ((8705116953827 / 250000000000) : ℝ) = ((250000000000 / 8705116953827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3560201681 / 1000000000) ≤ -Real.log (500000000000 / 17585144862011) ∧
    -Real.log (500000000000 / 17585144862011) ≤ (3560201687 / 1000000000) := by
  have h := checkLog_sound (w := (1585144862011 / 33585144862011)) (n := 12)
    (lo := (94465781 / 1000000000)) (hi := (47232891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17585144862011 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17585144862011 / 16000000000000) = 1/(500000000000 / 17585144862011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3560201681 / 1000000000) (3560201687 / 1000000000) (Real.log (17585144862011 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17585144862011 / 500000000000) = -Real.log (500000000000 / 17585144862011) := by
    rw [show ((17585144862011 / 500000000000) : ℝ) = ((500000000000 / 17585144862011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3530997851 / 1000000000) ≤ -Real.log (500000000000 / 17079017684491) ∧
    -Real.log (500000000000 / 17079017684491) ≤ (3530997857 / 1000000000) := by
  have h := checkLog_sound (w := (1079017684491 / 33079017684491)) (n := 12)
    (lo := (65261951 / 1000000000)) (hi := (509859 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17079017684491 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17079017684491 / 16000000000000) = 1/(500000000000 / 17079017684491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3530997851 / 1000000000) (3530997857 / 1000000000) (Real.log (17079017684491 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (17079017684491 / 500000000000) = -Real.log (500000000000 / 17079017684491) := by
    rw [show ((17079017684491 / 500000000000) : ℝ) = ((500000000000 / 17079017684491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3541288647 / 1000000000) ≤ -Real.log (250000000000 / 8627840909091) ∧
    -Real.log (250000000000 / 8627840909091) ≤ (3541288653 / 1000000000) := by
  have h := checkLog_sound (w := (627840909091 / 16627840909091)) (n := 12)
    (lo := (75552747 / 1000000000)) (hi := (18888187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8627840909091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8627840909091 / 8000000000000) = 1/(250000000000 / 8627840909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3541288647 / 1000000000) (3541288653 / 1000000000) (Real.log (8627840909091 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8627840909091 / 250000000000) = -Real.log (250000000000 / 8627840909091) := by
    rw [show ((8627840909091 / 250000000000) : ℝ) = ((250000000000 / 8627840909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0142
