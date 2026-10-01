import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0387
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

theorem reflection_log_1_neg : (203339361 / 1000000000) ≤ -Real.log (10240 / 12549) ∧
    -Real.log (10240 / 12549) ≤ (101669681 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 22789)) (n := 12)
    (lo := (203339361 / 1000000000)) (hi := (101669681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12549 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12549 / 10240) = 1/(10240 / 12549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (203339361 / 1000000000) (101669681 / 500000000) (Real.log (12549 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12549 / 10240) = -Real.log (10240 / 12549) := by
    rw [show ((12549 / 10240) : ℝ) = ((10240 / 12549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31940311 / 125000000) ≤ -Real.log (7931 / 10240) ∧
    -Real.log (7931 / 10240) ≤ (255522489 / 1000000000) := by
  have h := checkLog_sound (w := (2309 / 18171)) (n := 12)
    (lo := (31940311 / 125000000)) (hi := (255522489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7931) = 1/(7931 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255522489 / 1000000000) (-31940311 / 125000000) (Real.log (7931 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20310027 / 100000000) ≤ -Real.log (5120 / 6273) ∧
    -Real.log (5120 / 6273) ≤ (203100271 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 11393)) (n := 12)
    (lo := (20310027 / 100000000)) (hi := (203100271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6273 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6273 / 5120) = 1/(5120 / 6273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20310027 / 100000000) (203100271 / 1000000000) (Real.log (6273 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6273 / 5120) = -Real.log (5120 / 6273) := by
    rw [show ((6273 / 5120) : ℝ) = ((5120 / 6273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (255144297 / 1000000000) ≤ -Real.log (3967 / 5120) ∧
    -Real.log (3967 / 5120) ≤ (127572149 / 500000000) := by
  have h := checkLog_sound (w := (1153 / 9087)) (n := 12)
    (lo := (255144297 / 1000000000)) (hi := (127572149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3967) = 1/(3967 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127572149 / 500000000) (-255144297 / 1000000000) (Real.log (3967 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (372236821 / 1000000000) ≤ -Real.log (5120 / 7429) ∧
    -Real.log (5120 / 7429) ≤ (186118411 / 500000000) := by
  have h := checkLog_sound (w := (2309 / 12549)) (n := 12)
    (lo := (372236821 / 1000000000)) (hi := (186118411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7429 / 5120) = 1/(5120 / 7429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (372236821 / 1000000000) (186118411 / 500000000) (Real.log (7429 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7429 / 5120) = -Real.log (5120 / 7429) := by
    rw [show ((7429 / 5120) : ℝ) = ((5120 / 7429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (599614147 / 1000000000) ≤ -Real.log (2811 / 5120) ∧
    -Real.log (2811 / 5120) ≤ (149903537 / 250000000) := by
  have h := checkLog_sound (w := (2309 / 7931)) (n := 12)
    (lo := (599614147 / 1000000000)) (hi := (149903537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2811) = 1/(2811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149903537 / 250000000) (-599614147 / 1000000000) (Real.log (2811 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92958229 / 250000000) ≤ -Real.log (2560 / 3713) ∧
    -Real.log (2560 / 3713) ≤ (371832917 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 6273)) (n := 12)
    (lo := (92958229 / 250000000)) (hi := (371832917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3713 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3713 / 2560) = 1/(2560 / 3713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92958229 / 250000000) (371832917 / 1000000000) (Real.log (3713 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3713 / 2560) = -Real.log (2560 / 3713) := by
    rw [show ((3713 / 2560) : ℝ) = ((2560 / 3713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14963687 / 25000000) ≤ -Real.log (1407 / 2560) ∧
    -Real.log (1407 / 2560) ≤ (598547481 / 1000000000) := by
  have h := checkLog_sound (w := (1153 / 3967)) (n := 12)
    (lo := (14963687 / 25000000)) (hi := (598547481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1407) = 1/(1407 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-598547481 / 1000000000) (-14963687 / 25000000) (Real.log (1407 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (55741383 / 200000000) ≤ -Real.log (50000 / 66071) ∧
    -Real.log (50000 / 66071) ≤ (69676729 / 250000000) := by
  have h := checkLog_sound (w := (16071 / 116071)) (n := 12)
    (lo := (55741383 / 200000000)) (hi := (69676729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66071 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66071 / 50000) = 1/(50000 / 66071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (55741383 / 200000000) (69676729 / 250000000) (Real.log (66071 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66071 / 50000) = -Real.log (50000 / 66071) := by
    rw [show ((66071 / 50000) : ℝ) = ((50000 / 66071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (387752899 / 1000000000) ≤ -Real.log (33929 / 50000) ∧
    -Real.log (33929 / 50000) ≤ (3877529 / 10000000) := by
  have h := checkLog_sound (w := (16071 / 83929)) (n := 12)
    (lo := (387752899 / 1000000000)) (hi := (3877529 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33929) = 1/(33929 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3877529 / 10000000) (-387752899 / 1000000000) (Real.log (33929 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (279030757 / 1000000000) ≤ -Real.log (125000 / 165231) ∧
    -Real.log (125000 / 165231) ≤ (139515379 / 500000000) := by
  have h := checkLog_sound (w := (40231 / 290231)) (n := 12)
    (lo := (279030757 / 1000000000)) (hi := (139515379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165231 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165231 / 125000) = 1/(125000 / 165231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (279030757 / 1000000000) (139515379 / 500000000) (Real.log (165231 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165231 / 125000) = -Real.log (125000 / 165231) := by
    rw [show ((165231 / 125000) : ℝ) = ((125000 / 165231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (388383827 / 1000000000) ≤ -Real.log (84769 / 125000) ∧
    -Real.log (84769 / 125000) ≤ (97095957 / 250000000) := by
  have h := checkLog_sound (w := (40231 / 209769)) (n := 12)
    (lo := (388383827 / 1000000000)) (hi := (97095957 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84769) = 1/(84769 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-97095957 / 250000000) (-388383827 / 1000000000) (Real.log (84769 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210235803 / 1000000000) ≤ -Real.log (1000000 / 1233969) ∧
    -Real.log (1000000 / 1233969) ≤ (52558951 / 250000000) := by
  have h := checkLog_sound (w := (233969 / 2233969)) (n := 12)
    (lo := (210235803 / 1000000000)) (hi := (52558951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233969 / 1000000) = 1/(1000000 / 1233969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210235803 / 1000000000) (52558951 / 250000000) (Real.log (1233969 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1233969 / 1000000) = -Real.log (1000000 / 1233969) := by
    rw [show ((1233969 / 1000000) : ℝ) = ((1000000 / 1233969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1665829 / 6250000) ≤ -Real.log (766031 / 1000000) ∧
    -Real.log (766031 / 1000000) ≤ (266532641 / 1000000000) := by
  have h := checkLog_sound (w := (233969 / 1766031)) (n := 12)
    (lo := (1665829 / 6250000)) (hi := (266532641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766031) = 1/(766031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-266532641 / 1000000000) (-1665829 / 6250000) (Real.log (766031 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (210503197 / 1000000000) ≤ -Real.log (1000000 / 1234299) ∧
    -Real.log (1000000 / 1234299) ≤ (105251599 / 500000000) := by
  have h := checkLog_sound (w := (234299 / 2234299)) (n := 12)
    (lo := (210503197 / 1000000000)) (hi := (105251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234299 / 1000000) = 1/(1000000 / 1234299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (210503197 / 1000000000) (105251599 / 500000000) (Real.log (1234299 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1234299 / 1000000) = -Real.log (1000000 / 1234299) := by
    rw [show ((1234299 / 1000000) : ℝ) = ((1000000 / 1234299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66740881 / 250000000) ≤ -Real.log (765701 / 1000000) ∧
    -Real.log (765701 / 1000000) ≤ (10678541 / 40000000) := by
  have h := checkLog_sound (w := (234299 / 1765701)) (n := 12)
    (lo := (66740881 / 250000000)) (hi := (10678541 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765701) = 1/(765701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-10678541 / 40000000) (-66740881 / 250000000) (Real.log (765701 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (133291963 / 200000000) ≤ -Real.log (500000000000 / 973665595803) ∧
    -Real.log (500000000000 / 973665595803) ≤ (83307477 / 125000000) := by
  have h := checkLog_sound (w := (473665595803 / 1473665595803)) (n := 12)
    (lo := (133291963 / 200000000)) (hi := (83307477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973665595803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973665595803 / 500000000000) = 1/(500000000000 / 973665595803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (133291963 / 200000000) (83307477 / 125000000) (Real.log (973665595803 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (973665595803 / 500000000000) = -Real.log (500000000000 / 973665595803) := by
    rw [show ((973665595803 / 500000000000) : ℝ) = ((500000000000 / 973665595803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (83426823 / 125000000) ≤ -Real.log (500000000000 / 974595665869) ∧
    -Real.log (500000000000 / 974595665869) ≤ (133482917 / 200000000) := by
  have h := checkLog_sound (w := (474595665869 / 1474595665869)) (n := 12)
    (lo := (83426823 / 125000000)) (hi := (133482917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974595665869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974595665869 / 500000000000) = 1/(500000000000 / 974595665869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (83426823 / 125000000) (133482917 / 200000000) (Real.log (974595665869 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (974595665869 / 500000000000) = -Real.log (500000000000 / 974595665869) := by
    rw [show ((974595665869 / 500000000000) : ℝ) = ((500000000000 / 974595665869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (476768443 / 1000000000) ≤ -Real.log (250000000000 / 402715098997) ∧
    -Real.log (250000000000 / 402715098997) ≤ (119192111 / 250000000) := by
  have h := checkLog_sound (w := (152715098997 / 652715098997)) (n := 12)
    (lo := (476768443 / 1000000000)) (hi := (119192111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402715098997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402715098997 / 250000000000) = 1/(250000000000 / 402715098997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (476768443 / 1000000000) (119192111 / 250000000) (Real.log (402715098997 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (402715098997 / 250000000000) = -Real.log (250000000000 / 402715098997) := by
    rw [show ((402715098997 / 250000000000) : ℝ) = ((250000000000 / 402715098997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (238733361 / 500000000) ≤ -Real.log (125000000000 / 201498202301) ∧
    -Real.log (125000000000 / 201498202301) ≤ (477466723 / 1000000000) := by
  have h := checkLog_sound (w := (76498202301 / 326498202301)) (n := 12)
    (lo := (238733361 / 500000000)) (hi := (477466723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201498202301 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201498202301 / 125000000000) = 1/(125000000000 / 201498202301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (238733361 / 500000000) (477466723 / 1000000000) (Real.log (201498202301 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (201498202301 / 125000000000) = -Real.log (125000000000 / 201498202301) := by
    rw [show ((201498202301 / 125000000000) : ℝ) = ((125000000000 / 201498202301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0387
