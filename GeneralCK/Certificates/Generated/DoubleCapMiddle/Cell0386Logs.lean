import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0386
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

theorem reflection_log_1_neg : (40715679 / 200000000) ≤ -Real.log (1280 / 1569) ∧
    -Real.log (1280 / 1569) ≤ (50894599 / 250000000) := by
  have h := checkLog_sound (w := (289 / 2849)) (n := 12)
    (lo := (40715679 / 200000000)) (hi := (50894599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1280) = 1/(1280 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40715679 / 200000000) (50894599 / 250000000) (Real.log (1569 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1569 / 1280) = -Real.log (1280 / 1569) := by
    rw [show ((1569 / 1280) : ℝ) = ((1280 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (127950411 / 500000000) ≤ -Real.log (991 / 1280) ∧
    -Real.log (991 / 1280) ≤ (255900823 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2271)) (n := 12)
    (lo := (127950411 / 500000000)) (hi := (255900823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 991) = 1/(991 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255900823 / 1000000000) (-127950411 / 500000000) (Real.log (991 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (203339361 / 1000000000) ≤ -Real.log (10240 / 12549) ∧
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


theorem reflection_log_3 : Bounds (203339361 / 1000000000) (101669681 / 500000000) (Real.log (12549 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12549 / 10240) = -Real.log (10240 / 12549) := by
    rw [show ((12549 / 10240) : ℝ) = ((10240 / 12549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31940311 / 125000000) ≤ -Real.log (7931 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-255522489 / 1000000000) (-31940311 / 125000000) (Real.log (7931 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186320281 / 500000000) ≤ -Real.log (640 / 929) ∧
    -Real.log (640 / 929) ≤ (372640563 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1569)) (n := 12)
    (lo := (186320281 / 500000000)) (hi := (372640563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929 / 640) = 1/(640 / 929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186320281 / 500000000) (372640563 / 1000000000) (Real.log (929 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (929 / 640) = -Real.log (640 / 929) := by
    rw [show ((929 / 640) : ℝ) = ((640 / 929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (18771311 / 31250000) ≤ -Real.log (351 / 640) ∧
    -Real.log (351 / 640) ≤ (600681953 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 351) = 1/(351 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-600681953 / 1000000000) (-18771311 / 31250000) (Real.log (351 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (372236821 / 1000000000) ≤ -Real.log (5120 / 7429) ∧
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


theorem reflection_log_7 : Bounds (372236821 / 1000000000) (186118411 / 500000000) (Real.log (7429 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7429 / 5120) = -Real.log (5120 / 7429) := by
    rw [show ((7429 / 5120) : ℝ) = ((5120 / 7429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (599614147 / 1000000000) ≤ -Real.log (2811 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-149903537 / 250000000) (-599614147 / 1000000000) (Real.log (2811 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27903 / 100000) ≤ -Real.log (1000000 / 1321847) ∧
    -Real.log (1000000 / 1321847) ≤ (279030001 / 1000000000) := by
  have h := checkLog_sound (w := (321847 / 2321847)) (n := 12)
    (lo := (27903 / 100000)) (hi := (279030001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321847 / 1000000) = 1/(1000000 / 1321847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27903 / 100000) (279030001 / 1000000000) (Real.log (1321847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1321847 / 1000000) = -Real.log (1000000 / 1321847) := by
    rw [show ((1321847 / 1000000) : ℝ) = ((1000000 / 1321847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24273897 / 62500000) ≤ -Real.log (678153 / 1000000) ∧
    -Real.log (678153 / 1000000) ≤ (388382353 / 1000000000) := by
  have h := checkLog_sound (w := (321847 / 1678153)) (n := 12)
    (lo := (24273897 / 62500000)) (hi := (388382353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 678153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 678153) = 1/(678153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-388382353 / 1000000000) (-24273897 / 62500000) (Real.log (678153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (279352981 / 1000000000) ≤ -Real.log (500000 / 661137) ∧
    -Real.log (500000 / 661137) ≤ (139676491 / 500000000) := by
  have h := checkLog_sound (w := (161137 / 1161137)) (n := 12)
    (lo := (279352981 / 1000000000)) (hi := (139676491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661137 / 500000) = 1/(500000 / 661137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (279352981 / 1000000000) (139676491 / 500000000) (Real.log (661137 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (661137 / 500000) = -Real.log (500000 / 661137) := by
    rw [show ((661137 / 500000) : ℝ) = ((500000 / 661137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (194506101 / 500000000) ≤ -Real.log (338863 / 500000) ∧
    -Real.log (338863 / 500000) ≤ (389012203 / 1000000000) := by
  have h := checkLog_sound (w := (161137 / 838863)) (n := 12)
    (lo := (194506101 / 500000000)) (hi := (389012203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 338863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 338863) = 1/(338863 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-389012203 / 1000000000) (-194506101 / 500000000) (Real.log (338863 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210502387 / 1000000000) ≤ -Real.log (500000 / 617149) ∧
    -Real.log (500000 / 617149) ≤ (52625597 / 250000000) := by
  have h := checkLog_sound (w := (117149 / 1117149)) (n := 12)
    (lo := (210502387 / 1000000000)) (hi := (52625597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617149 / 500000) = 1/(500000 / 617149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210502387 / 1000000000) (52625597 / 250000000) (Real.log (617149 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (617149 / 500000) = -Real.log (500000 / 617149) := by
    rw [show ((617149 / 500000) : ℝ) = ((500000 / 617149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133481109 / 500000000) ≤ -Real.log (382851 / 500000) ∧
    -Real.log (382851 / 500000) ≤ (266962219 / 1000000000) := by
  have h := checkLog_sound (w := (117149 / 882851)) (n := 12)
    (lo := (133481109 / 500000000)) (hi := (266962219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382851) = 1/(382851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-266962219 / 1000000000) (-133481109 / 500000000) (Real.log (382851 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21076971 / 100000000) ≤ -Real.log (250000 / 308657) ∧
    -Real.log (250000 / 308657) ≤ (210769711 / 1000000000) := by
  have h := checkLog_sound (w := (58657 / 558657)) (n := 12)
    (lo := (21076971 / 100000000)) (hi := (210769711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308657 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308657 / 250000) = 1/(250000 / 308657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21076971 / 100000000) (210769711 / 1000000000) (Real.log (308657 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (308657 / 250000) = -Real.log (250000 / 308657) := by
    rw [show ((308657 / 250000) : ℝ) = ((250000 / 308657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33424161 / 125000000) ≤ -Real.log (191343 / 250000) ∧
    -Real.log (191343 / 250000) ≤ (267393289 / 1000000000) := by
  have h := checkLog_sound (w := (58657 / 441343)) (n := 12)
    (lo := (33424161 / 125000000)) (hi := (267393289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191343) = 1/(191343 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-267393289 / 1000000000) (-33424161 / 125000000) (Real.log (191343 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (667412353 / 1000000000) ≤ -Real.log (500000000000 / 974593491439) ∧
    -Real.log (500000000000 / 974593491439) ≤ (333706177 / 500000000) := by
  have h := checkLog_sound (w := (474593491439 / 1474593491439)) (n := 12)
    (lo := (667412353 / 1000000000)) (hi := (333706177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974593491439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974593491439 / 500000000000) = 1/(500000000000 / 974593491439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (667412353 / 1000000000) (333706177 / 500000000) (Real.log (974593491439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (974593491439 / 500000000000) = -Real.log (500000000000 / 974593491439) := by
    rw [show ((974593491439 / 500000000000) : ℝ) = ((500000000000 / 974593491439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5221603 / 7812500) ≤ -Real.log (250000000000 / 487761278157) ∧
    -Real.log (250000000000 / 487761278157) ≤ (133673037 / 200000000) := by
  have h := checkLog_sound (w := (237761278157 / 737761278157)) (n := 12)
    (lo := (5221603 / 7812500)) (hi := (133673037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487761278157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487761278157 / 250000000000) = 1/(250000000000 / 487761278157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5221603 / 7812500) (133673037 / 200000000) (Real.log (487761278157 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (487761278157 / 250000000000) = -Real.log (250000000000 / 487761278157) := by
    rw [show ((487761278157 / 250000000000) : ℝ) = ((250000000000 / 487761278157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (238732303 / 500000000) ≤ -Real.log (125000000000 / 201497775897) ∧
    -Real.log (125000000000 / 201497775897) ≤ (477464607 / 1000000000) := by
  have h := checkLog_sound (w := (76497775897 / 326497775897)) (n := 12)
    (lo := (238732303 / 500000000)) (hi := (477464607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201497775897 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201497775897 / 125000000000) = 1/(125000000000 / 201497775897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (238732303 / 500000000) (477464607 / 1000000000) (Real.log (201497775897 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (201497775897 / 125000000000) = -Real.log (125000000000 / 201497775897) := by
    rw [show ((201497775897 / 125000000000) : ℝ) = ((125000000000 / 201497775897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (239081499 / 500000000) ≤ -Real.log (250000000000 / 403277099241) ∧
    -Real.log (250000000000 / 403277099241) ≤ (478162999 / 1000000000) := by
  have h := checkLog_sound (w := (153277099241 / 653277099241)) (n := 12)
    (lo := (239081499 / 500000000)) (hi := (478162999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403277099241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403277099241 / 250000000000) = 1/(250000000000 / 403277099241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (239081499 / 500000000) (478162999 / 1000000000) (Real.log (403277099241 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (403277099241 / 250000000000) = -Real.log (250000000000 / 403277099241) := by
    rw [show ((403277099241 / 250000000000) : ℝ) = ((250000000000 / 403277099241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0386
