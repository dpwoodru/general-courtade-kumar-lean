import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0317
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

theorem reflection_log_1_neg : (43987057 / 200000000) ≤ -Real.log (10240 / 12759) ∧
    -Real.log (10240 / 12759) ≤ (109967643 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 22999)) (n := 12)
    (lo := (43987057 / 200000000)) (hi := (109967643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12759 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12759 / 10240) = 1/(10240 / 12759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43987057 / 200000000) (109967643 / 500000000) (Real.log (12759 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12759 / 10240) = -Real.log (10240 / 12759) := by
    rw [show ((12759 / 10240) : ℝ) = ((10240 / 12759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28235773 / 100000000) ≤ -Real.log (7721 / 10240) ∧
    -Real.log (7721 / 10240) ≤ (282357731 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 17961)) (n := 12)
    (lo := (28235773 / 100000000)) (hi := (282357731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7721) = 1/(7721 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-282357731 / 1000000000) (-28235773 / 100000000) (Real.log (7721 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (219700129 / 1000000000) ≤ -Real.log (2560 / 3189) ∧
    -Real.log (2560 / 3189) ≤ (21970013 / 100000000) := by
  have h := checkLog_sound (w := (629 / 5749)) (n := 12)
    (lo := (219700129 / 1000000000)) (hi := (21970013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3189 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3189 / 2560) = 1/(2560 / 3189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (219700129 / 1000000000) (21970013 / 100000000) (Real.log (3189 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3189 / 2560) = -Real.log (2560 / 3189) := by
    rw [show ((3189 / 2560) : ℝ) = ((2560 / 3189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56393851 / 200000000) ≤ -Real.log (1931 / 2560) ∧
    -Real.log (1931 / 2560) ≤ (35246157 / 125000000) := by
  have h := checkLog_sound (w := (629 / 4491)) (n := 12)
    (lo := (56393851 / 200000000)) (hi := (35246157 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1931) = 1/(1931 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-35246157 / 125000000) (-56393851 / 200000000) (Real.log (1931 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (80022453 / 200000000) ≤ -Real.log (5120 / 7639) ∧
    -Real.log (5120 / 7639) ≤ (200056133 / 500000000) := by
  have h := checkLog_sound (w := (2519 / 12759)) (n := 12)
    (lo := (80022453 / 200000000)) (hi := (200056133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7639 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7639 / 5120) = 1/(5120 / 7639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (80022453 / 200000000) (200056133 / 500000000) (Real.log (7639 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7639 / 5120) = -Real.log (5120 / 7639) := by
    rw [show ((7639 / 5120) : ℝ) = ((5120 / 7639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (169314613 / 250000000) ≤ -Real.log (2601 / 5120) ∧
    -Real.log (2601 / 5120) ≤ (677258453 / 1000000000) := by
  have h := checkLog_sound (w := (2519 / 7721)) (n := 12)
    (lo := (169314613 / 250000000)) (hi := (677258453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2601) = 1/(2601 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-677258453 / 1000000000) (-169314613 / 250000000) (Real.log (2601 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199859733 / 500000000) ≤ -Real.log (1280 / 1909) ∧
    -Real.log (1280 / 1909) ≤ (399719467 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 3189)) (n := 12)
    (lo := (199859733 / 500000000)) (hi := (399719467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909 / 1280) = 1/(1280 / 1909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199859733 / 500000000) (399719467 / 1000000000) (Real.log (1909 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1909 / 1280) = -Real.log (1280 / 1909) := by
    rw [show ((1909 / 1280) : ℝ) = ((1280 / 1909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (338052857 / 500000000) ≤ -Real.log (651 / 1280) ∧
    -Real.log (651 / 1280) ≤ (135221143 / 200000000) := by
  have h := checkLog_sound (w := (629 / 1931)) (n := 12)
    (lo := (338052857 / 500000000)) (hi := (135221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 651) = 1/(651 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-135221143 / 200000000) (-338052857 / 500000000) (Real.log (651 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75280833 / 250000000) ≤ -Real.log (62500 / 84461) ∧
    -Real.log (62500 / 84461) ≤ (301123333 / 1000000000) := by
  have h := checkLog_sound (w := (21961 / 146961)) (n := 12)
    (lo := (75280833 / 250000000)) (hi := (301123333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84461 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84461 / 62500) = 1/(62500 / 84461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75280833 / 250000000) (301123333 / 1000000000) (Real.log (84461 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (84461 / 62500) = -Real.log (62500 / 84461) := by
    rw [show ((84461 / 62500) : ℝ) = ((62500 / 84461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (432902083 / 1000000000) ≤ -Real.log (40539 / 62500) ∧
    -Real.log (40539 / 62500) ≤ (108225521 / 250000000) := by
  have h := checkLog_sound (w := (21961 / 103039)) (n := 12)
    (lo := (432902083 / 1000000000)) (hi := (108225521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40539) = 1/(40539 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-108225521 / 250000000) (-432902083 / 1000000000) (Real.log (40539 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75360369 / 250000000) ≤ -Real.log (500000 / 675903) ∧
    -Real.log (500000 / 675903) ≤ (301441477 / 1000000000) := by
  have h := checkLog_sound (w := (175903 / 1175903)) (n := 12)
    (lo := (75360369 / 250000000)) (hi := (301441477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675903 / 500000) = 1/(500000 / 675903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75360369 / 250000000) (301441477 / 1000000000) (Real.log (675903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (675903 / 500000) = -Real.log (500000 / 675903) := by
    rw [show ((675903 / 500000) : ℝ) = ((500000 / 675903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (108391311 / 250000000) ≤ -Real.log (324097 / 500000) ∧
    -Real.log (324097 / 500000) ≤ (86713049 / 200000000) := by
  have h := checkLog_sound (w := (175903 / 824097)) (n := 12)
    (lo := (108391311 / 250000000)) (hi := (86713049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 324097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 324097) = 1/(324097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86713049 / 200000000) (-108391311 / 250000000) (Real.log (324097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45785041 / 200000000) ≤ -Real.log (31250 / 39289) ∧
    -Real.log (31250 / 39289) ≤ (114462603 / 500000000) := by
  have h := checkLog_sound (w := (8039 / 70539)) (n := 12)
    (lo := (45785041 / 200000000)) (hi := (114462603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39289 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39289 / 31250) = 1/(31250 / 39289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45785041 / 200000000) (114462603 / 500000000) (Real.log (39289 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (39289 / 31250) = -Real.log (31250 / 39289) := by
    rw [show ((39289 / 31250) : ℝ) = ((31250 / 39289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297393071 / 1000000000) ≤ -Real.log (23211 / 31250) ∧
    -Real.log (23211 / 31250) ≤ (18587067 / 62500000) := by
  have h := checkLog_sound (w := (8039 / 54461)) (n := 12)
    (lo := (297393071 / 1000000000)) (hi := (18587067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23211) = 1/(23211 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-18587067 / 62500000) (-297393071 / 1000000000) (Real.log (23211 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22919401 / 100000000) ≤ -Real.log (500000 / 628793) ∧
    -Real.log (500000 / 628793) ≤ (229194011 / 1000000000) := by
  have h := checkLog_sound (w := (128793 / 1128793)) (n := 12)
    (lo := (22919401 / 100000000)) (hi := (229194011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628793 / 500000) = 1/(500000 / 628793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22919401 / 100000000) (229194011 / 1000000000) (Real.log (628793 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (628793 / 500000) = -Real.log (500000 / 628793) := by
    rw [show ((628793 / 500000) : ℝ) = ((500000 / 628793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (297848239 / 1000000000) ≤ -Real.log (371207 / 500000) ∧
    -Real.log (371207 / 500000) ≤ (3723103 / 12500000) := by
  have h := checkLog_sound (w := (128793 / 871207)) (n := 12)
    (lo := (297848239 / 1000000000)) (hi := (3723103 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371207) = 1/(371207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3723103 / 12500000) (-297848239 / 1000000000) (Real.log (371207 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (146805083 / 200000000) ≤ -Real.log (250000000000 / 520862626113) ∧
    -Real.log (250000000000 / 520862626113) ≤ (734025417 / 1000000000) := by
  have h := checkLog_sound (w := (20862626113 / 1020862626113)) (n := 12)
    (lo := (8175647 / 200000000)) (hi := (10219559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((520862626113 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(520862626113 / 500000000000) = 1/(250000000000 / 520862626113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (146805083 / 200000000) (734025417 / 1000000000) (Real.log (520862626113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (520862626113 / 250000000000) = -Real.log (250000000000 / 520862626113) := by
    rw [show ((520862626113 / 250000000000) : ℝ) = ((250000000000 / 520862626113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (287112 / 390625) ≤ -Real.log (62500000000 / 130343500557) ∧
    -Real.log (62500000000 / 130343500557) ≤ (367503361 / 500000000) := by
  have h := checkLog_sound (w := (5343500557 / 255343500557)) (n := 12)
    (lo := (2092977 / 50000000)) (hi := (41859541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130343500557 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(130343500557 / 125000000000) = 1/(62500000000 / 130343500557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (287112 / 390625) (367503361 / 500000000) (Real.log (130343500557 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (130343500557 / 62500000000) = -Real.log (62500000000 / 130343500557) := by
    rw [show ((130343500557 / 62500000000) : ℝ) = ((62500000000 / 130343500557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (526318277 / 1000000000) ≤ -Real.log (500000000000 / 846344405669) ∧
    -Real.log (500000000000 / 846344405669) ≤ (263159139 / 500000000) := by
  have h := checkLog_sound (w := (346344405669 / 1346344405669)) (n := 12)
    (lo := (526318277 / 1000000000)) (hi := (263159139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846344405669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846344405669 / 500000000000) = 1/(500000000000 / 846344405669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (526318277 / 1000000000) (263159139 / 500000000) (Real.log (846344405669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (846344405669 / 500000000000) = -Real.log (500000000000 / 846344405669) := by
    rw [show ((846344405669 / 500000000000) : ℝ) = ((500000000000 / 846344405669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2108169 / 4000000) ≤ -Real.log (62500000000 / 105869669753) ∧
    -Real.log (62500000000 / 105869669753) ≤ (527042251 / 1000000000) := by
  have h := checkLog_sound (w := (43369669753 / 168369669753)) (n := 12)
    (lo := (2108169 / 4000000)) (hi := (527042251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105869669753 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105869669753 / 62500000000) = 1/(62500000000 / 105869669753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2108169 / 4000000) (527042251 / 1000000000) (Real.log (105869669753 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (105869669753 / 62500000000) = -Real.log (62500000000 / 105869669753) := by
    rw [show ((105869669753 / 62500000000) : ℝ) = ((62500000000 / 105869669753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0317
