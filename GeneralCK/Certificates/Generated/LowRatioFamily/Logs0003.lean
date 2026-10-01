import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_192_neg : (82142597 / 500000000) ≤ -Real.log (1697 / 2000) ∧
    -Real.log (1697 / 2000) ≤ (32857039 / 200000000) := by
  have h := checkLog_sound (w := (303 / 3697)) (n := 12)
    (lo := (82142597 / 500000000)) (hi := (32857039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1697) = 1/(1697 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_192 : Bounds (-32857039 / 200000000) (-82142597 / 500000000) (Real.log (1697 / 2000)) := by
  have h := reflection_log_192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_193_neg : (2367 / 15625000) ≤ -Real.log (2000000 / 2000303) ∧
    -Real.log (2000000 / 2000303) ≤ (151489 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 4000303)) (n := 12)
    (lo := (2367 / 15625000)) (hi := (151489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000303 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000303 / 2000000) = 1/(2000000 / 2000303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_193 : Bounds (2367 / 15625000) (151489 / 1000000000) (Real.log (2000303 / 2000000)) := by
  have h := reflection_log_193_neg
  have he : Real.log (2000303 / 2000000) = -Real.log (2000000 / 2000303) := by
    rw [show ((2000303 / 2000000) : ℝ) = ((2000000 / 2000303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_194_neg : (151511 / 1000000000) ≤ -Real.log (1999697 / 2000000) ∧
    -Real.log (1999697 / 2000000) ≤ (18939 / 125000000) := by
  have h := checkLog_sound (w := (303 / 3999697)) (n := 12)
    (lo := (151511 / 1000000000)) (hi := (18939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999697) = 1/(1999697 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_194 : Bounds (-18939 / 125000000) (-151511 / 1000000000) (Real.log (1999697 / 2000000)) := by
  have h := reflection_log_194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_195_neg : (73382423 / 1000000000) ≤ -Real.log (500000 / 538071) ∧
    -Real.log (500000 / 538071) ≤ (9172803 / 125000000) := by
  have h := checkLog_sound (w := (38071 / 1038071)) (n := 12)
    (lo := (73382423 / 1000000000)) (hi := (9172803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538071 / 500000) = 1/(500000 / 538071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_195 : Bounds (73382423 / 1000000000) (9172803 / 125000000) (Real.log (538071 / 500000)) := by
  have h := reflection_log_195_neg
  have he : Real.log (538071 / 500000) = -Real.log (500000 / 538071) := by
    rw [show ((538071 / 500000) : ℝ) = ((500000 / 538071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_196_neg : (39598449 / 500000000) ≤ -Real.log (461929 / 500000) ∧
    -Real.log (461929 / 500000) ≤ (79196899 / 1000000000) := by
  have h := checkLog_sound (w := (38071 / 961929)) (n := 12)
    (lo := (39598449 / 500000000)) (hi := (79196899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461929) = 1/(461929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_196 : Bounds (-79196899 / 1000000000) (-39598449 / 500000000) (Real.log (461929 / 500000)) := by
  have h := reflection_log_196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_197_neg : (232579 / 40000000) ≤ -Real.log (248550598959 / 250000000000) ∧
    -Real.log (248550598959 / 250000000000) ≤ (1453619 / 250000000) := by
  have h := checkLog_sound (w := (1449401041 / 498550598959)) (n := 12)
    (lo := (232579 / 40000000)) (hi := (1453619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248550598959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248550598959) = 1/(248550598959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_197 : Bounds (-1453619 / 250000000) (-232579 / 40000000) (Real.log (248550598959 / 250000000000)) := by
  have h := reflection_log_197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_198_neg : (1902137 / 12500000) ≤ -Real.log (100000000000 / 116435927931) ∧
    -Real.log (100000000000 / 116435927931) ≤ (152170961 / 1000000000) := by
  have h := checkLog_sound (w := (16435927931 / 216435927931)) (n := 12)
    (lo := (1902137 / 12500000)) (hi := (152170961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116435927931 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116435927931 / 100000000000) = 1/(100000000000 / 116435927931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_198 : Bounds (1902137 / 12500000) (152170961 / 1000000000) (Real.log (116435927931 / 100000000000)) := by
  have h := reflection_log_198_neg
  have he : Real.log (116435927931 / 100000000000) = -Real.log (100000000000 / 116435927931) := by
    rw [show ((116435927931 / 100000000000) : ℝ) = ((100000000000 / 116435927931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_199_neg : (76289661 / 500000000) ≤ -Real.log (500000000000 / 582417427787) ∧
    -Real.log (500000000000 / 582417427787) ≤ (152579323 / 1000000000) := by
  have h := checkLog_sound (w := (82417427787 / 1082417427787)) (n := 12)
    (lo := (76289661 / 500000000)) (hi := (152579323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582417427787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582417427787 / 500000000000) = 1/(500000000000 / 582417427787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_199 : Bounds (76289661 / 500000000) (152579323 / 1000000000) (Real.log (582417427787 / 500000000000)) := by
  have h := reflection_log_199_neg
  have he : Real.log (582417427787 / 500000000000) = -Real.log (500000000000 / 582417427787) := by
    rw [show ((582417427787 / 500000000000) : ℝ) = ((500000000000 / 582417427787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_200_neg : (305145939 / 1000000000) ≤ -Real.log (31250000000 / 42400718831) ∧
    -Real.log (31250000000 / 42400718831) ≤ (15257297 / 50000000) := by
  have h := checkLog_sound (w := (11150718831 / 73650718831)) (n := 12)
    (lo := (305145939 / 1000000000)) (hi := (15257297 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42400718831 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42400718831 / 31250000000) = 1/(31250000000 / 42400718831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_200 : Bounds (305145939 / 1000000000) (15257297 / 50000000) (Real.log (42400718831 / 31250000000)) := by
  have h := reflection_log_200_neg
  have he : Real.log (42400718831 / 31250000000) = -Real.log (31250000000 / 42400718831) := by
    rw [show ((42400718831 / 31250000000) : ℝ) = ((31250000000 / 42400718831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_201_neg : (152675317 / 500000000) ≤ -Real.log (500000000000 / 678550383029) ∧
    -Real.log (500000000000 / 678550383029) ≤ (61070127 / 200000000) := by
  have h := checkLog_sound (w := (178550383029 / 1178550383029)) (n := 12)
    (lo := (152675317 / 500000000)) (hi := (61070127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678550383029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678550383029 / 500000000000) = 1/(500000000000 / 678550383029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_201 : Bounds (152675317 / 500000000) (61070127 / 200000000) (Real.log (678550383029 / 500000000000)) := by
  have h := reflection_log_201_neg
  have he : Real.log (678550383029 / 500000000000) = -Real.log (500000000000 / 678550383029) := by
    rw [show ((678550383029 / 500000000000) : ℝ) = ((500000000000 / 678550383029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_202_neg : (141152279 / 1000000000) ≤ -Real.log (2500 / 2879) ∧
    -Real.log (2500 / 2879) ≤ (3528807 / 25000000) := by
  have h := checkLog_sound (w := (379 / 5379)) (n := 12)
    (lo := (141152279 / 1000000000)) (hi := (3528807 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2879 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2879 / 2500) = 1/(2500 / 2879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_202 : Bounds (141152279 / 1000000000) (3528807 / 25000000) (Real.log (2879 / 2500)) := by
  have h := reflection_log_202_neg
  have he : Real.log (2879 / 2500) = -Real.log (2500 / 2879) := by
    rw [show ((2879 / 2500) : ℝ) = ((2500 / 2879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_203_neg : (10275191 / 62500000) ≤ -Real.log (2121 / 2500) ∧
    -Real.log (2121 / 2500) ≤ (164403057 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 4621)) (n := 12)
    (lo := (10275191 / 62500000)) (hi := (164403057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2121) = 1/(2121 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_203 : Bounds (-164403057 / 1000000000) (-10275191 / 62500000) (Real.log (2121 / 2500)) := by
  have h := reflection_log_203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_204_neg : (37897 / 250000000) ≤ -Real.log (2500000 / 2500379) ∧
    -Real.log (2500000 / 2500379) ≤ (151589 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 5000379)) (n := 12)
    (lo := (37897 / 250000000)) (hi := (151589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500379 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500379 / 2500000) = 1/(2500000 / 2500379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_204 : Bounds (37897 / 250000000) (151589 / 1000000000) (Real.log (2500379 / 2500000)) := by
  have h := reflection_log_204_neg
  have he : Real.log (2500379 / 2500000) = -Real.log (2500000 / 2500379) := by
    rw [show ((2500379 / 2500000) : ℝ) = ((2500000 / 2500379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_205_neg : (151611 / 1000000000) ≤ -Real.log (2499621 / 2500000) ∧
    -Real.log (2499621 / 2500000) ≤ (37903 / 250000000) := by
  have h := checkLog_sound (w := (379 / 4999621)) (n := 12)
    (lo := (151611 / 1000000000)) (hi := (37903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499621) = 1/(2499621 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_205 : Bounds (-37903 / 250000000) (-151611 / 1000000000) (Real.log (2499621 / 2500000)) := by
  have h := reflection_log_205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_206_neg : (18357221 / 250000000) ≤ -Real.log (31250 / 33631) ∧
    -Real.log (31250 / 33631) ≤ (14685777 / 200000000) := by
  have h := checkLog_sound (w := (2381 / 64881)) (n := 12)
    (lo := (18357221 / 250000000)) (hi := (14685777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33631 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33631 / 31250) = 1/(31250 / 33631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_206 : Bounds (18357221 / 250000000) (14685777 / 200000000) (Real.log (33631 / 31250)) := by
  have h := reflection_log_206_neg
  have he : Real.log (33631 / 31250) = -Real.log (31250 / 33631) := by
    rw [show ((33631 / 31250) : ℝ) = ((31250 / 33631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_207_neg : (79251021 / 1000000000) ≤ -Real.log (28869 / 31250) ∧
    -Real.log (28869 / 31250) ≤ (39625511 / 500000000) := by
  have h := checkLog_sound (w := (2381 / 60119)) (n := 12)
    (lo := (79251021 / 1000000000)) (hi := (39625511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28869) = 1/(28869 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_207 : Bounds (-39625511 / 500000000) (-79251021 / 1000000000) (Real.log (28869 / 31250)) := by
  have h := reflection_log_207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_208_neg : (727767 / 125000000) ≤ -Real.log (970893339 / 976562500) ∧
    -Real.log (970893339 / 976562500) ≤ (5822137 / 1000000000) := by
  have h := checkLog_sound (w := (5669161 / 1947455839)) (n := 12)
    (lo := (727767 / 125000000)) (hi := (5822137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 970893339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 970893339) = 1/(970893339 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_208 : Bounds (-5822137 / 1000000000) (-727767 / 125000000) (Real.log (970893339 / 976562500)) := by
  have h := reflection_log_208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_209_neg : (9517097 / 62500000) ≤ -Real.log (500000000000 / 582239369703) ∧
    -Real.log (500000000000 / 582239369703) ≤ (152273553 / 1000000000) := by
  have h := checkLog_sound (w := (82239369703 / 1082239369703)) (n := 12)
    (lo := (9517097 / 62500000)) (hi := (152273553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582239369703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582239369703 / 500000000000) = 1/(500000000000 / 582239369703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_209 : Bounds (9517097 / 62500000) (152273553 / 1000000000) (Real.log (582239369703 / 500000000000)) := by
  have h := reflection_log_209_neg
  have he : Real.log (582239369703 / 500000000000) = -Real.log (500000000000 / 582239369703) := by
    rw [show ((582239369703 / 500000000000) : ℝ) = ((500000000000 / 582239369703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_210_neg : (30535981 / 200000000) ≤ -Real.log (125000000000 / 145619003083) ∧
    -Real.log (125000000000 / 145619003083) ≤ (76339953 / 500000000) := by
  have h := checkLog_sound (w := (20619003083 / 270619003083)) (n := 12)
    (lo := (30535981 / 200000000)) (hi := (76339953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145619003083 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145619003083 / 125000000000) = 1/(125000000000 / 145619003083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_210 : Bounds (30535981 / 200000000) (76339953 / 500000000) (Real.log (145619003083 / 125000000000)) := by
  have h := reflection_log_210_neg
  have he : Real.log (145619003083 / 125000000000) = -Real.log (125000000000 / 145619003083) := by
    rw [show ((145619003083 / 125000000000) : ℝ) = ((125000000000 / 145619003083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_211_neg : (152675317 / 500000000) ≤ -Real.log (125000000000 / 169637595757) ∧
    -Real.log (125000000000 / 169637595757) ≤ (61070127 / 200000000) := by
  have h := checkLog_sound (w := (44637595757 / 294637595757)) (n := 12)
    (lo := (152675317 / 500000000)) (hi := (61070127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169637595757 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169637595757 / 125000000000) = 1/(125000000000 / 169637595757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_211 : Bounds (152675317 / 500000000) (61070127 / 200000000) (Real.log (169637595757 / 125000000000)) := by
  have h := reflection_log_211_neg
  have he : Real.log (169637595757 / 125000000000) = -Real.log (125000000000 / 169637595757) := by
    rw [show ((169637595757 / 125000000000) : ℝ) = ((125000000000 / 169637595757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_212_neg : (38194417 / 125000000) ≤ -Real.log (250000000000 / 339344648751) ∧
    -Real.log (250000000000 / 339344648751) ≤ (305555337 / 1000000000) := by
  have h := checkLog_sound (w := (89344648751 / 589344648751)) (n := 12)
    (lo := (38194417 / 125000000)) (hi := (305555337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339344648751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339344648751 / 250000000000) = 1/(250000000000 / 339344648751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_212 : Bounds (38194417 / 125000000) (305555337 / 1000000000) (Real.log (339344648751 / 250000000000)) := by
  have h := reflection_log_212_neg
  have he : Real.log (339344648751 / 250000000000) = -Real.log (250000000000 / 339344648751) := by
    rw [show ((339344648751 / 250000000000) : ℝ) = ((250000000000 / 339344648751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_213_neg : (141239111 / 1000000000) ≤ -Real.log (10000 / 11517) ∧
    -Real.log (10000 / 11517) ≤ (17654889 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 21517)) (n := 12)
    (lo := (141239111 / 1000000000)) (hi := (17654889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11517 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11517 / 10000) = 1/(10000 / 11517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_213 : Bounds (141239111 / 1000000000) (17654889 / 125000000) (Real.log (11517 / 10000)) := by
  have h := reflection_log_213_neg
  have he : Real.log (11517 / 10000) = -Real.log (10000 / 11517) := by
    rw [show ((11517 / 10000) : ℝ) = ((10000 / 11517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_214_neg : (41130233 / 250000000) ≤ -Real.log (8483 / 10000) ∧
    -Real.log (8483 / 10000) ≤ (164520933 / 1000000000) := by
  have h := checkLog_sound (w := (1517 / 18483)) (n := 12)
    (lo := (41130233 / 250000000)) (hi := (164520933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8483) = 1/(8483 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_214 : Bounds (-164520933 / 1000000000) (-41130233 / 250000000) (Real.log (8483 / 10000)) := by
  have h := reflection_log_214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_215_neg : (18961 / 125000000) ≤ -Real.log (10000000 / 10001517) ∧
    -Real.log (10000000 / 10001517) ≤ (151689 / 1000000000) := by
  have h := checkLog_sound (w := (1517 / 20001517)) (n := 12)
    (lo := (18961 / 125000000)) (hi := (151689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001517 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001517 / 10000000) = 1/(10000000 / 10001517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_215 : Bounds (18961 / 125000000) (151689 / 1000000000) (Real.log (10001517 / 10000000)) := by
  have h := reflection_log_215_neg
  have he : Real.log (10001517 / 10000000) = -Real.log (10000000 / 10001517) := by
    rw [show ((10001517 / 10000000) : ℝ) = ((10000000 / 10001517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_216_neg : (151711 / 1000000000) ≤ -Real.log (9998483 / 10000000) ∧
    -Real.log (9998483 / 10000000) ≤ (4741 / 31250000) := by
  have h := checkLog_sound (w := (1517 / 19998483)) (n := 12)
    (lo := (151711 / 1000000000)) (hi := (4741 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998483) = 1/(9998483 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_216 : Bounds (-4741 / 31250000) (-151711 / 1000000000) (Real.log (9998483 / 10000000)) := by
  have h := reflection_log_216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_217_neg : (4592267 / 62500000) ≤ -Real.log (1000000 / 1076243) ∧
    -Real.log (1000000 / 1076243) ≤ (73476273 / 1000000000) := by
  have h := checkLog_sound (w := (76243 / 2076243)) (n := 12)
    (lo := (4592267 / 62500000)) (hi := (73476273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076243 / 1000000) = 1/(1000000 / 1076243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_217 : Bounds (4592267 / 62500000) (73476273 / 1000000000) (Real.log (1076243 / 1000000)) := by
  have h := reflection_log_217_neg
  have he : Real.log (1076243 / 1000000) = -Real.log (1000000 / 1076243) := by
    rw [show ((1076243 / 1000000) : ℝ) = ((1000000 / 1076243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_218_neg : (19826557 / 250000000) ≤ -Real.log (923757 / 1000000) ∧
    -Real.log (923757 / 1000000) ≤ (79306229 / 1000000000) := by
  have h := checkLog_sound (w := (76243 / 1923757)) (n := 12)
    (lo := (19826557 / 250000000)) (hi := (79306229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923757) = 1/(923757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_218 : Bounds (-79306229 / 1000000000) (-19826557 / 250000000) (Real.log (923757 / 1000000)) := by
  have h := reflection_log_218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_219_neg : (1457489 / 250000000) ≤ -Real.log (994187004951 / 1000000000000) ∧
    -Real.log (994187004951 / 1000000000000) ≤ (5829957 / 1000000000) := by
  have h := checkLog_sound (w := (5812995049 / 1994187004951)) (n := 12)
    (lo := (1457489 / 250000000)) (hi := (5829957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994187004951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994187004951) = 1/(994187004951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_219 : Bounds (-5829957 / 1000000000) (-1457489 / 250000000) (Real.log (994187004951 / 1000000000000)) := by
  have h := reflection_log_219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_220_neg : (76187067 / 500000000) ≤ -Real.log (20000000000 / 23291917399) ∧
    -Real.log (20000000000 / 23291917399) ≤ (30474827 / 200000000) := by
  have h := checkLog_sound (w := (3291917399 / 43291917399)) (n := 12)
    (lo := (76187067 / 500000000)) (hi := (30474827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23291917399 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23291917399 / 20000000000) = 1/(20000000000 / 23291917399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_220 : Bounds (76187067 / 500000000) (30474827 / 200000000) (Real.log (23291917399 / 20000000000)) := by
  have h := reflection_log_220_neg
  have he : Real.log (23291917399 / 20000000000) = -Real.log (20000000000 / 23291917399) := by
    rw [show ((23291917399 / 20000000000) : ℝ) = ((20000000000 / 23291917399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_221_neg : (152782501 / 1000000000) ≤ -Real.log (250000000000 / 291267887551) ∧
    -Real.log (250000000000 / 291267887551) ≤ (76391251 / 500000000) := by
  have h := checkLog_sound (w := (41267887551 / 541267887551)) (n := 12)
    (lo := (152782501 / 1000000000)) (hi := (76391251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291267887551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291267887551 / 250000000000) = 1/(250000000000 / 291267887551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_221 : Bounds (152782501 / 1000000000) (76391251 / 500000000) (Real.log (291267887551 / 250000000000)) := by
  have h := reflection_log_221_neg
  have he : Real.log (291267887551 / 250000000000) = -Real.log (250000000000 / 291267887551) := by
    rw [show ((291267887551 / 250000000000) : ℝ) = ((250000000000 / 291267887551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_222_neg : (38194417 / 125000000) ≤ -Real.log (500000000000 / 678689297501) ∧
    -Real.log (500000000000 / 678689297501) ≤ (305555337 / 1000000000) := by
  have h := checkLog_sound (w := (178689297501 / 1178689297501)) (n := 12)
    (lo := (38194417 / 125000000)) (hi := (305555337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678689297501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678689297501 / 500000000000) = 1/(500000000000 / 678689297501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_222 : Bounds (38194417 / 125000000) (305555337 / 1000000000) (Real.log (678689297501 / 500000000000)) := by
  have h := reflection_log_222_neg
  have he : Real.log (678689297501 / 500000000000) = -Real.log (500000000000 / 678689297501) := by
    rw [show ((678689297501 / 500000000000) : ℝ) = ((500000000000 / 678689297501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_223_neg : (305760043 / 1000000000) ≤ -Real.log (20000000000 / 27153129789) ∧
    -Real.log (20000000000 / 27153129789) ≤ (76440011 / 250000000) := by
  have h := checkLog_sound (w := (7153129789 / 47153129789)) (n := 12)
    (lo := (305760043 / 1000000000)) (hi := (76440011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27153129789 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27153129789 / 20000000000) = 1/(20000000000 / 27153129789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_223 : Bounds (305760043 / 1000000000) (76440011 / 250000000) (Real.log (27153129789 / 20000000000)) := by
  have h := reflection_log_223_neg
  have he : Real.log (27153129789 / 20000000000) = -Real.log (20000000000 / 27153129789) := by
    rw [show ((27153129789 / 20000000000) : ℝ) = ((20000000000 / 27153129789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_224_neg : (8832871 / 62500000) ≤ -Real.log (5000 / 5759) ∧
    -Real.log (5000 / 5759) ≤ (141325937 / 1000000000) := by
  have h := checkLog_sound (w := (759 / 10759)) (n := 12)
    (lo := (8832871 / 62500000)) (hi := (141325937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 5000) = 1/(5000 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_224 : Bounds (8832871 / 62500000) (141325937 / 1000000000) (Real.log (5759 / 5000)) := by
  have h := reflection_log_224_neg
  have he : Real.log (5759 / 5000) = -Real.log (5000 / 5759) := by
    rw [show ((5759 / 5000) : ℝ) = ((5000 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_225_neg : (164638821 / 1000000000) ≤ -Real.log (4241 / 5000) ∧
    -Real.log (4241 / 5000) ≤ (82319411 / 500000000) := by
  have h := checkLog_sound (w := (759 / 9241)) (n := 12)
    (lo := (164638821 / 1000000000)) (hi := (82319411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4241) = 1/(4241 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_225 : Bounds (-82319411 / 500000000) (-164638821 / 1000000000) (Real.log (4241 / 5000)) := by
  have h := reflection_log_225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_226_neg : (37947 / 250000000) ≤ -Real.log (5000000 / 5000759) ∧
    -Real.log (5000000 / 5000759) ≤ (151789 / 1000000000) := by
  have h := checkLog_sound (w := (759 / 10000759)) (n := 12)
    (lo := (37947 / 250000000)) (hi := (151789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000759 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000759 / 5000000) = 1/(5000000 / 5000759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_226 : Bounds (37947 / 250000000) (151789 / 1000000000) (Real.log (5000759 / 5000000)) := by
  have h := reflection_log_226_neg
  have he : Real.log (5000759 / 5000000) = -Real.log (5000000 / 5000759) := by
    rw [show ((5000759 / 5000000) : ℝ) = ((5000000 / 5000759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_227_neg : (151811 / 1000000000) ≤ -Real.log (4999241 / 5000000) ∧
    -Real.log (4999241 / 5000000) ≤ (37953 / 250000000) := by
  have h := checkLog_sound (w := (759 / 9999241)) (n := 12)
    (lo := (151811 / 1000000000)) (hi := (37953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999241) = 1/(4999241 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_227 : Bounds (-37953 / 250000000) (-151811 / 1000000000) (Real.log (4999241 / 5000000)) := by
  have h := reflection_log_227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_228_neg : (36761829 / 500000000) ≤ -Real.log (500000 / 538147) ∧
    -Real.log (500000 / 538147) ≤ (73523659 / 1000000000) := by
  have h := checkLog_sound (w := (38147 / 1038147)) (n := 12)
    (lo := (36761829 / 500000000)) (hi := (73523659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538147 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538147 / 500000) = 1/(500000 / 538147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_228 : Bounds (36761829 / 500000000) (73523659 / 1000000000) (Real.log (538147 / 500000)) := by
  have h := reflection_log_228_neg
  have he : Real.log (538147 / 500000) = -Real.log (500000 / 538147) := by
    rw [show ((538147 / 500000) : ℝ) = ((500000 / 538147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_229_neg : (79361439 / 1000000000) ≤ -Real.log (461853 / 500000) ∧
    -Real.log (461853 / 500000) ≤ (496009 / 6250000) := by
  have h := checkLog_sound (w := (38147 / 961853)) (n := 12)
    (lo := (79361439 / 1000000000)) (hi := (496009 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461853) = 1/(461853 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_229 : Bounds (-496009 / 6250000) (-79361439 / 1000000000) (Real.log (461853 / 500000)) := by
  have h := reflection_log_229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_230_neg : (5837781 / 1000000000) ≤ -Real.log (248544806391 / 250000000000) ∧
    -Real.log (248544806391 / 250000000000) ≤ (2918891 / 500000000) := by
  have h := checkLog_sound (w := (1455193609 / 498544806391)) (n := 12)
    (lo := (5837781 / 1000000000)) (hi := (2918891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248544806391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248544806391) = 1/(248544806391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_230 : Bounds (-2918891 / 500000000) (-5837781 / 1000000000) (Real.log (248544806391 / 250000000000)) := by
  have h := reflection_log_230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_231_neg : (152476727 / 1000000000) ≤ -Real.log (500000000000 / 582357678083) ∧
    -Real.log (500000000000 / 582357678083) ≤ (19059591 / 125000000) := by
  have h := checkLog_sound (w := (82357678083 / 1082357678083)) (n := 12)
    (lo := (152476727 / 1000000000)) (hi := (19059591 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582357678083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582357678083 / 500000000000) = 1/(500000000000 / 582357678083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_231 : Bounds (152476727 / 1000000000) (19059591 / 125000000) (Real.log (582357678083 / 500000000000)) := by
  have h := reflection_log_231_neg
  have he : Real.log (582357678083 / 500000000000) = -Real.log (500000000000 / 582357678083) := by
    rw [show ((582357678083 / 500000000000) : ℝ) = ((500000000000 / 582357678083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_232_neg : (76442549 / 500000000) ≤ -Real.log (50000000000 / 58259554447) ∧
    -Real.log (50000000000 / 58259554447) ≤ (152885099 / 1000000000) := by
  have h := checkLog_sound (w := (8259554447 / 108259554447)) (n := 12)
    (lo := (76442549 / 500000000)) (hi := (152885099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58259554447 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58259554447 / 50000000000) = 1/(50000000000 / 58259554447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_232 : Bounds (76442549 / 500000000) (152885099 / 1000000000) (Real.log (58259554447 / 50000000000)) := by
  have h := reflection_log_232_neg
  have he : Real.log (58259554447 / 50000000000) = -Real.log (50000000000 / 58259554447) := by
    rw [show ((58259554447 / 50000000000) : ℝ) = ((50000000000 / 58259554447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_233_neg : (305760043 / 1000000000) ≤ -Real.log (125000000000 / 169707061181) ∧
    -Real.log (125000000000 / 169707061181) ≤ (76440011 / 250000000) := by
  have h := checkLog_sound (w := (44707061181 / 294707061181)) (n := 12)
    (lo := (305760043 / 1000000000)) (hi := (76440011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169707061181 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169707061181 / 125000000000) = 1/(125000000000 / 169707061181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_233 : Bounds (305760043 / 1000000000) (76440011 / 250000000) (Real.log (169707061181 / 125000000000)) := by
  have h := reflection_log_233_neg
  have he : Real.log (169707061181 / 125000000000) = -Real.log (125000000000 / 169707061181) := by
    rw [show ((169707061181 / 125000000000) : ℝ) = ((125000000000 / 169707061181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_234_neg : (152982379 / 500000000) ≤ -Real.log (62500000000 / 84870903089) ∧
    -Real.log (62500000000 / 84870903089) ≤ (305964759 / 1000000000) := by
  have h := checkLog_sound (w := (22370903089 / 147370903089)) (n := 12)
    (lo := (152982379 / 500000000)) (hi := (305964759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84870903089 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84870903089 / 62500000000) = 1/(62500000000 / 84870903089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_234 : Bounds (152982379 / 500000000) (305964759 / 1000000000) (Real.log (84870903089 / 62500000000)) := by
  have h := reflection_log_234_neg
  have he : Real.log (84870903089 / 62500000000) = -Real.log (62500000000 / 84870903089) := by
    rw [show ((84870903089 / 62500000000) : ℝ) = ((62500000000 / 84870903089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_235_neg : (8838297 / 62500000) ≤ -Real.log (10000 / 11519) ∧
    -Real.log (10000 / 11519) ≤ (141412753 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 21519)) (n := 12)
    (lo := (8838297 / 62500000)) (hi := (141412753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11519 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11519 / 10000) = 1/(10000 / 11519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_235 : Bounds (8838297 / 62500000) (141412753 / 1000000000) (Real.log (11519 / 10000)) := by
  have h := reflection_log_235_neg
  have he : Real.log (11519 / 10000) = -Real.log (10000 / 11519) := by
    rw [show ((11519 / 10000) : ℝ) = ((10000 / 11519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_236_neg : (6590269 / 40000000) ≤ -Real.log (8481 / 10000) ∧
    -Real.log (8481 / 10000) ≤ (82378363 / 500000000) := by
  have h := checkLog_sound (w := (1519 / 18481)) (n := 12)
    (lo := (6590269 / 40000000)) (hi := (82378363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8481) = 1/(8481 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_236 : Bounds (-82378363 / 500000000) (-6590269 / 40000000) (Real.log (8481 / 10000)) := by
  have h := reflection_log_236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_237_neg : (9493 / 62500000) ≤ -Real.log (10000000 / 10001519) ∧
    -Real.log (10000000 / 10001519) ≤ (151889 / 1000000000) := by
  have h := checkLog_sound (w := (1519 / 20001519)) (n := 12)
    (lo := (9493 / 62500000)) (hi := (151889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001519 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001519 / 10000000) = 1/(10000000 / 10001519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_237 : Bounds (9493 / 62500000) (151889 / 1000000000) (Real.log (10001519 / 10000000)) := by
  have h := reflection_log_237_neg
  have he : Real.log (10001519 / 10000000) = -Real.log (10000000 / 10001519) := by
    rw [show ((10001519 / 10000000) : ℝ) = ((10000000 / 10001519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_238_neg : (151911 / 1000000000) ≤ -Real.log (9998481 / 10000000) ∧
    -Real.log (9998481 / 10000000) ≤ (18989 / 125000000) := by
  have h := checkLog_sound (w := (1519 / 19998481)) (n := 12)
    (lo := (151911 / 1000000000)) (hi := (18989 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998481) = 1/(9998481 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_238 : Bounds (-18989 / 125000000) (-151911 / 1000000000) (Real.log (9998481 / 10000000)) := by
  have h := reflection_log_238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_239_neg : (36690747 / 500000000) ≤ -Real.log (1000000 / 1076141) ∧
    -Real.log (1000000 / 1076141) ≤ (14676299 / 200000000) := by
  have h := checkLog_sound (w := (76141 / 2076141)) (n := 12)
    (lo := (36690747 / 500000000)) (hi := (14676299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1076141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1076141 / 1000000) = 1/(1000000 / 1076141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_239 : Bounds (36690747 / 500000000) (14676299 / 200000000) (Real.log (1076141 / 1000000)) := by
  have h := reflection_log_239_neg
  have he : Real.log (1076141 / 1000000) = -Real.log (1000000 / 1076141) := by
    rw [show ((1076141 / 1000000) : ℝ) = ((1000000 / 1076141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_240_neg : (9899477 / 125000000) ≤ -Real.log (923859 / 1000000) ∧
    -Real.log (923859 / 1000000) ≤ (79195817 / 1000000000) := by
  have h := checkLog_sound (w := (76141 / 1923859)) (n := 12)
    (lo := (9899477 / 125000000)) (hi := (79195817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 923859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 923859) = 1/(923859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_240 : Bounds (-79195817 / 1000000000) (-9899477 / 125000000) (Real.log (923859 / 1000000)) := by
  have h := reflection_log_240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_241_neg : (73570113 / 1000000000) ≤ -Real.log (125000 / 134543) ∧
    -Real.log (125000 / 134543) ≤ (36785057 / 500000000) := by
  have h := checkLog_sound (w := (9543 / 259543)) (n := 12)
    (lo := (73570113 / 1000000000)) (hi := (36785057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134543 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134543 / 125000) = 1/(125000 / 134543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_241 : Bounds (73570113 / 1000000000) (36785057 / 500000000) (Real.log (134543 / 125000)) := by
  have h := reflection_log_241_neg
  have he : Real.log (134543 / 125000) = -Real.log (125000 / 134543) := by
    rw [show ((134543 / 125000) : ℝ) = ((125000 / 134543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_242_neg : (79415571 / 1000000000) ≤ -Real.log (115457 / 125000) ∧
    -Real.log (115457 / 125000) ≤ (19853893 / 250000000) := by
  have h := checkLog_sound (w := (9543 / 240457)) (n := 12)
    (lo := (79415571 / 1000000000)) (hi := (19853893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115457) = 1/(115457 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_242 : Bounds (-19853893 / 250000000) (-79415571 / 1000000000) (Real.log (115457 / 125000)) := by
  have h := reflection_log_242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_243_neg : (5845457 / 1000000000) ≤ -Real.log (15533931151 / 15625000000) ∧
    -Real.log (15533931151 / 15625000000) ≤ (2922729 / 500000000) := by
  have h := checkLog_sound (w := (91068849 / 31158931151)) (n := 12)
    (lo := (5845457 / 1000000000)) (hi := (2922729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15533931151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15533931151) = 1/(15533931151 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_243 : Bounds (-2922729 / 500000000) (-5845457 / 1000000000) (Real.log (15533931151 / 15625000000)) := by
  have h := reflection_log_243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_244_neg : (2907161 / 500000000) ≤ -Real.log (994202548119 / 1000000000000) ∧
    -Real.log (994202548119 / 1000000000000) ≤ (5814323 / 1000000000) := by
  have h := checkLog_sound (w := (5797451881 / 1994202548119)) (n := 12)
    (lo := (2907161 / 500000000)) (hi := (5814323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994202548119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994202548119) = 1/(994202548119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_244 : Bounds (-5814323 / 1000000000) (-2907161 / 500000000) (Real.log (994202548119 / 1000000000000)) := by
  have h := reflection_log_244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_245_neg : (15257731 / 100000000) ≤ -Real.log (3125000000 / 3640101601) ∧
    -Real.log (3125000000 / 3640101601) ≤ (152577311 / 1000000000) := by
  have h := checkLog_sound (w := (515101601 / 6765101601)) (n := 12)
    (lo := (15257731 / 100000000)) (hi := (152577311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3640101601 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3640101601 / 3125000000) = 1/(3125000000 / 3640101601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_245 : Bounds (15257731 / 100000000) (152577311 / 1000000000) (Real.log (3640101601 / 3125000000)) := by
  have h := reflection_log_245_neg
  have he : Real.log (3640101601 / 3125000000) = -Real.log (3125000000 / 3640101601) := by
    rw [show ((3640101601 / 3125000000) : ℝ) = ((3125000000 / 3640101601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_246_neg : (38246421 / 250000000) ≤ -Real.log (250000000000 / 291327074149) ∧
    -Real.log (250000000000 / 291327074149) ≤ (30597137 / 200000000) := by
  have h := checkLog_sound (w := (41327074149 / 541327074149)) (n := 12)
    (lo := (38246421 / 250000000)) (hi := (30597137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291327074149 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291327074149 / 250000000000) = 1/(250000000000 / 291327074149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_246 : Bounds (38246421 / 250000000) (30597137 / 200000000) (Real.log (291327074149 / 250000000000)) := by
  have h := reflection_log_246_neg
  have he : Real.log (291327074149 / 250000000000) = -Real.log (250000000000 / 291327074149) := by
    rw [show ((291327074149 / 250000000000) : ℝ) = ((250000000000 / 291327074149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_247_neg : (152982379 / 500000000) ≤ -Real.log (500000000000 / 678967224711) ∧
    -Real.log (500000000000 / 678967224711) ≤ (305964759 / 1000000000) := by
  have h := checkLog_sound (w := (178967224711 / 1178967224711)) (n := 12)
    (lo := (152982379 / 500000000)) (hi := (305964759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678967224711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678967224711 / 500000000000) = 1/(500000000000 / 678967224711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_247 : Bounds (152982379 / 500000000) (305964759 / 1000000000) (Real.log (678967224711 / 500000000000)) := by
  have h := reflection_log_247_neg
  have he : Real.log (678967224711 / 500000000000) = -Real.log (500000000000 / 678967224711) := by
    rw [show ((678967224711 / 500000000000) : ℝ) = ((500000000000 / 678967224711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_248_neg : (153084739 / 500000000) ≤ -Real.log (15625000000 / 21222069921) ∧
    -Real.log (15625000000 / 21222069921) ≤ (306169479 / 1000000000) := by
  have h := checkLog_sound (w := (5597069921 / 36847069921)) (n := 12)
    (lo := (153084739 / 500000000)) (hi := (306169479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21222069921 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21222069921 / 15625000000) = 1/(15625000000 / 21222069921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_248 : Bounds (153084739 / 500000000) (306169479 / 1000000000) (Real.log (21222069921 / 15625000000)) := by
  have h := reflection_log_248_neg
  have he : Real.log (21222069921 / 15625000000) = -Real.log (15625000000 / 21222069921) := by
    rw [show ((21222069921 / 15625000000) : ℝ) = ((15625000000 / 21222069921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_249_neg : (70749781 / 500000000) ≤ -Real.log (125 / 144) ∧
    -Real.log (125 / 144) ≤ (141499563 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 269)) (n := 12)
    (lo := (70749781 / 500000000)) (hi := (141499563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144 / 125) = 1/(125 / 144) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_249 : Bounds (70749781 / 500000000) (141499563 / 1000000000) (Real.log (144 / 125)) := by
  have h := reflection_log_249_neg
  have he : Real.log (144 / 125) = -Real.log (125 / 144) := by
    rw [show ((144 / 125) : ℝ) = ((125 / 144) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_250_neg : (164874643 / 1000000000) ≤ -Real.log (106 / 125) ∧
    -Real.log (106 / 125) ≤ (41218661 / 250000000) := by
  have h := checkLog_sound (w := (19 / 231)) (n := 12)
    (lo := (164874643 / 1000000000)) (hi := (41218661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 106) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 106) = 1/(106 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_250 : Bounds (-41218661 / 250000000) (-164874643 / 1000000000) (Real.log (106 / 125)) := by
  have h := reflection_log_250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_251_neg : (37997 / 250000000) ≤ -Real.log (125000 / 125019) ∧
    -Real.log (125000 / 125019) ≤ (151989 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 250019)) (n := 12)
    (lo := (37997 / 250000000)) (hi := (151989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125019 / 125000) = 1/(125000 / 125019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_251 : Bounds (37997 / 250000000) (151989 / 1000000000) (Real.log (125019 / 125000)) := by
  have h := reflection_log_251_neg
  have he : Real.log (125019 / 125000) = -Real.log (125000 / 125019) := by
    rw [show ((125019 / 125000) : ℝ) = ((125000 / 125019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_252_neg : (152011 / 1000000000) ≤ -Real.log (124981 / 125000) ∧
    -Real.log (124981 / 125000) ≤ (38003 / 250000000) := by
  have h := checkLog_sound (w := (19 / 249981)) (n := 12)
    (lo := (152011 / 1000000000)) (hi := (38003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124981) = 1/(124981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_252 : Bounds (-38003 / 250000000) (-152011 / 1000000000) (Real.log (124981 / 125000)) := by
  have h := reflection_log_252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_253_neg : (36808747 / 500000000) ≤ -Real.log (200000 / 215279) ∧
    -Real.log (200000 / 215279) ≤ (14723499 / 200000000) := by
  have h := checkLog_sound (w := (15279 / 415279)) (n := 12)
    (lo := (36808747 / 500000000)) (hi := (14723499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215279 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215279 / 200000) = 1/(200000 / 215279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_253 : Bounds (36808747 / 500000000) (14723499 / 200000000) (Real.log (215279 / 200000)) := by
  have h := reflection_log_253_neg
  have he : Real.log (215279 / 200000) = -Real.log (200000 / 215279) := by
    rw [show ((215279 / 200000) : ℝ) = ((200000 / 215279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_254_neg : (79470787 / 1000000000) ≤ -Real.log (184721 / 200000) ∧
    -Real.log (184721 / 200000) ≤ (19867697 / 250000000) := by
  have h := checkLog_sound (w := (15279 / 384721)) (n := 12)
    (lo := (79470787 / 1000000000)) (hi := (19867697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184721) = 1/(184721 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_254 : Bounds (-19867697 / 250000000) (-79470787 / 1000000000) (Real.log (184721 / 200000)) := by
  have h := reflection_log_254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_255_neg : (5853293 / 1000000000) ≤ -Real.log (39766552159 / 40000000000) ∧
    -Real.log (39766552159 / 40000000000) ≤ (2926647 / 500000000) := by
  have h := checkLog_sound (w := (233447841 / 79766552159)) (n := 12)
    (lo := (5853293 / 1000000000)) (hi := (2926647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39766552159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39766552159) = 1/(39766552159 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_255 : Bounds (-2926647 / 500000000) (-5853293 / 1000000000) (Real.log (39766552159 / 40000000000)) := by
  have h := reflection_log_255_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
