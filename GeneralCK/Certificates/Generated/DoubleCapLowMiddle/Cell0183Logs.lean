import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0183
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

theorem reflection_log_1_neg : (124249661 / 200000000) ≤ -Real.log (800 / 1489) ∧
    -Real.log (800 / 1489) ≤ (310624153 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2289)) (n := 12)
    (lo := (124249661 / 200000000)) (hi := (310624153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 800) = 1/(800 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (124249661 / 200000000) (310624153 / 500000000) (Real.log (1489 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1489 / 800) = -Real.log (800 / 1489) := by
    rw [show ((1489 / 800) : ℝ) = ((800 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79003261 / 40000000) ≤ -Real.log (111 / 800) ∧
    -Real.log (111 / 800) ≤ (246885191 / 125000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 111) = 1/(111 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-246885191 / 125000000) (-79003261 / 40000000) (Real.log (111 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (619652001 / 1000000000) ≤ -Real.log (6400 / 11893) ∧
    -Real.log (6400 / 11893) ≤ (309826001 / 500000000) := by
  have h := checkLog_sound (w := (5493 / 18293)) (n := 12)
    (lo := (619652001 / 1000000000)) (hi := (309826001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11893 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11893 / 6400) = 1/(6400 / 11893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (619652001 / 1000000000) (309826001 / 500000000) (Real.log (11893 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11893 / 6400) = -Real.log (6400 / 11893) := by
    rw [show ((11893 / 6400) : ℝ) = ((6400 / 11893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (976955409 / 500000000) ≤ -Real.log (907 / 6400) ∧
    -Real.log (907 / 6400) ≤ (1953910821 / 1000000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 907) = 1/(907 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1953910821 / 1000000000) (-976955409 / 500000000) (Real.log (907 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (543776723 / 1000000000) ≤ -Real.log (400 / 689) ∧
    -Real.log (400 / 689) ≤ (135944181 / 250000000) := by
  have h := checkLog_sound (w := (289 / 1089)) (n := 12)
    (lo := (543776723 / 1000000000)) (hi := (135944181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689 / 400) = 1/(400 / 689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (543776723 / 1000000000) (135944181 / 250000000) (Real.log (689 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (689 / 400) = -Real.log (400 / 689) := by
    rw [show ((689 / 400) : ℝ) = ((400 / 689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (256386869 / 200000000) ≤ -Real.log (111 / 400) ∧
    -Real.log (111 / 400) ≤ (1281934347 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 111) = 1/(111 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1281934347 / 1000000000) (-256386869 / 200000000) (Real.log (111 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16885117 / 31250000) ≤ -Real.log (3200 / 5493) ∧
    -Real.log (3200 / 5493) ≤ (108064749 / 200000000) := by
  have h := checkLog_sound (w := (2293 / 8693)) (n := 12)
    (lo := (16885117 / 31250000)) (hi := (108064749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5493 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5493 / 3200) = 1/(3200 / 5493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16885117 / 31250000) (108064749 / 200000000) (Real.log (5493 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5493 / 3200) = -Real.log (3200 / 5493) := by
    rw [show ((5493 / 3200) : ℝ) = ((3200 / 5493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (630381819 / 500000000) ≤ -Real.log (907 / 3200) ∧
    -Real.log (907 / 3200) ≤ (31519091 / 25000000) := by
  have h := checkLog_sound (w := (693 / 2507)) (n := 12)
    (lo := (283808229 / 500000000)) (hi := (567616459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 907) = 1/(907 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31519091 / 25000000) (-630381819 / 500000000) (Real.log (907 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (639865067 / 1000000000) ≤ -Real.log (40000 / 75849) ∧
    -Real.log (40000 / 75849) ≤ (159966267 / 250000000) := by
  have h := checkLog_sound (w := (35849 / 115849)) (n := 12)
    (lo := (639865067 / 1000000000)) (hi := (159966267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75849 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75849 / 40000) = 1/(40000 / 75849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (639865067 / 1000000000) (159966267 / 250000000) (Real.log (75849 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75849 / 40000) = -Real.log (40000 / 75849) := by
    rw [show ((75849 / 40000) : ℝ) = ((40000 / 75849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2265530183 / 1000000000) ≤ -Real.log (4151 / 40000) ∧
    -Real.log (4151 / 40000) ≤ (2265530187 / 1000000000) := by
  have h := checkLog_sound (w := (849 / 9151)) (n := 12)
    (lo := (186088643 / 1000000000)) (hi := (46522161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5000 / 4151) = 1/(4151 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2265530187 / 1000000000) (-2265530183 / 1000000000) (Real.log (4151 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16020979 / 25000000) ≤ -Real.log (1000000 / 1898073) ∧
    -Real.log (1000000 / 1898073) ≤ (640839161 / 1000000000) := by
  have h := checkLog_sound (w := (898073 / 2898073)) (n := 12)
    (lo := (16020979 / 25000000)) (hi := (640839161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1898073 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1898073 / 1000000) = 1/(1000000 / 1898073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16020979 / 25000000) (640839161 / 1000000000) (Real.log (1898073 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1898073 / 1000000) = -Real.log (1000000 / 1898073) := by
    rw [show ((1898073 / 1000000) : ℝ) = ((1000000 / 1898073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1141749203 / 500000000) ≤ -Real.log (101927 / 1000000) ∧
    -Real.log (101927 / 1000000) ≤ (228349841 / 100000000) := by
  have h := checkLog_sound (w := (23073 / 226927)) (n := 12)
    (lo := (102028433 / 500000000)) (hi := (204056867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101927) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 101927) = 1/(101927 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-228349841 / 100000000) (-1141749203 / 500000000) (Real.log (101927 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (637024347 / 1000000000) ≤ -Real.log (500000 / 945423) ∧
    -Real.log (500000 / 945423) ≤ (159256087 / 250000000) := by
  have h := checkLog_sound (w := (445423 / 1445423)) (n := 12)
    (lo := (637024347 / 1000000000)) (hi := (159256087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945423 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945423 / 500000) = 1/(500000 / 945423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (637024347 / 1000000000) (159256087 / 250000000) (Real.log (945423 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (945423 / 500000) = -Real.log (500000 / 945423) := by
    rw [show ((945423 / 500000) : ℝ) = ((500000 / 945423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (553748887 / 250000000) ≤ -Real.log (54577 / 500000) ∧
    -Real.log (54577 / 500000) ≤ (69218611 / 31250000) := by
  have h := checkLog_sound (w := (7923 / 117077)) (n := 12)
    (lo := (16944251 / 125000000)) (hi := (135554009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54577) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 54577) = 1/(54577 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-69218611 / 31250000) (-553748887 / 250000000) (Real.log (54577 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (159535039 / 250000000) ≤ -Real.log (1000000 / 1892957) ∧
    -Real.log (1000000 / 1892957) ≤ (638140157 / 1000000000) := by
  have h := checkLog_sound (w := (892957 / 2892957)) (n := 12)
    (lo := (159535039 / 250000000)) (hi := (638140157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1892957 / 1000000) = 1/(1000000 / 1892957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (159535039 / 250000000) (638140157 / 1000000000) (Real.log (1892957 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1892957 / 1000000) = -Real.log (1000000 / 1892957) := by
    rw [show ((1892957 / 1000000) : ℝ) = ((1000000 / 1892957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1117262327 / 500000000) ≤ -Real.log (107043 / 1000000) ∧
    -Real.log (107043 / 1000000) ≤ (1117262329 / 500000000) := by
  have h := checkLog_sound (w := (17957 / 232043)) (n := 12)
    (lo := (77541557 / 500000000)) (hi := (31016623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107043) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 107043) = 1/(107043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1117262329 / 500000000) (-1117262327 / 500000000) (Real.log (107043 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (11621581 / 4000000) ≤ -Real.log (125000000000 / 2284058058299) ∧
    -Real.log (125000000000 / 2284058058299) ≤ (581079051 / 200000000) := by
  have h := checkLog_sound (w := (284058058299 / 4284058058299)) (n := 12)
    (lo := (13280653 / 100000000)) (hi := (132806531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2284058058299 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2284058058299 / 2000000000000) = 1/(125000000000 / 2284058058299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (11621581 / 4000000) (581079051 / 200000000) (Real.log (2284058058299 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2284058058299 / 125000000000) = -Real.log (125000000000 / 2284058058299) := by
    rw [show ((2284058058299 / 125000000000) : ℝ) = ((125000000000 / 2284058058299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1462168783 / 500000000) ≤ -Real.log (500000000000 / 9310943125963) ∧
    -Real.log (500000000000 / 9310943125963) ≤ (2924337571 / 1000000000) := by
  have h := checkLog_sound (w := (1310943125963 / 17310943125963)) (n := 12)
    (lo := (75874423 / 500000000)) (hi := (151748847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9310943125963 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(9310943125963 / 8000000000000) = 1/(500000000000 / 9310943125963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1462168783 / 500000000) (2924337571 / 1000000000) (Real.log (9310943125963 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9310943125963 / 500000000000) = -Real.log (500000000000 / 9310943125963) := by
    rw [show ((9310943125963 / 500000000000) : ℝ) = ((500000000000 / 9310943125963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (570403979 / 200000000) ≤ -Real.log (20000000000 / 346454733679) ∧
    -Real.log (20000000000 / 346454733679) ≤ (28520199 / 10000000) := by
  have h := checkLog_sound (w := (26454733679 / 666454733679)) (n := 12)
    (lo := (3177247 / 40000000)) (hi := (9928897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346454733679 / 320000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(346454733679 / 320000000000) = 1/(20000000000 / 346454733679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (570403979 / 200000000) (28520199 / 10000000) (Real.log (346454733679 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (346454733679 / 20000000000) = -Real.log (20000000000 / 346454733679) := by
    rw [show ((346454733679 / 20000000000) : ℝ) = ((20000000000 / 346454733679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (287266481 / 100000000) ≤ -Real.log (500000000000 / 8842040114721) ∧
    -Real.log (500000000000 / 8842040114721) ≤ (574532963 / 200000000) := by
  have h := checkLog_sound (w := (842040114721 / 16842040114721)) (n := 12)
    (lo := (10007609 / 100000000)) (hi := (100076091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8842040114721 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8842040114721 / 8000000000000) = 1/(500000000000 / 8842040114721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (287266481 / 100000000) (574532963 / 200000000) (Real.log (8842040114721 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8842040114721 / 500000000000) = -Real.log (500000000000 / 8842040114721) := by
    rw [show ((8842040114721 / 500000000000) : ℝ) = ((500000000000 / 8842040114721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0183
