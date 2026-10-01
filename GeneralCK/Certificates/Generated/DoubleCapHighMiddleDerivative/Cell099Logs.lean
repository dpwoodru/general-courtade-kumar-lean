import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell099
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (268953087 / 1000000000) ≤ -Real.log (256 / 335) ∧
    -Real.log (256 / 335) ≤ (525299 / 1953125) := by
  have h := checkLog_sound (w := (79 / 591)) (n := 12)
    (lo := (268953087 / 1000000000)) (hi := (525299 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335 / 256) = 1/(256 / 335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (268953087 / 1000000000) (525299 / 1953125) (Real.log (335 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (335 / 256) = -Real.log (256 / 335) := by
    rw [show ((335 / 256) : ℝ) = ((256 / 335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (369027711 / 1000000000) ≤ -Real.log (177 / 256) ∧
    -Real.log (177 / 256) ≤ (2883029 / 7812500) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 177) = 1/(177 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2883029 / 7812500) (-369027711 / 1000000000) (Real.log (177 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10740209 / 40000000) ≤ -Real.log (5120 / 6697) ∧
    -Real.log (5120 / 6697) ≤ (134252613 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 11817)) (n := 12)
    (lo := (10740209 / 40000000)) (hi := (134252613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6697 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6697 / 5120) = 1/(5120 / 6697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10740209 / 40000000) (134252613 / 500000000) (Real.log (6697 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6697 / 5120) = -Real.log (5120 / 6697) := by
    rw [show ((6697 / 5120) : ℝ) = ((5120 / 6697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (368180613 / 1000000000) ≤ -Real.log (3543 / 5120) ∧
    -Real.log (3543 / 5120) ≤ (184090307 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 8663)) (n := 12)
    (lo := (368180613 / 1000000000)) (hi := (184090307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3543) = 1/(3543 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-184090307 / 500000000) (-368180613 / 1000000000) (Real.log (3543 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (197776511 / 1000000000) ≤ -Real.log (100000 / 121869) ∧
    -Real.log (100000 / 121869) ≤ (1545129 / 7812500) := by
  have h := checkLog_sound (w := (21869 / 221869)) (n := 12)
    (lo := (197776511 / 1000000000)) (hi := (1545129 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121869 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121869 / 100000) = 1/(100000 / 121869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (197776511 / 1000000000) (1545129 / 7812500) (Real.log (121869 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121869 / 100000) = -Real.log (100000 / 121869) := by
    rw [show ((121869 / 100000) : ℝ) = ((100000 / 121869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3084791 / 12500000) ≤ -Real.log (78131 / 100000) ∧
    -Real.log (78131 / 100000) ≤ (246783281 / 1000000000) := by
  have h := checkLog_sound (w := (21869 / 178131)) (n := 12)
    (lo := (3084791 / 12500000)) (hi := (246783281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78131) = 1/(78131 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-246783281 / 1000000000) (-3084791 / 12500000) (Real.log (78131 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12382619 / 62500000) ≤ -Real.log (1000000 / 1219111) ∧
    -Real.log (1000000 / 1219111) ≤ (39624381 / 200000000) := by
  have h := checkLog_sound (w := (219111 / 2219111)) (n := 12)
    (lo := (12382619 / 62500000)) (hi := (39624381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219111 / 1000000) = 1/(1000000 / 1219111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12382619 / 62500000) (39624381 / 200000000) (Real.log (1219111 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1219111 / 1000000) = -Real.log (1000000 / 1219111) := by
    rw [show ((1219111 / 1000000) : ℝ) = ((1000000 / 1219111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30915283 / 125000000) ≤ -Real.log (780889 / 1000000) ∧
    -Real.log (780889 / 1000000) ≤ (49464453 / 200000000) := by
  have h := checkLog_sound (w := (219111 / 1780889)) (n := 12)
    (lo := (30915283 / 125000000)) (hi := (49464453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780889) = 1/(780889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-49464453 / 200000000) (-30915283 / 125000000) (Real.log (780889 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72791613 / 500000000) ≤ -Real.log (500000 / 578357) ∧
    -Real.log (500000 / 578357) ≤ (145583227 / 1000000000) := by
  have h := checkLog_sound (w := (78357 / 1078357)) (n := 12)
    (lo := (72791613 / 500000000)) (hi := (145583227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578357 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578357 / 500000) = 1/(500000 / 578357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72791613 / 500000000) (145583227 / 1000000000) (Real.log (578357 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (578357 / 500000) = -Real.log (500000 / 578357) := by
    rw [show ((578357 / 500000) : ℝ) = ((500000 / 578357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170449113 / 1000000000) ≤ -Real.log (421643 / 500000) ∧
    -Real.log (421643 / 500000) ≤ (85224557 / 500000000) := by
  have h := checkLog_sound (w := (78357 / 921643)) (n := 12)
    (lo := (170449113 / 1000000000)) (hi := (85224557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421643) = 1/(421643 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-85224557 / 500000000) (-170449113 / 1000000000) (Real.log (421643 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145851191 / 1000000000) ≤ -Real.log (31250 / 36157) ∧
    -Real.log (31250 / 36157) ≤ (18231399 / 125000000) := by
  have h := checkLog_sound (w := (4907 / 67407)) (n := 12)
    (lo := (145851191 / 1000000000)) (hi := (18231399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36157 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36157 / 31250) = 1/(31250 / 36157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145851191 / 1000000000) (18231399 / 125000000) (Real.log (36157 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (36157 / 31250) = -Real.log (31250 / 36157) := by
    rw [show ((36157 / 31250) : ℝ) = ((31250 / 36157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (170816791 / 1000000000) ≤ -Real.log (26343 / 31250) ∧
    -Real.log (26343 / 31250) ≤ (21352099 / 125000000) := by
  have h := checkLog_sound (w := (4907 / 57593)) (n := 12)
    (lo := (170816791 / 1000000000)) (hi := (21352099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26343) = 1/(26343 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21352099 / 125000000) (-170816791 / 1000000000) (Real.log (26343 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (636685839 / 1000000000) ≤ -Real.log (500000000000 / 945103020039) ∧
    -Real.log (500000000000 / 945103020039) ≤ (7958573 / 12500000) := by
  have h := checkLog_sound (w := (445103020039 / 1445103020039)) (n := 12)
    (lo := (636685839 / 1000000000)) (hi := (7958573 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((945103020039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(945103020039 / 500000000000) = 1/(500000000000 / 945103020039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (636685839 / 1000000000) (7958573 / 12500000) (Real.log (945103020039 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (945103020039 / 500000000000) = -Real.log (500000000000 / 945103020039) := by
    rw [show ((945103020039 / 500000000000) : ℝ) = ((500000000000 / 945103020039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (637980799 / 1000000000) ≤ -Real.log (15625000000 / 29572740113) ∧
    -Real.log (15625000000 / 29572740113) ≤ (199369 / 312500) := by
  have h := checkLog_sound (w := (13947740113 / 45197740113)) (n := 12)
    (lo := (637980799 / 1000000000)) (hi := (199369 / 312500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29572740113 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29572740113 / 15625000000) = 1/(15625000000 / 29572740113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (637980799 / 1000000000) (199369 / 312500) (Real.log (29572740113 / 15625000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (29572740113 / 15625000000) = -Real.log (15625000000 / 29572740113) := by
    rw [show ((29572740113 / 15625000000) : ℝ) = ((15625000000 / 29572740113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (27784987 / 62500000) ≤ -Real.log (500000000000 / 779901703549) ∧
    -Real.log (500000000000 / 779901703549) ≤ (444559793 / 1000000000) := by
  have h := checkLog_sound (w := (279901703549 / 1279901703549)) (n := 12)
    (lo := (27784987 / 62500000)) (hi := (444559793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779901703549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779901703549 / 500000000000) = 1/(500000000000 / 779901703549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27784987 / 62500000) (444559793 / 1000000000) (Real.log (779901703549 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (779901703549 / 500000000000) = -Real.log (500000000000 / 779901703549) := by
    rw [show ((779901703549 / 500000000000) : ℝ) = ((500000000000 / 779901703549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (445444169 / 1000000000) ≤ -Real.log (50000000000 / 78059173583) ∧
    -Real.log (50000000000 / 78059173583) ≤ (44544417 / 100000000) := by
  have h := checkLog_sound (w := (28059173583 / 128059173583)) (n := 12)
    (lo := (445444169 / 1000000000)) (hi := (44544417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78059173583 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78059173583 / 50000000000) = 1/(50000000000 / 78059173583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (445444169 / 1000000000) (44544417 / 100000000) (Real.log (78059173583 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (78059173583 / 50000000000) = -Real.log (50000000000 / 78059173583) := by
    rw [show ((78059173583 / 50000000000) : ℝ) = ((50000000000 / 78059173583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (15801617 / 50000000) ≤ -Real.log (62500000000 / 85729663483) ∧
    -Real.log (62500000000 / 85729663483) ≤ (316032341 / 1000000000) := by
  have h := checkLog_sound (w := (23229663483 / 148229663483)) (n := 12)
    (lo := (15801617 / 50000000)) (hi := (316032341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85729663483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85729663483 / 62500000000) = 1/(62500000000 / 85729663483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (15801617 / 50000000) (316032341 / 1000000000) (Real.log (85729663483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (85729663483 / 62500000000) = -Real.log (62500000000 / 85729663483) := by
    rw [show ((85729663483 / 62500000000) : ℝ) = ((62500000000 / 85729663483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (158333991 / 500000000) ≤ -Real.log (15625000000 / 21446043541) ∧
    -Real.log (15625000000 / 21446043541) ≤ (316667983 / 1000000000) := by
  have h := checkLog_sound (w := (5821043541 / 37071043541)) (n := 12)
    (lo := (158333991 / 500000000)) (hi := (316667983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21446043541 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21446043541 / 15625000000) = 1/(15625000000 / 21446043541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (158333991 / 500000000) (316667983 / 1000000000) (Real.log (21446043541 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21446043541 / 15625000000) = -Real.log (15625000000 / 21446043541) := by
    rw [show ((21446043541 / 15625000000) : ℝ) = ((15625000000 / 21446043541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24965599 / 1000000000) ≤ -Real.log (952483851 / 976562500) ∧
    -Real.log (952483851 / 976562500) ≤ (31207 / 1250000) := by
  have h := checkLog_sound (w := (24078649 / 1929046351)) (n := 12)
    (lo := (24965599 / 1000000000)) (hi := (31207 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 952483851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 952483851) = 1/(952483851 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31207 / 1250000) (-24965599 / 1000000000) (Real.log (952483851 / 976562500)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24865887 / 1000000000) ≤ -Real.log (243860180551 / 250000000000) ∧
    -Real.log (243860180551 / 250000000000) ≤ (777059 / 31250000) := by
  have h := checkLog_sound (w := (6139819449 / 493860180551)) (n := 12)
    (lo := (24865887 / 1000000000)) (hi := (777059 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243860180551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243860180551) = 1/(243860180551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-777059 / 31250000) (-24865887 / 1000000000) (Real.log (243860180551 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell099
