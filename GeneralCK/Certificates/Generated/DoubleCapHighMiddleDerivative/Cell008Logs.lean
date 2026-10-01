import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell008
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

theorem reflection_log_1_neg : (227353427 / 1000000000) ≤ -Real.log (5120 / 6427) ∧
    -Real.log (5120 / 6427) ≤ (56838357 / 250000000) := by
  have h := checkLog_sound (w := (1307 / 11547)) (n := 12)
    (lo := (227353427 / 1000000000)) (hi := (56838357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427 / 5120) = 1/(5120 / 6427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227353427 / 1000000000) (56838357 / 250000000) (Real.log (6427 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6427 / 5120) = -Real.log (5120 / 6427) := by
    rw [show ((6427 / 5120) : ℝ) = ((5120 / 6427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (147369079 / 500000000) ≤ -Real.log (3813 / 5120) ∧
    -Real.log (3813 / 5120) ≤ (294738159 / 1000000000) := by
  have h := checkLog_sound (w := (1307 / 8933)) (n := 12)
    (lo := (147369079 / 500000000)) (hi := (294738159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3813) = 1/(3813 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-294738159 / 1000000000) (-147369079 / 500000000) (Real.log (3813 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226886537 / 1000000000) ≤ -Real.log (640 / 803) ∧
    -Real.log (640 / 803) ≤ (113443269 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1443)) (n := 12)
    (lo := (226886537 / 1000000000)) (hi := (113443269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803 / 640) = 1/(640 / 803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226886537 / 1000000000) (113443269 / 500000000) (Real.log (803 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (803 / 640) = -Real.log (640 / 803) := by
    rw [show ((803 / 640) : ℝ) = ((640 / 803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58790337 / 200000000) ≤ -Real.log (477 / 640) ∧
    -Real.log (477 / 640) ≤ (146975843 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 477) = 1/(477 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-146975843 / 500000000) (-58790337 / 200000000) (Real.log (477 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4150379 / 25000000) ≤ -Real.log (1000000 / 1180591) ∧
    -Real.log (1000000 / 1180591) ≤ (166015161 / 1000000000) := by
  have h := checkLog_sound (w := (180591 / 2180591)) (n := 12)
    (lo := (4150379 / 25000000)) (hi := (166015161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180591 / 1000000) = 1/(1000000 / 1180591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4150379 / 25000000) (166015161 / 1000000000) (Real.log (1180591 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1180591 / 1000000) = -Real.log (1000000 / 1180591) := by
    rw [show ((1180591 / 1000000) : ℝ) = ((1000000 / 1180591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (19917193 / 100000000) ≤ -Real.log (819409 / 1000000) ∧
    -Real.log (819409 / 1000000) ≤ (199171931 / 1000000000) := by
  have h := checkLog_sound (w := (180591 / 1819409)) (n := 12)
    (lo := (19917193 / 100000000)) (hi := (199171931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819409) = 1/(819409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-199171931 / 1000000000) (-19917193 / 100000000) (Real.log (819409 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41592501 / 250000000) ≤ -Real.log (100000 / 118101) ∧
    -Real.log (100000 / 118101) ≤ (33274001 / 200000000) := by
  have h := checkLog_sound (w := (18101 / 218101)) (n := 12)
    (lo := (41592501 / 250000000)) (hi := (33274001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118101 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118101 / 100000) = 1/(100000 / 118101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41592501 / 250000000) (33274001 / 200000000) (Real.log (118101 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (118101 / 100000) = -Real.log (100000 / 118101) := by
    rw [show ((118101 / 100000) : ℝ) = ((100000 / 118101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39936681 / 200000000) ≤ -Real.log (81899 / 100000) ∧
    -Real.log (81899 / 100000) ≤ (99841703 / 500000000) := by
  have h := checkLog_sound (w := (18101 / 181899)) (n := 12)
    (lo := (39936681 / 200000000)) (hi := (99841703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81899) = 1/(81899 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-99841703 / 500000000) (-39936681 / 200000000) (Real.log (81899 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (24242009 / 200000000) ≤ -Real.log (500000 / 564431) ∧
    -Real.log (500000 / 564431) ≤ (60605023 / 500000000) := by
  have h := checkLog_sound (w := (64431 / 1064431)) (n := 12)
    (lo := (24242009 / 200000000)) (hi := (60605023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564431 / 500000) = 1/(500000 / 564431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (24242009 / 200000000) (60605023 / 500000000) (Real.log (564431 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (564431 / 500000) = -Real.log (500000 / 564431) := by
    rw [show ((564431 / 500000) : ℝ) = ((500000 / 564431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (34488719 / 250000000) ≤ -Real.log (435569 / 500000) ∧
    -Real.log (435569 / 500000) ≤ (137954877 / 1000000000) := by
  have h := checkLog_sound (w := (64431 / 935569)) (n := 12)
    (lo := (34488719 / 250000000)) (hi := (137954877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435569) = 1/(435569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-137954877 / 1000000000) (-34488719 / 250000000) (Real.log (435569 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121479307 / 1000000000) ≤ -Real.log (500000 / 564583) ∧
    -Real.log (500000 / 564583) ≤ (30369827 / 250000000) := by
  have h := checkLog_sound (w := (64583 / 1064583)) (n := 12)
    (lo := (121479307 / 1000000000)) (hi := (30369827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564583 / 500000) = 1/(500000 / 564583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121479307 / 1000000000) (30369827 / 250000000) (Real.log (564583 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (564583 / 500000) = -Real.log (500000 / 564583) := by
    rw [show ((564583 / 500000) : ℝ) = ((500000 / 564583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27660781 / 200000000) ≤ -Real.log (435417 / 500000) ∧
    -Real.log (435417 / 500000) ≤ (69151953 / 500000000) := by
  have h := checkLog_sound (w := (64583 / 935417)) (n := 12)
    (lo := (27660781 / 200000000)) (hi := (69151953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435417) = 1/(435417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69151953 / 500000000) (-27660781 / 200000000) (Real.log (435417 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (520838223 / 1000000000) ≤ -Real.log (7812500000 / 13151860587) ∧
    -Real.log (7812500000 / 13151860587) ≤ (32552389 / 62500000) := by
  have h := checkLog_sound (w := (5339360587 / 20964360587)) (n := 12)
    (lo := (520838223 / 1000000000)) (hi := (32552389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13151860587 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13151860587 / 7812500000) = 1/(7812500000 / 13151860587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (520838223 / 1000000000) (32552389 / 62500000) (Real.log (13151860587 / 7812500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (13151860587 / 7812500000) = -Real.log (7812500000 / 13151860587) := by
    rw [show ((13151860587 / 7812500000) : ℝ) = ((7812500000 / 13151860587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (104418317 / 200000000) ≤ -Real.log (50000000000 / 84277471807) ∧
    -Real.log (50000000000 / 84277471807) ≤ (261045793 / 500000000) := by
  have h := checkLog_sound (w := (34277471807 / 134277471807)) (n := 12)
    (lo := (104418317 / 200000000)) (hi := (261045793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84277471807 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84277471807 / 50000000000) = 1/(50000000000 / 84277471807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (104418317 / 200000000) (261045793 / 500000000) (Real.log (84277471807 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (84277471807 / 50000000000) = -Real.log (50000000000 / 84277471807) := by
    rw [show ((84277471807 / 50000000000) : ℝ) = ((50000000000 / 84277471807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (36518709 / 100000000) ≤ -Real.log (250000000000 / 360195885083) ∧
    -Real.log (250000000000 / 360195885083) ≤ (365187091 / 1000000000) := by
  have h := checkLog_sound (w := (110195885083 / 610195885083)) (n := 12)
    (lo := (36518709 / 100000000)) (hi := (365187091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360195885083 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360195885083 / 250000000000) = 1/(250000000000 / 360195885083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (36518709 / 100000000) (365187091 / 1000000000) (Real.log (360195885083 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (360195885083 / 250000000000) = -Real.log (250000000000 / 360195885083) := by
    rw [show ((360195885083 / 250000000000) : ℝ) = ((250000000000 / 360195885083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (366053409 / 1000000000) ≤ -Real.log (62500000000 / 90127016203) ∧
    -Real.log (62500000000 / 90127016203) ≤ (36605341 / 100000000) := by
  have h := checkLog_sound (w := (27627016203 / 152627016203)) (n := 12)
    (lo := (366053409 / 1000000000)) (hi := (36605341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90127016203 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90127016203 / 62500000000) = 1/(62500000000 / 90127016203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (366053409 / 1000000000) (36605341 / 100000000) (Real.log (90127016203 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (90127016203 / 62500000000) = -Real.log (62500000000 / 90127016203) := by
    rw [show ((90127016203 / 62500000000) : ℝ) = ((62500000000 / 90127016203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (259164921 / 1000000000) ≤ -Real.log (62500000000 / 80990468789) ∧
    -Real.log (62500000000 / 80990468789) ≤ (129582461 / 500000000) := by
  have h := checkLog_sound (w := (18490468789 / 143490468789)) (n := 12)
    (lo := (259164921 / 1000000000)) (hi := (129582461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80990468789 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80990468789 / 62500000000) = 1/(62500000000 / 80990468789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (259164921 / 1000000000) (129582461 / 500000000) (Real.log (80990468789 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (80990468789 / 62500000000) = -Real.log (62500000000 / 80990468789) := by
    rw [show ((80990468789 / 62500000000) : ℝ) = ((62500000000 / 80990468789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64945803 / 250000000) ≤ -Real.log (62500000000 / 81040559969) ∧
    -Real.log (62500000000 / 81040559969) ≤ (259783213 / 1000000000) := by
  have h := checkLog_sound (w := (18540559969 / 143540559969)) (n := 12)
    (lo := (64945803 / 250000000)) (hi := (259783213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81040559969 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81040559969 / 62500000000) = 1/(62500000000 / 81040559969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64945803 / 250000000) (259783213 / 1000000000) (Real.log (81040559969 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (81040559969 / 62500000000) = -Real.log (62500000000 / 81040559969) := by
    rw [show ((81040559969 / 62500000000) : ℝ) = ((62500000000 / 81040559969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8412299 / 500000000) ≤ -Real.log (245829036111 / 250000000000) ∧
    -Real.log (245829036111 / 250000000000) ≤ (16824599 / 1000000000) := by
  have h := checkLog_sound (w := (4170963889 / 495829036111)) (n := 12)
    (lo := (8412299 / 500000000)) (hi := (16824599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245829036111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245829036111) = 1/(245829036111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16824599 / 1000000000) (-8412299 / 500000000) (Real.log (245829036111 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1674483 / 100000000) ≤ -Real.log (245848646239 / 250000000000) ∧
    -Real.log (245848646239 / 250000000000) ≤ (16744831 / 1000000000) := by
  have h := checkLog_sound (w := (4151353761 / 495848646239)) (n := 12)
    (lo := (1674483 / 100000000)) (hi := (16744831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245848646239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245848646239) = 1/(245848646239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16744831 / 1000000000) (-1674483 / 100000000) (Real.log (245848646239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell008
