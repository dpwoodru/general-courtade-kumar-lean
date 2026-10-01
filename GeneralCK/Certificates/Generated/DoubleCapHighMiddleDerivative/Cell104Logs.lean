import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell104
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

theorem reflection_log_1_neg : (27118939 / 100000000) ≤ -Real.log (1024 / 1343) ∧
    -Real.log (1024 / 1343) ≤ (271189391 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 2367)) (n := 12)
    (lo := (27118939 / 100000000)) (hi := (271189391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343 / 1024) = 1/(1024 / 1343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27118939 / 100000000) (271189391 / 1000000000) (Real.log (1343 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1343 / 1024) = -Real.log (1024 / 1343) := by
    rw [show ((1343 / 1024) : ℝ) = ((1024 / 1343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (186637001 / 500000000) ≤ -Real.log (705 / 1024) ∧
    -Real.log (705 / 1024) ≤ (373274003 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1729)) (n := 12)
    (lo := (186637001 / 500000000)) (hi := (373274003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 705) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 705) = 1/(705 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-373274003 / 1000000000) (-186637001 / 500000000) (Real.log (705 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27074253 / 100000000) ≤ -Real.log (640 / 839) ∧
    -Real.log (640 / 839) ≤ (270742531 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1479)) (n := 12)
    (lo := (27074253 / 100000000)) (hi := (270742531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839 / 640) = 1/(640 / 839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27074253 / 100000000) (270742531 / 1000000000) (Real.log (839 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (839 / 640) = -Real.log (640 / 839) := by
    rw [show ((839 / 640) : ℝ) = ((640 / 839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3724233 / 10000000) ≤ -Real.log (441 / 640) ∧
    -Real.log (441 / 640) ≤ (372423301 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 441) = 1/(441 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-372423301 / 1000000000) (-3724233 / 10000000) (Real.log (441 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199497371 / 1000000000) ≤ -Real.log (1000000 / 1220789) ∧
    -Real.log (1000000 / 1220789) ≤ (49874343 / 250000000) := by
  have h := checkLog_sound (w := (220789 / 2220789)) (n := 12)
    (lo := (199497371 / 1000000000)) (hi := (49874343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220789 / 1000000) = 1/(1000000 / 1220789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199497371 / 1000000000) (49874343 / 250000000) (Real.log (1220789 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1220789 / 1000000) = -Real.log (1000000 / 1220789) := by
    rw [show ((1220789 / 1000000) : ℝ) = ((1000000 / 1220789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (249473409 / 1000000000) ≤ -Real.log (779211 / 1000000) ∧
    -Real.log (779211 / 1000000) ≤ (24947341 / 100000000) := by
  have h := checkLog_sound (w := (220789 / 1779211)) (n := 12)
    (lo := (249473409 / 1000000000)) (hi := (24947341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779211) = 1/(779211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24947341 / 100000000) (-249473409 / 1000000000) (Real.log (779211 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199841351 / 1000000000) ≤ -Real.log (1000000 / 1221209) ∧
    -Real.log (1000000 / 1221209) ≤ (24980169 / 125000000) := by
  have h := checkLog_sound (w := (221209 / 2221209)) (n := 12)
    (lo := (199841351 / 1000000000)) (hi := (24980169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221209 / 1000000) = 1/(1000000 / 1221209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199841351 / 1000000000) (24980169 / 125000000) (Real.log (1221209 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1221209 / 1000000) = -Real.log (1000000 / 1221209) := by
    rw [show ((1221209 / 1000000) : ℝ) = ((1000000 / 1221209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (250012561 / 1000000000) ≤ -Real.log (778791 / 1000000) ∧
    -Real.log (778791 / 1000000) ≤ (125006281 / 500000000) := by
  have h := checkLog_sound (w := (221209 / 1778791)) (n := 12)
    (lo := (250012561 / 1000000000)) (hi := (125006281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778791) = 1/(778791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-125006281 / 500000000) (-250012561 / 1000000000) (Real.log (778791 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29383603 / 200000000) ≤ -Real.log (1000000 / 1158259) ∧
    -Real.log (1000000 / 1158259) ≤ (1147797 / 7812500) := by
  have h := checkLog_sound (w := (158259 / 2158259)) (n := 12)
    (lo := (29383603 / 200000000)) (hi := (1147797 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158259 / 1000000) = 1/(1000000 / 1158259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29383603 / 200000000) (1147797 / 7812500) (Real.log (1158259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1158259 / 1000000) = -Real.log (1000000 / 1158259) := by
    rw [show ((1158259 / 1000000) : ℝ) = ((1000000 / 1158259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (172282913 / 1000000000) ≤ -Real.log (841741 / 1000000) ∧
    -Real.log (841741 / 1000000) ≤ (86141457 / 500000000) := by
  have h := checkLog_sound (w := (158259 / 1841741)) (n := 12)
    (lo := (172282913 / 1000000000)) (hi := (86141457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841741) = 1/(841741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86141457 / 500000000) (-172282913 / 1000000000) (Real.log (841741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73592811 / 500000000) ≤ -Real.log (1000000 / 1158569) ∧
    -Real.log (1000000 / 1158569) ≤ (147185623 / 1000000000) := by
  have h := checkLog_sound (w := (158569 / 2158569)) (n := 12)
    (lo := (73592811 / 500000000)) (hi := (147185623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158569 / 1000000) = 1/(1000000 / 1158569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73592811 / 500000000) (147185623 / 1000000000) (Real.log (1158569 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1158569 / 1000000) = -Real.log (1000000 / 1158569) := by
    rw [show ((1158569 / 1000000) : ℝ) = ((1000000 / 1158569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (34530253 / 200000000) ≤ -Real.log (841431 / 1000000) ∧
    -Real.log (841431 / 1000000) ≤ (86325633 / 500000000) := by
  have h := checkLog_sound (w := (158569 / 1841431)) (n := 12)
    (lo := (34530253 / 200000000)) (hi := (86325633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841431) = 1/(841431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86325633 / 500000000) (-34530253 / 200000000) (Real.log (841431 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (643165831 / 1000000000) ≤ -Real.log (125000000000 / 237811791383) ∧
    -Real.log (125000000000 / 237811791383) ≤ (80395729 / 125000000) := by
  have h := checkLog_sound (w := (112811791383 / 362811791383)) (n := 12)
    (lo := (643165831 / 1000000000)) (hi := (80395729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237811791383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237811791383 / 125000000000) = 1/(125000000000 / 237811791383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (643165831 / 1000000000) (80395729 / 125000000) (Real.log (237811791383 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (237811791383 / 125000000000) = -Real.log (125000000000 / 237811791383) := by
    rw [show ((237811791383 / 125000000000) : ℝ) = ((125000000000 / 237811791383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (644463393 / 1000000000) ≤ -Real.log (7812500000 / 14882535461) ∧
    -Real.log (7812500000 / 14882535461) ≤ (322231697 / 500000000) := by
  have h := checkLog_sound (w := (7070035461 / 22695035461)) (n := 12)
    (lo := (644463393 / 1000000000)) (hi := (322231697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14882535461 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14882535461 / 7812500000) = 1/(7812500000 / 14882535461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (644463393 / 1000000000) (322231697 / 500000000) (Real.log (14882535461 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (14882535461 / 7812500000) = -Real.log (7812500000 / 14882535461) := by
    rw [show ((14882535461 / 7812500000) : ℝ) = ((7812500000 / 14882535461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22448539 / 50000000) ≤ -Real.log (62500000000 / 97918679921) ∧
    -Real.log (62500000000 / 97918679921) ≤ (448970781 / 1000000000) := by
  have h := checkLog_sound (w := (35418679921 / 160418679921)) (n := 12)
    (lo := (22448539 / 50000000)) (hi := (448970781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97918679921 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97918679921 / 62500000000) = 1/(62500000000 / 97918679921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22448539 / 50000000) (448970781 / 1000000000) (Real.log (97918679921 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (97918679921 / 62500000000) = -Real.log (62500000000 / 97918679921) := by
    rw [show ((97918679921 / 62500000000) : ℝ) = ((62500000000 / 97918679921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (449853913 / 1000000000) ≤ -Real.log (500000000000 / 784041546449) ∧
    -Real.log (500000000000 / 784041546449) ≤ (224926957 / 500000000) := by
  have h := checkLog_sound (w := (284041546449 / 1284041546449)) (n := 12)
    (lo := (449853913 / 1000000000)) (hi := (224926957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784041546449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784041546449 / 500000000000) = 1/(500000000000 / 784041546449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (449853913 / 1000000000) (224926957 / 500000000) (Real.log (784041546449 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (784041546449 / 500000000000) = -Real.log (500000000000 / 784041546449) := by
    rw [show ((784041546449 / 500000000000) : ℝ) = ((500000000000 / 784041546449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9975029 / 31250000) ≤ -Real.log (250000000000 / 344006945129) ∧
    -Real.log (250000000000 / 344006945129) ≤ (319200929 / 1000000000) := by
  have h := checkLog_sound (w := (94006945129 / 594006945129)) (n := 12)
    (lo := (9975029 / 31250000)) (hi := (319200929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344006945129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344006945129 / 250000000000) = 1/(250000000000 / 344006945129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9975029 / 31250000) (319200929 / 1000000000) (Real.log (344006945129 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (344006945129 / 250000000000) = -Real.log (250000000000 / 344006945129) := by
    rw [show ((344006945129 / 250000000000) : ℝ) = ((250000000000 / 344006945129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39979611 / 125000000) ≤ -Real.log (125000000000 / 172112894581) ∧
    -Real.log (125000000000 / 172112894581) ≤ (319836889 / 1000000000) := by
  have h := checkLog_sound (w := (47112894581 / 297112894581)) (n := 12)
    (lo := (39979611 / 125000000)) (hi := (319836889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172112894581 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172112894581 / 125000000000) = 1/(125000000000 / 172112894581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39979611 / 125000000) (319836889 / 1000000000) (Real.log (172112894581 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172112894581 / 125000000000) = -Real.log (125000000000 / 172112894581) := by
    rw [show ((172112894581 / 125000000000) : ℝ) = ((125000000000 / 172112894581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (12732821 / 500000000) ≤ -Real.log (974855872239 / 1000000000000) ∧
    -Real.log (974855872239 / 1000000000000) ≤ (25465643 / 1000000000) := by
  have h := checkLog_sound (w := (25144127761 / 1974855872239)) (n := 12)
    (lo := (12732821 / 500000000)) (hi := (25465643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974855872239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974855872239) = 1/(974855872239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25465643 / 1000000000) (-12732821 / 500000000) (Real.log (974855872239 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25364897 / 1000000000) ≤ -Real.log (974954088919 / 1000000000000) ∧
    -Real.log (974954088919 / 1000000000000) ≤ (12682449 / 500000000) := by
  have h := checkLog_sound (w := (25045911081 / 1974954088919)) (n := 12)
    (lo := (25364897 / 1000000000)) (hi := (12682449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974954088919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974954088919) = 1/(974954088919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-12682449 / 500000000) (-25364897 / 1000000000) (Real.log (974954088919 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell104
