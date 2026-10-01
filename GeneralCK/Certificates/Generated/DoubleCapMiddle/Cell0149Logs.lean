import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0149
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

theorem reflection_log_1_neg : (291386141 / 1000000000) ≤ -Real.log (1280 / 1713) ∧
    -Real.log (1280 / 1713) ≤ (145693071 / 500000000) := by
  have h := checkLog_sound (w := (433 / 2993)) (n := 12)
    (lo := (291386141 / 1000000000)) (hi := (145693071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1280) = 1/(1280 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291386141 / 1000000000) (145693071 / 500000000) (Real.log (1713 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1713 / 1280) = -Real.log (1280 / 1713) := by
    rw [show ((1713 / 1280) : ℝ) = ((1280 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (206457331 / 500000000) ≤ -Real.log (847 / 1280) ∧
    -Real.log (847 / 1280) ≤ (412914663 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2127)) (n := 12)
    (lo := (206457331 / 500000000)) (hi := (412914663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 847) = 1/(847 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-412914663 / 1000000000) (-206457331 / 500000000) (Real.log (847 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (290510101 / 1000000000) ≤ -Real.log (2560 / 3423) ∧
    -Real.log (2560 / 3423) ≤ (145255051 / 500000000) := by
  have h := checkLog_sound (w := (863 / 5983)) (n := 12)
    (lo := (290510101 / 1000000000)) (hi := (145255051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3423 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3423 / 2560) = 1/(2560 / 3423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (290510101 / 1000000000) (145255051 / 500000000) (Real.log (3423 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3423 / 2560) = -Real.log (2560 / 3423) := by
    rw [show ((3423 / 2560) : ℝ) = ((2560 / 3423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (51393159 / 125000000) ≤ -Real.log (1697 / 2560) ∧
    -Real.log (1697 / 2560) ≤ (411145273 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 4257)) (n := 12)
    (lo := (51393159 / 125000000)) (hi := (411145273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1697) = 1/(1697 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-411145273 / 1000000000) (-51393159 / 125000000) (Real.log (1697 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (258372783 / 500000000) ≤ -Real.log (640 / 1073) ∧
    -Real.log (640 / 1073) ≤ (516745567 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1713)) (n := 12)
    (lo := (258372783 / 500000000)) (hi := (516745567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1073 / 640) = 1/(640 / 1073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (258372783 / 500000000) (516745567 / 1000000000) (Real.log (1073 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1073 / 640) = -Real.log (640 / 1073) := by
    rw [show ((1073 / 640) : ℝ) = ((640 / 1073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (564374691 / 500000000) ≤ -Real.log (207 / 640) ∧
    -Real.log (207 / 640) ≤ (141093673 / 125000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 207) = 1/(207 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-141093673 / 125000000) (-564374691 / 500000000) (Real.log (207 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (257673319 / 500000000) ≤ -Real.log (1280 / 2143) ∧
    -Real.log (1280 / 2143) ≤ (515346639 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 3423)) (n := 12)
    (lo := (257673319 / 500000000)) (hi := (515346639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2143 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2143 / 1280) = 1/(1280 / 2143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (257673319 / 500000000) (515346639 / 1000000000) (Real.log (2143 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2143 / 1280) = -Real.log (1280 / 2143) := by
    rw [show ((2143 / 1280) : ℝ) = ((1280 / 2143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (560764567 / 500000000) ≤ -Real.log (417 / 1280) ∧
    -Real.log (417 / 1280) ≤ (70095571 / 62500000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 417) = 1/(417 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-70095571 / 62500000) (-560764567 / 500000000) (Real.log (417 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (198742341 / 500000000) ≤ -Real.log (1000000 / 1488077) ∧
    -Real.log (1000000 / 1488077) ≤ (397484683 / 1000000000) := by
  have h := checkLog_sound (w := (488077 / 2488077)) (n := 12)
    (lo := (198742341 / 500000000)) (hi := (397484683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1488077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1488077 / 1000000) = 1/(1000000 / 1488077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (198742341 / 500000000) (397484683 / 1000000000) (Real.log (1488077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1488077 / 1000000) = -Real.log (1000000 / 1488077) := by
    rw [show ((1488077 / 1000000) : ℝ) = ((1000000 / 1488077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133916211 / 200000000) ≤ -Real.log (511923 / 1000000) ∧
    -Real.log (511923 / 1000000) ≤ (2615551 / 3906250) := by
  have h := checkLog_sound (w := (488077 / 1511923)) (n := 12)
    (lo := (133916211 / 200000000)) (hi := (2615551 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 511923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 511923) = 1/(511923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2615551 / 3906250) (-133916211 / 200000000) (Real.log (511923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (199346783 / 500000000) ≤ -Real.log (1000000 / 1489877) ∧
    -Real.log (1000000 / 1489877) ≤ (398693567 / 1000000000) := by
  have h := checkLog_sound (w := (489877 / 2489877)) (n := 12)
    (lo := (199346783 / 500000000)) (hi := (398693567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489877 / 1000000) = 1/(1000000 / 1489877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (199346783 / 500000000) (398693567 / 1000000000) (Real.log (1489877 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1489877 / 1000000) = -Real.log (1000000 / 1489877) := by
    rw [show ((1489877 / 1000000) : ℝ) = ((1000000 / 1489877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (134620681 / 200000000) ≤ -Real.log (510123 / 1000000) ∧
    -Real.log (510123 / 1000000) ≤ (336551703 / 500000000) := by
  have h := checkLog_sound (w := (489877 / 1510123)) (n := 12)
    (lo := (134620681 / 200000000)) (hi := (336551703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 510123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 510123) = 1/(510123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336551703 / 500000000) (-134620681 / 200000000) (Real.log (510123 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (314373417 / 1000000000) ≤ -Real.log (1000000 / 1369401) ∧
    -Real.log (1000000 / 1369401) ≤ (157186709 / 500000000) := by
  have h := checkLog_sound (w := (369401 / 2369401)) (n := 12)
    (lo := (314373417 / 1000000000)) (hi := (157186709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369401 / 1000000) = 1/(1000000 / 1369401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (314373417 / 1000000000) (157186709 / 500000000) (Real.log (1369401 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1369401 / 1000000) = -Real.log (1000000 / 1369401) := by
    rw [show ((1369401 / 1000000) : ℝ) = ((1000000 / 1369401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (461085117 / 1000000000) ≤ -Real.log (630599 / 1000000) ∧
    -Real.log (630599 / 1000000) ≤ (230542559 / 500000000) := by
  have h := checkLog_sound (w := (369401 / 1630599)) (n := 12)
    (lo := (461085117 / 1000000000)) (hi := (230542559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 630599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 630599) = 1/(630599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-230542559 / 500000000) (-461085117 / 1000000000) (Real.log (630599 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (315507577 / 1000000000) ≤ -Real.log (200000 / 274191) ∧
    -Real.log (200000 / 274191) ≤ (157753789 / 500000000) := by
  have h := checkLog_sound (w := (74191 / 474191)) (n := 12)
    (lo := (315507577 / 1000000000)) (hi := (157753789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274191 / 200000) = 1/(200000 / 274191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (315507577 / 1000000000) (157753789 / 500000000) (Real.log (274191 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (274191 / 200000) = -Real.log (200000 / 274191) := by
    rw [show ((274191 / 200000) : ℝ) = ((200000 / 274191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231776241 / 500000000) ≤ -Real.log (125809 / 200000) ∧
    -Real.log (125809 / 200000) ≤ (463552483 / 1000000000) := by
  have h := checkLog_sound (w := (74191 / 325809)) (n := 12)
    (lo := (231776241 / 500000000)) (hi := (463552483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125809) = 1/(125809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-463552483 / 1000000000) (-231776241 / 500000000) (Real.log (125809 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1067065737 / 1000000000) ≤ -Real.log (50000000000 / 145341877587) ∧
    -Real.log (50000000000 / 145341877587) ≤ (1067065739 / 1000000000) := by
  have h := checkLog_sound (w := (45341877587 / 245341877587)) (n := 12)
    (lo := (373918557 / 1000000000)) (hi := (186959279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145341877587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145341877587 / 100000000000) = 1/(50000000000 / 145341877587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1067065737 / 1000000000) (1067065739 / 1000000000) (Real.log (145341877587 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (145341877587 / 50000000000) = -Real.log (50000000000 / 145341877587) := by
    rw [show ((145341877587 / 50000000000) : ℝ) = ((50000000000 / 145341877587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1071796971 / 1000000000) ≤ -Real.log (500000000000 / 1460311532709) ∧
    -Real.log (500000000000 / 1460311532709) ≤ (1071796973 / 1000000000) := by
  have h := checkLog_sound (w := (460311532709 / 2460311532709)) (n := 12)
    (lo := (378649791 / 1000000000)) (hi := (5916403 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1460311532709 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1460311532709 / 1000000000000) = 1/(500000000000 / 1460311532709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1071796971 / 1000000000) (1071796973 / 1000000000) (Real.log (1460311532709 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1460311532709 / 500000000000) = -Real.log (500000000000 / 1460311532709) := by
    rw [show ((1460311532709 / 500000000000) : ℝ) = ((500000000000 / 1460311532709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (155091707 / 200000000) ≤ -Real.log (500000000000 / 1085793824601) ∧
    -Real.log (500000000000 / 1085793824601) ≤ (775458537 / 1000000000) := by
  have h := checkLog_sound (w := (85793824601 / 2085793824601)) (n := 12)
    (lo := (16462271 / 200000000)) (hi := (20577839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085793824601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1085793824601 / 1000000000000) = 1/(500000000000 / 1085793824601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (155091707 / 200000000) (775458537 / 1000000000) (Real.log (1085793824601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1085793824601 / 500000000000) = -Real.log (500000000000 / 1085793824601) := by
    rw [show ((1085793824601 / 500000000000) : ℝ) = ((500000000000 / 1085793824601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (779060059 / 1000000000) ≤ -Real.log (250000000000 / 544855693949) ∧
    -Real.log (250000000000 / 544855693949) ≤ (779060061 / 1000000000) := by
  have h := checkLog_sound (w := (44855693949 / 1044855693949)) (n := 12)
    (lo := (85912879 / 1000000000)) (hi := (1073911 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544855693949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(544855693949 / 500000000000) = 1/(250000000000 / 544855693949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (779060059 / 1000000000) (779060061 / 1000000000) (Real.log (544855693949 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (544855693949 / 250000000000) = -Real.log (250000000000 / 544855693949) := by
    rw [show ((544855693949 / 250000000000) : ℝ) = ((250000000000 / 544855693949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0149
