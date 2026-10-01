import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0094
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

theorem reflection_log_1_neg : (10575733 / 31250000) ≤ -Real.log (2560 / 3591) ∧
    -Real.log (2560 / 3591) ≤ (338423457 / 1000000000) := by
  have h := checkLog_sound (w := (1031 / 6151)) (n := 12)
    (lo := (10575733 / 31250000)) (hi := (338423457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3591 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3591 / 2560) = 1/(2560 / 3591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10575733 / 31250000) (338423457 / 1000000000) (Real.log (3591 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3591 / 2560) = -Real.log (2560 / 3591) := by
    rw [show ((3591 / 2560) : ℝ) = ((2560 / 3591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (515393331 / 1000000000) ≤ -Real.log (1529 / 2560) ∧
    -Real.log (1529 / 2560) ≤ (128848333 / 250000000) := by
  have h := checkLog_sound (w := (1031 / 4089)) (n := 12)
    (lo := (515393331 / 1000000000)) (hi := (128848333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1529) = 1/(1529 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-128848333 / 250000000) (-515393331 / 1000000000) (Real.log (1529 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67517537 / 200000000) ≤ -Real.log (640 / 897) ∧
    -Real.log (640 / 897) ≤ (168793843 / 500000000) := by
  have h := checkLog_sound (w := (257 / 1537)) (n := 12)
    (lo := (67517537 / 200000000)) (hi := (168793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897 / 640) = 1/(640 / 897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67517537 / 200000000) (168793843 / 500000000) (Real.log (897 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (897 / 640) = -Real.log (640 / 897) := by
    rw [show ((897 / 640) : ℝ) = ((640 / 897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (513433187 / 1000000000) ≤ -Real.log (383 / 640) ∧
    -Real.log (383 / 640) ≤ (128358297 / 250000000) := by
  have h := checkLog_sound (w := (257 / 1023)) (n := 12)
    (lo := (513433187 / 1000000000)) (hi := (128358297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 383) = 1/(383 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-128358297 / 250000000) (-513433187 / 1000000000) (Real.log (383 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (590820253 / 1000000000) ≤ -Real.log (1280 / 2311) ∧
    -Real.log (1280 / 2311) ≤ (295410127 / 500000000) := by
  have h := checkLog_sound (w := (1031 / 3591)) (n := 12)
    (lo := (590820253 / 1000000000)) (hi := (295410127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 1280) = 1/(1280 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (590820253 / 1000000000) (295410127 / 500000000) (Real.log (2311 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2311 / 1280) = -Real.log (1280 / 2311) := by
    rw [show ((2311 / 1280) : ℝ) = ((1280 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1637162459 / 1000000000) ≤ -Real.log (249 / 1280) ∧
    -Real.log (249 / 1280) ≤ (818581231 / 500000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 249) = 1/(249 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-818581231 / 500000000) (-1637162459 / 1000000000) (Real.log (249 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (58952127 / 100000000) ≤ -Real.log (320 / 577) ∧
    -Real.log (320 / 577) ≤ (589521271 / 1000000000) := by
  have h := checkLog_sound (w := (257 / 897)) (n := 12)
    (lo := (58952127 / 100000000)) (hi := (589521271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577 / 320) = 1/(320 / 577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (58952127 / 100000000) (589521271 / 1000000000) (Real.log (577 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (577 / 320) = -Real.log (320 / 577) := by
    rw [show ((577 / 320) : ℝ) = ((320 / 577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (406296567 / 250000000) ≤ -Real.log (63 / 320) ∧
    -Real.log (63 / 320) ≤ (1625186271 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 63) = 1/(63 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1625186271 / 1000000000) (-406296567 / 250000000) (Real.log (63 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (231804111 / 500000000) ≤ -Real.log (5000 / 7949) ∧
    -Real.log (5000 / 7949) ≤ (463608223 / 1000000000) := by
  have h := checkLog_sound (w := (2949 / 12949)) (n := 12)
    (lo := (231804111 / 500000000)) (hi := (463608223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7949 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7949 / 5000) = 1/(5000 / 7949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (231804111 / 500000000) (463608223 / 1000000000) (Real.log (7949 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (7949 / 5000) = -Real.log (5000 / 7949) := by
    rw [show ((7949 / 5000) : ℝ) = ((5000 / 7949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (27847201 / 31250000) ≤ -Real.log (2051 / 5000) ∧
    -Real.log (2051 / 5000) ≤ (445555217 / 500000000) := by
  have h := checkLog_sound (w := (449 / 4551)) (n := 12)
    (lo := (49490813 / 250000000)) (hi := (197963253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2051) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2500 / 2051) = 1/(2051 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-445555217 / 500000000) (-27847201 / 31250000) (Real.log (2051 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29050871 / 62500000) ≤ -Real.log (500000 / 795859) ∧
    -Real.log (500000 / 795859) ≤ (464813937 / 1000000000) := by
  have h := checkLog_sound (w := (295859 / 1295859)) (n := 12)
    (lo := (29050871 / 62500000)) (hi := (464813937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795859 / 500000) = 1/(500000 / 795859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29050871 / 62500000) (464813937 / 1000000000) (Real.log (795859 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (795859 / 500000) = -Real.log (500000 / 795859) := by
    rw [show ((795859 / 500000) : ℝ) = ((500000 / 795859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (447898583 / 500000000) ≤ -Real.log (204141 / 500000) ∧
    -Real.log (204141 / 500000) ≤ (55987323 / 62500000) := by
  have h := checkLog_sound (w := (45859 / 454141)) (n := 12)
    (lo := (101324993 / 500000000)) (hi := (202649987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 204141) = 1/(204141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55987323 / 62500000) (-447898583 / 500000000) (Real.log (204141 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (379224481 / 1000000000) ≤ -Real.log (1000000 / 1461151) ∧
    -Real.log (1000000 / 1461151) ≤ (189612241 / 500000000) := by
  have h := checkLog_sound (w := (461151 / 2461151)) (n := 12)
    (lo := (379224481 / 1000000000)) (hi := (189612241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461151 / 1000000) = 1/(1000000 / 1461151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (379224481 / 1000000000) (189612241 / 500000000) (Real.log (1461151 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1461151 / 1000000) = -Real.log (1000000 / 1461151) := by
    rw [show ((1461151 / 1000000) : ℝ) = ((1000000 / 1461151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (123663979 / 200000000) ≤ -Real.log (538849 / 1000000) ∧
    -Real.log (538849 / 1000000) ≤ (77289987 / 125000000) := by
  have h := checkLog_sound (w := (461151 / 1538849)) (n := 12)
    (lo := (123663979 / 200000000)) (hi := (77289987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 538849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 538849) = 1/(538849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-77289987 / 125000000) (-123663979 / 200000000) (Real.log (538849 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (380465881 / 1000000000) ≤ -Real.log (500000 / 731483) ∧
    -Real.log (500000 / 731483) ≤ (190232941 / 500000000) := by
  have h := checkLog_sound (w := (231483 / 1231483)) (n := 12)
    (lo := (380465881 / 1000000000)) (hi := (190232941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((731483 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(731483 / 500000) = 1/(500000 / 731483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (380465881 / 1000000000) (190232941 / 500000000) (Real.log (731483 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (731483 / 500000) = -Real.log (500000 / 731483) := by
    rw [show ((731483 / 500000) : ℝ) = ((500000 / 731483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (621693871 / 1000000000) ≤ -Real.log (268517 / 500000) ∧
    -Real.log (268517 / 500000) ≤ (38855867 / 62500000) := by
  have h := checkLog_sound (w := (231483 / 768517)) (n := 12)
    (lo := (621693871 / 1000000000)) (hi := (38855867 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 268517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 268517) = 1/(268517 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-38855867 / 62500000) (-621693871 / 1000000000) (Real.log (268517 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (677359327 / 500000000) ≤ -Real.log (25000000000 / 96891760117) ∧
    -Real.log (25000000000 / 96891760117) ≤ (21167479 / 15625000) := by
  have h := checkLog_sound (w := (46891760117 / 146891760117)) (n := 12)
    (lo := (330785737 / 500000000)) (hi := (26462859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96891760117 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96891760117 / 50000000000) = 1/(25000000000 / 96891760117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (677359327 / 500000000) (21167479 / 15625000) (Real.log (96891760117 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (96891760117 / 25000000000) = -Real.log (25000000000 / 96891760117) := by
    rw [show ((96891760117 / 25000000000) : ℝ) = ((25000000000 / 96891760117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (680305551 / 500000000) ≤ -Real.log (250000000000 / 974643751133) ∧
    -Real.log (250000000000 / 974643751133) ≤ (42519097 / 31250000) := by
  have h := checkLog_sound (w := (474643751133 / 1474643751133)) (n := 12)
    (lo := (333731961 / 500000000)) (hi := (667463923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974643751133 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(974643751133 / 500000000000) = 1/(250000000000 / 974643751133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (680305551 / 500000000) (42519097 / 31250000) (Real.log (974643751133 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (974643751133 / 250000000000) = -Real.log (250000000000 / 974643751133) := by
    rw [show ((974643751133 / 250000000000) : ℝ) = ((250000000000 / 974643751133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (124693047 / 125000000) ≤ -Real.log (500000000000 / 1355807471109) ∧
    -Real.log (500000000000 / 1355807471109) ≤ (498772189 / 500000000) := by
  have h := checkLog_sound (w := (355807471109 / 2355807471109)) (n := 12)
    (lo := (76099299 / 250000000)) (hi := (304397197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355807471109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1355807471109 / 1000000000000) = 1/(500000000000 / 1355807471109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (124693047 / 125000000) (498772189 / 500000000) (Real.log (1355807471109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1355807471109 / 500000000000) = -Real.log (500000000000 / 1355807471109) := by
    rw [show ((1355807471109 / 500000000000) : ℝ) = ((500000000000 / 1355807471109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1002159753 / 1000000000) ≤ -Real.log (250000000000 / 681039747949) ∧
    -Real.log (250000000000 / 681039747949) ≤ (200431951 / 200000000) := by
  have h := checkLog_sound (w := (181039747949 / 1181039747949)) (n := 12)
    (lo := (309012573 / 1000000000)) (hi := (154506287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681039747949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(681039747949 / 500000000000) = 1/(250000000000 / 681039747949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1002159753 / 1000000000) (200431951 / 200000000) (Real.log (681039747949 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (681039747949 / 250000000000) = -Real.log (250000000000 / 681039747949) := by
    rw [show ((681039747949 / 250000000000) : ℝ) = ((250000000000 / 681039747949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0094
