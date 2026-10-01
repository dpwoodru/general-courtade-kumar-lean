import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0475
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

theorem reflection_log_1_neg : (91465861 / 500000000) ≤ -Real.log (20480 / 24591) ∧
    -Real.log (20480 / 24591) ≤ (182931723 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 45071)) (n := 12)
    (lo := (91465861 / 500000000)) (hi := (182931723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24591 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24591 / 20480) = 1/(20480 / 24591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (91465861 / 500000000) (182931723 / 1000000000) (Real.log (24591 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24591 / 20480) = -Real.log (20480 / 24591) := by
    rw [show ((24591 / 20480) : ℝ) = ((20480 / 24591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112029749 / 500000000) ≤ -Real.log (16369 / 20480) ∧
    -Real.log (16369 / 20480) ≤ (224059499 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 36849)) (n := 12)
    (lo := (112029749 / 500000000)) (hi := (224059499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16369) = 1/(16369 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-224059499 / 1000000000) (-112029749 / 500000000) (Real.log (16369 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91404859 / 500000000) ≤ -Real.log (5120 / 6147) ∧
    -Real.log (5120 / 6147) ≤ (182809719 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 11267)) (n := 12)
    (lo := (91404859 / 500000000)) (hi := (182809719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6147 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6147 / 5120) = 1/(5120 / 6147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91404859 / 500000000) (182809719 / 1000000000) (Real.log (6147 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6147 / 5120) = -Real.log (5120 / 6147) := by
    rw [show ((6147 / 5120) : ℝ) = ((5120 / 6147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (223876241 / 1000000000) ≤ -Real.log (4093 / 5120) ∧
    -Real.log (4093 / 5120) ≤ (111938121 / 500000000) := by
  have h := checkLog_sound (w := (1027 / 9213)) (n := 12)
    (lo := (223876241 / 1000000000)) (hi := (111938121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4093) = 1/(4093 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111938121 / 500000000) (-223876241 / 1000000000) (Real.log (4093 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168759003 / 500000000) ≤ -Real.log (10240 / 14351) ∧
    -Real.log (10240 / 14351) ≤ (337518007 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 24591)) (n := 12)
    (lo := (168759003 / 500000000)) (hi := (337518007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14351 / 10240) = 1/(10240 / 14351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168759003 / 500000000) (337518007 / 1000000000) (Real.log (14351 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14351 / 10240) = -Real.log (10240 / 14351) := by
    rw [show ((14351 / 10240) : ℝ) = ((10240 / 14351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (102654003 / 200000000) ≤ -Real.log (6129 / 10240) ∧
    -Real.log (6129 / 10240) ≤ (2004961 / 3906250) := by
  have h := checkLog_sound (w := (4111 / 16369)) (n := 12)
    (lo := (102654003 / 200000000)) (hi := (2004961 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6129) = 1/(6129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2004961 / 3906250) (-102654003 / 200000000) (Real.log (6129 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16865447 / 50000000) ≤ -Real.log (2560 / 3587) ∧
    -Real.log (2560 / 3587) ≤ (337308941 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 6147)) (n := 12)
    (lo := (16865447 / 50000000)) (hi := (337308941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3587 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3587 / 2560) = 1/(2560 / 3587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16865447 / 50000000) (337308941 / 1000000000) (Real.log (3587 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3587 / 2560) = -Real.log (2560 / 3587) := by
    rw [show ((3587 / 2560) : ℝ) = ((2560 / 3587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256390329 / 500000000) ≤ -Real.log (1533 / 2560) ∧
    -Real.log (1533 / 2560) ≤ (512780659 / 1000000000) := by
  have h := checkLog_sound (w := (1027 / 4093)) (n := 12)
    (lo := (256390329 / 500000000)) (hi := (512780659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1533) = 1/(1533 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-512780659 / 1000000000) (-256390329 / 500000000) (Real.log (1533 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5026253 / 20000000) ≤ -Real.log (62500 / 80357) ∧
    -Real.log (62500 / 80357) ≤ (251312651 / 1000000000) := by
  have h := checkLog_sound (w := (17857 / 142857)) (n := 12)
    (lo := (5026253 / 20000000)) (hi := (251312651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80357 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80357 / 62500) = 1/(62500 / 80357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5026253 / 20000000) (251312651 / 1000000000) (Real.log (80357 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (80357 / 62500) = -Real.log (62500 / 80357) := by
    rw [show ((80357 / 62500) : ℝ) = ((62500 / 80357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84117259 / 250000000) ≤ -Real.log (44643 / 62500) ∧
    -Real.log (44643 / 62500) ≤ (336469037 / 1000000000) := by
  have h := checkLog_sound (w := (17857 / 107143)) (n := 12)
    (lo := (84117259 / 250000000)) (hi := (336469037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44643) = 1/(44643 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-336469037 / 1000000000) (-84117259 / 250000000) (Real.log (44643 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251478303 / 1000000000) ≤ -Real.log (40000 / 51437) ∧
    -Real.log (40000 / 51437) ≤ (7858697 / 31250000) := by
  have h := checkLog_sound (w := (11437 / 91437)) (n := 12)
    (lo := (251478303 / 1000000000)) (hi := (7858697 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51437 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51437 / 40000) = 1/(40000 / 51437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251478303 / 1000000000) (7858697 / 31250000) (Real.log (51437 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (51437 / 40000) = -Real.log (40000 / 51437) := by
    rw [show ((51437 / 40000) : ℝ) = ((40000 / 51437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4209591 / 12500000) ≤ -Real.log (28563 / 40000) ∧
    -Real.log (28563 / 40000) ≤ (336767281 / 1000000000) := by
  have h := checkLog_sound (w := (11437 / 68563)) (n := 12)
    (lo := (4209591 / 12500000)) (hi := (336767281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28563) = 1/(28563 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-336767281 / 1000000000) (-4209591 / 12500000) (Real.log (28563 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (187890189 / 1000000000) ≤ -Real.log (1000000 / 1206701) ∧
    -Real.log (1000000 / 1206701) ≤ (18789019 / 100000000) := by
  have h := checkLog_sound (w := (206701 / 2206701)) (n := 12)
    (lo := (187890189 / 1000000000)) (hi := (18789019 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206701 / 1000000) = 1/(1000000 / 1206701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (187890189 / 1000000000) (18789019 / 100000000) (Real.log (1206701 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1206701 / 1000000) = -Real.log (1000000 / 1206701) := by
    rw [show ((1206701 / 1000000) : ℝ) = ((1000000 / 1206701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231555079 / 1000000000) ≤ -Real.log (793299 / 1000000) ∧
    -Real.log (793299 / 1000000) ≤ (5788877 / 25000000) := by
  have h := checkLog_sound (w := (206701 / 1793299)) (n := 12)
    (lo := (231555079 / 1000000000)) (hi := (5788877 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793299) = 1/(793299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5788877 / 25000000) (-231555079 / 1000000000) (Real.log (793299 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188024431 / 1000000000) ≤ -Real.log (1000000 / 1206863) ∧
    -Real.log (1000000 / 1206863) ≤ (11751527 / 62500000) := by
  have h := checkLog_sound (w := (206863 / 2206863)) (n := 12)
    (lo := (188024431 / 1000000000)) (hi := (11751527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206863 / 1000000) = 1/(1000000 / 1206863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188024431 / 1000000000) (11751527 / 62500000) (Real.log (1206863 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1206863 / 1000000) = -Real.log (1000000 / 1206863) := by
    rw [show ((1206863 / 1000000) : ℝ) = ((1000000 / 1206863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23175931 / 100000000) ≤ -Real.log (793137 / 1000000) ∧
    -Real.log (793137 / 1000000) ≤ (231759311 / 1000000000) := by
  have h := checkLog_sound (w := (206863 / 1793137)) (n := 12)
    (lo := (23175931 / 100000000)) (hi := (231759311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793137) = 1/(793137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-231759311 / 1000000000) (-23175931 / 100000000) (Real.log (793137 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (587781687 / 1000000000) ≤ -Real.log (250000000000 / 449997760007) ∧
    -Real.log (250000000000 / 449997760007) ≤ (73472711 / 125000000) := by
  have h := checkLog_sound (w := (199997760007 / 699997760007)) (n := 12)
    (lo := (587781687 / 1000000000)) (hi := (73472711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449997760007 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449997760007 / 250000000000) = 1/(250000000000 / 449997760007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (587781687 / 1000000000) (73472711 / 125000000) (Real.log (449997760007 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (449997760007 / 250000000000) = -Real.log (250000000000 / 449997760007) := by
    rw [show ((449997760007 / 250000000000) : ℝ) = ((250000000000 / 449997760007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (588245583 / 1000000000) ≤ -Real.log (500000000000 / 900413121871) ∧
    -Real.log (500000000000 / 900413121871) ≤ (36765349 / 62500000) := by
  have h := checkLog_sound (w := (400413121871 / 1400413121871)) (n := 12)
    (lo := (588245583 / 1000000000)) (hi := (36765349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900413121871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900413121871 / 500000000000) = 1/(500000000000 / 900413121871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (588245583 / 1000000000) (36765349 / 62500000) (Real.log (900413121871 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (900413121871 / 500000000000) = -Real.log (500000000000 / 900413121871) := by
    rw [show ((900413121871 / 500000000000) : ℝ) = ((500000000000 / 900413121871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (419445269 / 1000000000) ≤ -Real.log (500000000000 / 760558755273) ∧
    -Real.log (500000000000 / 760558755273) ≤ (41944527 / 100000000) := by
  have h := checkLog_sound (w := (260558755273 / 1260558755273)) (n := 12)
    (lo := (419445269 / 1000000000)) (hi := (41944527 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760558755273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760558755273 / 500000000000) = 1/(500000000000 / 760558755273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (419445269 / 1000000000) (41944527 / 100000000) (Real.log (760558755273 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760558755273 / 500000000000) = -Real.log (500000000000 / 760558755273) := by
    rw [show ((760558755273 / 500000000000) : ℝ) = ((500000000000 / 760558755273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (419783741 / 1000000000) ≤ -Real.log (50000000000 / 76081622721) ∧
    -Real.log (50000000000 / 76081622721) ≤ (209891871 / 500000000) := by
  have h := checkLog_sound (w := (26081622721 / 126081622721)) (n := 12)
    (lo := (419783741 / 1000000000)) (hi := (209891871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76081622721 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76081622721 / 50000000000) = 1/(50000000000 / 76081622721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (419783741 / 1000000000) (209891871 / 500000000) (Real.log (76081622721 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76081622721 / 50000000000) = -Real.log (50000000000 / 76081622721) := by
    rw [show ((76081622721 / 50000000000) : ℝ) = ((50000000000 / 76081622721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0475
