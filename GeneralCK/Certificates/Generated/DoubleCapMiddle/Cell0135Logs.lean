import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0135
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

theorem reflection_log_1_neg : (758927 / 2500000) ≤ -Real.log (640 / 867) ∧
    -Real.log (640 / 867) ≤ (303570801 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1507)) (n := 12)
    (lo := (758927 / 2500000)) (hi := (303570801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867 / 640) = 1/(640 / 867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (758927 / 2500000) (303570801 / 1000000000) (Real.log (867 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (867 / 640) = -Real.log (640 / 867) := by
    rw [show ((867 / 640) : ℝ) = ((640 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (438020583 / 1000000000) ≤ -Real.log (413 / 640) ∧
    -Real.log (413 / 640) ≤ (54752573 / 125000000) := by
  have h := checkLog_sound (w := (227 / 1053)) (n := 12)
    (lo := (438020583 / 1000000000)) (hi := (54752573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 413) = 1/(413 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-54752573 / 125000000) (-438020583 / 1000000000) (Real.log (413 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (151352687 / 500000000) ≤ -Real.log (512 / 693) ∧
    -Real.log (512 / 693) ≤ (2421643 / 8000000) := by
  have h := checkLog_sound (w := (181 / 1205)) (n := 12)
    (lo := (151352687 / 500000000)) (hi := (2421643 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 512) = 1/(512 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (151352687 / 500000000) (2421643 / 8000000) (Real.log (693 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (693 / 512) = -Real.log (512 / 693) := by
    rw [show ((693 / 512) : ℝ) = ((512 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (436206249 / 1000000000) ≤ -Real.log (331 / 512) ∧
    -Real.log (331 / 512) ≤ (69793 / 160000) := by
  have h := checkLog_sound (w := (181 / 843)) (n := 12)
    (lo := (436206249 / 1000000000)) (hi := (69793 / 160000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 331) = 1/(331 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69793 / 160000) (-436206249 / 1000000000) (Real.log (331 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (268063903 / 500000000) ≤ -Real.log (320 / 547) ∧
    -Real.log (320 / 547) ≤ (536127807 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 867)) (n := 12)
    (lo := (268063903 / 500000000)) (hi := (536127807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547 / 320) = 1/(320 / 547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (268063903 / 500000000) (536127807 / 1000000000) (Real.log (547 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (547 / 320) = -Real.log (320 / 547) := by
    rw [show ((547 / 320) : ℝ) = ((320 / 547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (617860751 / 500000000) ≤ -Real.log (93 / 320) ∧
    -Real.log (93 / 320) ≤ (38616297 / 31250000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 93) = 1/(93 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38616297 / 31250000) (-617860751 / 500000000) (Real.log (93 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2139023 / 4000000) ≤ -Real.log (256 / 437) ∧
    -Real.log (256 / 437) ≤ (534755751 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 693)) (n := 12)
    (lo := (2139023 / 4000000)) (hi := (534755751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437 / 256) = 1/(256 / 437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2139023 / 4000000) (534755751 / 1000000000) (Real.log (437 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (437 / 256) = -Real.log (256 / 437) := by
    rw [show ((437 / 256) : ℝ) = ((256 / 437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122768933 / 100000000) ≤ -Real.log (75 / 256) ∧
    -Real.log (75 / 256) ≤ (306922333 / 250000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 75) = 1/(75 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-306922333 / 250000000) (-122768933 / 100000000) (Real.log (75 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (414357453 / 1000000000) ≤ -Real.log (500000 / 756699) ∧
    -Real.log (500000 / 756699) ≤ (207178727 / 500000000) := by
  have h := checkLog_sound (w := (256699 / 1256699)) (n := 12)
    (lo := (414357453 / 1000000000)) (hi := (207178727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756699 / 500000) = 1/(500000 / 756699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (414357453 / 1000000000) (207178727 / 500000000) (Real.log (756699 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (756699 / 500000) = -Real.log (500000 / 756699) := by
    rw [show ((756699 / 500000) : ℝ) = ((500000 / 756699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (720308737 / 1000000000) ≤ -Real.log (243301 / 500000) ∧
    -Real.log (243301 / 500000) ≤ (720308739 / 1000000000) := by
  have h := checkLog_sound (w := (6699 / 493301)) (n := 12)
    (lo := (27161557 / 1000000000)) (hi := (13580779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 243301) = 1/(243301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-720308739 / 1000000000) (-720308737 / 1000000000) (Real.log (243301 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (207780651 / 500000000) ≤ -Real.log (1000000 / 1515221) ∧
    -Real.log (1000000 / 1515221) ≤ (415561303 / 1000000000) := by
  have h := checkLog_sound (w := (515221 / 2515221)) (n := 12)
    (lo := (207780651 / 500000000)) (hi := (415561303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1515221 / 1000000) = 1/(1000000 / 1515221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (207780651 / 500000000) (415561303 / 1000000000) (Real.log (1515221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1515221 / 1000000) = -Real.log (1000000 / 1515221) := by
    rw [show ((1515221 / 1000000) : ℝ) = ((1000000 / 1515221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (724062161 / 1000000000) ≤ -Real.log (484779 / 1000000) ∧
    -Real.log (484779 / 1000000) ≤ (724062163 / 1000000000) := by
  have h := checkLog_sound (w := (15221 / 984779)) (n := 12)
    (lo := (30914981 / 1000000000)) (hi := (15457491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 484779) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 484779) = 1/(484779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-724062163 / 1000000000) (-724062161 / 1000000000) (Real.log (484779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10323863 / 31250000) ≤ -Real.log (500000 / 695737) ∧
    -Real.log (500000 / 695737) ≤ (330363617 / 1000000000) := by
  have h := checkLog_sound (w := (195737 / 1195737)) (n := 12)
    (lo := (10323863 / 31250000)) (hi := (330363617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695737 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695737 / 500000) = 1/(500000 / 695737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10323863 / 31250000) (330363617 / 1000000000) (Real.log (695737 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (695737 / 500000) = -Real.log (500000 / 695737) := by
    rw [show ((695737 / 500000) : ℝ) = ((500000 / 695737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (496715639 / 1000000000) ≤ -Real.log (304263 / 500000) ∧
    -Real.log (304263 / 500000) ≤ (12417891 / 25000000) := by
  have h := checkLog_sound (w := (195737 / 804263)) (n := 12)
    (lo := (496715639 / 1000000000)) (hi := (12417891 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 304263) = 1/(304263 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-12417891 / 25000000) (-496715639 / 1000000000) (Real.log (304263 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4143973 / 12500000) ≤ -Real.log (1000000 / 1393081) ∧
    -Real.log (1000000 / 1393081) ≤ (331517841 / 1000000000) := by
  have h := checkLog_sound (w := (393081 / 2393081)) (n := 12)
    (lo := (4143973 / 12500000)) (hi := (331517841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393081 / 1000000) = 1/(1000000 / 1393081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4143973 / 12500000) (331517841 / 1000000000) (Real.log (1393081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1393081 / 1000000) = -Real.log (1000000 / 1393081) := by
    rw [show ((1393081 / 1000000) : ℝ) = ((1000000 / 1393081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (499359939 / 1000000000) ≤ -Real.log (606919 / 1000000) ∧
    -Real.log (606919 / 1000000) ≤ (24967997 / 50000000) := by
  have h := checkLog_sound (w := (393081 / 1606919)) (n := 12)
    (lo := (499359939 / 1000000000)) (hi := (24967997 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606919) = 1/(606919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-24967997 / 50000000) (-499359939 / 1000000000) (Real.log (606919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1134666191 / 1000000000) ≤ -Real.log (500000000000 / 1555067591173) ∧
    -Real.log (500000000000 / 1555067591173) ≤ (1134666193 / 1000000000) := by
  have h := checkLog_sound (w := (555067591173 / 2555067591173)) (n := 12)
    (lo := (441519011 / 1000000000)) (hi := (110379753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1555067591173 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1555067591173 / 1000000000000) = 1/(500000000000 / 1555067591173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1134666191 / 1000000000) (1134666193 / 1000000000) (Real.log (1555067591173 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1555067591173 / 500000000000) = -Real.log (500000000000 / 1555067591173) := by
    rw [show ((1555067591173 / 500000000000) : ℝ) = ((500000000000 / 1555067591173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (142452933 / 125000000) ≤ -Real.log (250000000000 / 781397812199) ∧
    -Real.log (250000000000 / 781397812199) ≤ (569811733 / 500000000) := by
  have h := checkLog_sound (w := (281397812199 / 1281397812199)) (n := 12)
    (lo := (111619071 / 250000000)) (hi := (89295257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781397812199 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(781397812199 / 500000000000) = 1/(250000000000 / 781397812199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (142452933 / 125000000) (569811733 / 500000000) (Real.log (781397812199 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (781397812199 / 250000000000) = -Real.log (250000000000 / 781397812199) := by
    rw [show ((781397812199 / 250000000000) : ℝ) = ((250000000000 / 781397812199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (165415851 / 200000000) ≤ -Real.log (500000000000 / 1143315158267) ∧
    -Real.log (500000000000 / 1143315158267) ≤ (827079257 / 1000000000) := by
  have h := checkLog_sound (w := (143315158267 / 2143315158267)) (n := 12)
    (lo := (5357283 / 40000000)) (hi := (33483019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143315158267 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1143315158267 / 1000000000000) = 1/(500000000000 / 1143315158267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (165415851 / 200000000) (827079257 / 1000000000) (Real.log (1143315158267 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1143315158267 / 500000000000) = -Real.log (500000000000 / 1143315158267) := by
    rw [show ((1143315158267 / 500000000000) : ℝ) = ((500000000000 / 1143315158267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41543889 / 50000000) ≤ -Real.log (500000000000 / 1147666327797) ∧
    -Real.log (500000000000 / 1147666327797) ≤ (415438891 / 500000000) := by
  have h := checkLog_sound (w := (147666327797 / 2147666327797)) (n := 12)
    (lo := (688653 / 5000000)) (hi := (137730601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147666327797 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147666327797 / 1000000000000) = 1/(500000000000 / 1147666327797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41543889 / 50000000) (415438891 / 500000000) (Real.log (1147666327797 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1147666327797 / 500000000000) = -Real.log (500000000000 / 1147666327797) := by
    rw [show ((1147666327797 / 500000000000) : ℝ) = ((500000000000 / 1147666327797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0135
