import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell140
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

theorem reflection_log_1_neg : (143572409 / 500000000) ≤ -Real.log (5120 / 6823) ∧
    -Real.log (5120 / 6823) ≤ (287144819 / 1000000000) := by
  have h := checkLog_sound (w := (1703 / 11943)) (n := 12)
    (lo := (143572409 / 500000000)) (hi := (287144819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6823 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6823 / 5120) = 1/(5120 / 6823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (143572409 / 500000000) (287144819 / 1000000000) (Real.log (6823 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6823 / 5120) = -Real.log (5120 / 6823) := by
    rw [show ((6823 / 5120) : ℝ) = ((5120 / 6823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (80878293 / 200000000) ≤ -Real.log (3417 / 5120) ∧
    -Real.log (3417 / 5120) ≤ (202195733 / 500000000) := by
  have h := checkLog_sound (w := (1703 / 8537)) (n := 12)
    (lo := (80878293 / 200000000)) (hi := (202195733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3417) = 1/(3417 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-202195733 / 500000000) (-80878293 / 200000000) (Real.log (3417 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (35838129 / 125000000) ≤ -Real.log (256 / 341) ∧
    -Real.log (256 / 341) ≤ (286705033 / 1000000000) := by
  have h := checkLog_sound (w := (85 / 597)) (n := 12)
    (lo := (35838129 / 125000000)) (hi := (286705033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341 / 256) = 1/(256 / 341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (35838129 / 125000000) (286705033 / 1000000000) (Real.log (341 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (341 / 256) = -Real.log (256 / 341) := by
    rw [show ((341 / 256) : ℝ) = ((256 / 341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (403513887 / 1000000000) ≤ -Real.log (171 / 256) ∧
    -Real.log (171 / 256) ≤ (12609809 / 31250000) := by
  have h := checkLog_sound (w := (85 / 427)) (n := 12)
    (lo := (403513887 / 1000000000)) (hi := (12609809 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 171) = 1/(171 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12609809 / 31250000) (-403513887 / 1000000000) (Real.log (171 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (211809159 / 1000000000) ≤ -Real.log (125000 / 154489) ∧
    -Real.log (125000 / 154489) ≤ (5295229 / 25000000) := by
  have h := checkLog_sound (w := (29489 / 279489)) (n := 12)
    (lo := (211809159 / 1000000000)) (hi := (5295229 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154489 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154489 / 125000) = 1/(125000 / 154489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (211809159 / 1000000000) (5295229 / 25000000) (Real.log (154489 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (154489 / 125000) = -Real.log (125000 / 154489) := by
    rw [show ((154489 / 125000) : ℝ) = ((125000 / 154489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (269072313 / 1000000000) ≤ -Real.log (95511 / 125000) ∧
    -Real.log (95511 / 125000) ≤ (134536157 / 500000000) := by
  have h := checkLog_sound (w := (29489 / 220511)) (n := 12)
    (lo := (269072313 / 1000000000)) (hi := (134536157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95511) = 1/(95511 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134536157 / 500000000) (-269072313 / 1000000000) (Real.log (95511 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10607487 / 50000000) ≤ -Real.log (1000000 / 1236333) ∧
    -Real.log (1000000 / 1236333) ≤ (212149741 / 1000000000) := by
  have h := checkLog_sound (w := (236333 / 2236333)) (n := 12)
    (lo := (10607487 / 50000000)) (hi := (212149741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236333 / 1000000) = 1/(1000000 / 1236333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10607487 / 50000000) (212149741 / 1000000000) (Real.log (1236333 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1236333 / 1000000) = -Real.log (1000000 / 1236333) := by
    rw [show ((1236333 / 1000000) : ℝ) = ((1000000 / 1236333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33702931 / 125000000) ≤ -Real.log (763667 / 1000000) ∧
    -Real.log (763667 / 1000000) ≤ (269623449 / 1000000000) := by
  have h := checkLog_sound (w := (236333 / 1763667)) (n := 12)
    (lo := (33702931 / 125000000)) (hi := (269623449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763667) = 1/(763667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-269623449 / 1000000000) (-33702931 / 125000000) (Real.log (763667 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (31302777 / 200000000) ≤ -Real.log (1000000 / 1169427) ∧
    -Real.log (1000000 / 1169427) ≤ (78256943 / 500000000) := by
  have h := checkLog_sound (w := (169427 / 2169427)) (n := 12)
    (lo := (31302777 / 200000000)) (hi := (78256943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169427 / 1000000) = 1/(1000000 / 1169427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (31302777 / 200000000) (78256943 / 500000000) (Real.log (1169427 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1169427 / 1000000) = -Real.log (1000000 / 1169427) := by
    rw [show ((1169427 / 1000000) : ℝ) = ((1000000 / 1169427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92819727 / 500000000) ≤ -Real.log (830573 / 1000000) ∧
    -Real.log (830573 / 1000000) ≤ (37127891 / 200000000) := by
  have h := checkLog_sound (w := (169427 / 1830573)) (n := 12)
    (lo := (92819727 / 500000000)) (hi := (37127891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830573) = 1/(830573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37127891 / 200000000) (-92819727 / 500000000) (Real.log (830573 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156781501 / 1000000000) ≤ -Real.log (50000 / 58487) ∧
    -Real.log (50000 / 58487) ≤ (78390751 / 500000000) := by
  have h := checkLog_sound (w := (8487 / 108487)) (n := 12)
    (lo := (156781501 / 1000000000)) (hi := (78390751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58487 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58487 / 50000) = 1/(50000 / 58487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156781501 / 1000000000) (78390751 / 500000000) (Real.log (58487 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58487 / 50000) = -Real.log (50000 / 58487) := by
    rw [show ((58487 / 50000) : ℝ) = ((50000 / 58487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93008187 / 500000000) ≤ -Real.log (41513 / 50000) ∧
    -Real.log (41513 / 50000) ≤ (1488131 / 8000000) := by
  have h := checkLog_sound (w := (8487 / 91513)) (n := 12)
    (lo := (93008187 / 500000000)) (hi := (1488131 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 41513) = 1/(41513 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1488131 / 8000000) (-93008187 / 500000000) (Real.log (41513 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (17255473 / 25000000) ≤ -Real.log (500000000000 / 997076023391) ∧
    -Real.log (500000000000 / 997076023391) ≤ (690218921 / 1000000000) := by
  have h := checkLog_sound (w := (497076023391 / 1497076023391)) (n := 12)
    (lo := (17255473 / 25000000)) (hi := (690218921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997076023391 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997076023391 / 500000000000) = 1/(500000000000 / 997076023391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (17255473 / 25000000) (690218921 / 1000000000) (Real.log (997076023391 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (997076023391 / 500000000000) = -Real.log (500000000000 / 997076023391) := by
    rw [show ((997076023391 / 500000000000) : ℝ) = ((500000000000 / 997076023391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (172884071 / 250000000) ≤ -Real.log (500000000000 / 998390400937) ∧
    -Real.log (500000000000 / 998390400937) ≤ (138307257 / 200000000) := by
  have h := checkLog_sound (w := (498390400937 / 1498390400937)) (n := 12)
    (lo := (172884071 / 250000000)) (hi := (138307257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((998390400937 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(998390400937 / 500000000000) = 1/(500000000000 / 998390400937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (172884071 / 250000000) (138307257 / 200000000) (Real.log (998390400937 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (998390400937 / 500000000000) = -Real.log (500000000000 / 998390400937) := by
    rw [show ((998390400937 / 500000000000) : ℝ) = ((500000000000 / 998390400937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (7513773 / 15625000) ≤ -Real.log (62500000000 / 101093722189) ∧
    -Real.log (62500000000 / 101093722189) ≤ (480881473 / 1000000000) := by
  have h := checkLog_sound (w := (38593722189 / 163593722189)) (n := 12)
    (lo := (7513773 / 15625000)) (hi := (480881473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101093722189 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101093722189 / 62500000000) = 1/(62500000000 / 101093722189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7513773 / 15625000) (480881473 / 1000000000) (Real.log (101093722189 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (101093722189 / 62500000000) = -Real.log (62500000000 / 101093722189) := by
    rw [show ((101093722189 / 62500000000) : ℝ) = ((62500000000 / 101093722189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (120443297 / 250000000) ≤ -Real.log (15625000000 / 25295977337) ∧
    -Real.log (15625000000 / 25295977337) ≤ (481773189 / 1000000000) := by
  have h := checkLog_sound (w := (9670977337 / 40920977337)) (n := 12)
    (lo := (120443297 / 250000000)) (hi := (481773189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25295977337 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25295977337 / 15625000000) = 1/(15625000000 / 25295977337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (120443297 / 250000000) (481773189 / 1000000000) (Real.log (25295977337 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (25295977337 / 15625000000) = -Real.log (15625000000 / 25295977337) := by
    rw [show ((25295977337 / 15625000000) : ℝ) = ((15625000000 / 25295977337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (17107667 / 50000000) ≤ -Real.log (500000000000 / 703988090149) ∧
    -Real.log (500000000000 / 703988090149) ≤ (342153341 / 1000000000) := by
  have h := checkLog_sound (w := (203988090149 / 1203988090149)) (n := 12)
    (lo := (17107667 / 50000000)) (hi := (342153341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703988090149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703988090149 / 500000000000) = 1/(500000000000 / 703988090149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17107667 / 50000000) (342153341 / 1000000000) (Real.log (703988090149 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703988090149 / 500000000000) = -Real.log (500000000000 / 703988090149) := by
    rw [show ((703988090149 / 500000000000) : ℝ) = ((500000000000 / 703988090149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (85699469 / 250000000) ≤ -Real.log (50000000000 / 70444198203) ∧
    -Real.log (50000000000 / 70444198203) ≤ (342797877 / 1000000000) := by
  have h := checkLog_sound (w := (20444198203 / 120444198203)) (n := 12)
    (lo := (85699469 / 250000000)) (hi := (342797877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70444198203 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70444198203 / 50000000000) = 1/(50000000000 / 70444198203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (85699469 / 250000000) (342797877 / 1000000000) (Real.log (70444198203 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (70444198203 / 50000000000) = -Real.log (50000000000 / 70444198203) := by
    rw [show ((70444198203 / 50000000000) : ℝ) = ((50000000000 / 70444198203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3654359 / 125000000) ≤ -Real.log (2427970831 / 2500000000) ∧
    -Real.log (2427970831 / 2500000000) ≤ (29234873 / 1000000000) := by
  have h := checkLog_sound (w := (72029169 / 4927970831)) (n := 12)
    (lo := (3654359 / 125000000)) (hi := (29234873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2427970831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2427970831) = 1/(2427970831 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29234873 / 1000000000) (-3654359 / 125000000) (Real.log (2427970831 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (29125569 / 1000000000) ≤ -Real.log (971294491671 / 1000000000000) ∧
    -Real.log (971294491671 / 1000000000000) ≤ (2912557 / 100000000) := by
  have h := checkLog_sound (w := (28705508329 / 1971294491671)) (n := 12)
    (lo := (29125569 / 1000000000)) (hi := (2912557 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971294491671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971294491671) = 1/(971294491671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2912557 / 100000000) (-29125569 / 1000000000) (Real.log (971294491671 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell140
