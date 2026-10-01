import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell255
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

theorem reflection_log_1_neg : (84118059 / 250000000) ≤ -Real.log (5 / 7) ∧
    -Real.log (5 / 7) ≤ (336472237 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 6)) (n := 12)
    (lo := (84118059 / 250000000)) (hi := (336472237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7 / 5) = 1/(5 / 7) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84118059 / 250000000) (336472237 / 1000000000) (Real.log (7 / 5)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7 / 5) = -Real.log (5 / 7) := by
    rw [show ((7 / 5) : ℝ) = ((5 / 7) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (510825623 / 1000000000) ≤ -Real.log (3 / 5) ∧
    -Real.log (3 / 5) ≤ (63853203 / 125000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 3) = 1/(3 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63853203 / 125000000) (-510825623 / 1000000000) (Real.log (3 / 5)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (168026811 / 500000000) ≤ -Real.log (1024 / 1433) ∧
    -Real.log (1024 / 1433) ≤ (336053623 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2457)) (n := 12)
    (lo := (168026811 / 500000000)) (hi := (336053623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1024) = 1/(1024 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (168026811 / 500000000) (336053623 / 1000000000) (Real.log (1433 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1433 / 1024) = -Real.log (1024 / 1433) := by
    rw [show ((1433 / 1024) : ℝ) = ((1024 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (509849537 / 1000000000) ≤ -Real.log (615 / 1024) ∧
    -Real.log (615 / 1024) ≤ (254924769 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1639)) (n := 12)
    (lo := (509849537 / 1000000000)) (hi := (254924769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 615) = 1/(615 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-254924769 / 500000000) (-509849537 / 1000000000) (Real.log (615 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62580901 / 250000000) ≤ -Real.log (1000000 / 1284441) ∧
    -Real.log (1000000 / 1284441) ≤ (50064721 / 200000000) := by
  have h := checkLog_sound (w := (284441 / 2284441)) (n := 12)
    (lo := (62580901 / 250000000)) (hi := (50064721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284441 / 1000000) = 1/(1000000 / 1284441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62580901 / 250000000) (50064721 / 200000000) (Real.log (1284441 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1284441 / 1000000) = -Real.log (1000000 / 1284441) := by
    rw [show ((1284441 / 1000000) : ℝ) = ((1000000 / 1284441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (334691223 / 1000000000) ≤ -Real.log (715559 / 1000000) ∧
    -Real.log (715559 / 1000000) ≤ (41836403 / 125000000) := by
  have h := checkLog_sound (w := (284441 / 1715559)) (n := 12)
    (lo := (334691223 / 1000000000)) (hi := (41836403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715559) = 1/(715559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41836403 / 125000000) (-334691223 / 1000000000) (Real.log (715559 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7832951 / 31250000) ≤ -Real.log (500000 / 642433) ∧
    -Real.log (500000 / 642433) ≤ (250654433 / 1000000000) := by
  have h := checkLog_sound (w := (142433 / 1142433)) (n := 12)
    (lo := (7832951 / 31250000)) (hi := (250654433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642433 / 500000) = 1/(500000 / 642433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7832951 / 31250000) (250654433 / 1000000000) (Real.log (642433 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642433 / 500000) = -Real.log (500000 / 642433) := by
    rw [show ((642433 / 500000) : ℝ) = ((500000 / 642433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (335285341 / 1000000000) ≤ -Real.log (357567 / 500000) ∧
    -Real.log (357567 / 500000) ≤ (167642671 / 500000000) := by
  have h := checkLog_sound (w := (142433 / 857567)) (n := 12)
    (lo := (335285341 / 1000000000)) (hi := (167642671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357567) = 1/(357567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167642671 / 500000000) (-335285341 / 1000000000) (Real.log (357567 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (93546743 / 500000000) ≤ -Real.log (50000 / 60287) ∧
    -Real.log (50000 / 60287) ≤ (187093487 / 1000000000) := by
  have h := checkLog_sound (w := (10287 / 110287)) (n := 12)
    (lo := (93546743 / 500000000)) (hi := (187093487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60287 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60287 / 50000) = 1/(50000 / 60287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (93546743 / 500000000) (187093487 / 1000000000) (Real.log (60287 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (60287 / 50000) = -Real.log (50000 / 60287) := by
    rw [show ((60287 / 50000) : ℝ) = ((50000 / 60287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46068883 / 200000000) ≤ -Real.log (39713 / 50000) ∧
    -Real.log (39713 / 50000) ≤ (7198263 / 31250000) := by
  have h := checkLog_sound (w := (10287 / 89713)) (n := 12)
    (lo := (46068883 / 200000000)) (hi := (7198263 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39713) = 1/(39713 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7198263 / 31250000) (-46068883 / 200000000) (Real.log (39713 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (187359677 / 1000000000) ≤ -Real.log (1000000 / 1206061) ∧
    -Real.log (1000000 / 1206061) ≤ (93679839 / 500000000) := by
  have h := checkLog_sound (w := (206061 / 2206061)) (n := 12)
    (lo := (187359677 / 1000000000)) (hi := (93679839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206061 / 1000000) = 1/(1000000 / 1206061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (187359677 / 1000000000) (93679839 / 500000000) (Real.log (1206061 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1206061 / 1000000) = -Real.log (1000000 / 1206061) := by
    rw [show ((1206061 / 1000000) : ℝ) = ((1000000 / 1206061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115374323 / 500000000) ≤ -Real.log (793939 / 1000000) ∧
    -Real.log (793939 / 1000000) ≤ (230748647 / 1000000000) := by
  have h := checkLog_sound (w := (206061 / 1793939)) (n := 12)
    (lo := (115374323 / 500000000)) (hi := (230748647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793939) = 1/(793939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-230748647 / 1000000000) (-115374323 / 500000000) (Real.log (793939 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (845903159 / 1000000000) ≤ -Real.log (250000000000 / 582520325203) ∧
    -Real.log (250000000000 / 582520325203) ≤ (845903161 / 1000000000) := by
  have h := checkLog_sound (w := (82520325203 / 1082520325203)) (n := 12)
    (lo := (152755979 / 1000000000)) (hi := (7637799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582520325203 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(582520325203 / 500000000000) = 1/(250000000000 / 582520325203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (845903159 / 1000000000) (845903161 / 1000000000) (Real.log (582520325203 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (582520325203 / 250000000000) = -Real.log (250000000000 / 582520325203) := by
    rw [show ((582520325203 / 250000000000) : ℝ) = ((250000000000 / 582520325203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (847297859 / 1000000000) ≤ -Real.log (500000000000 / 1166666666667) ∧
    -Real.log (500000000000 / 1166666666667) ≤ (847297861 / 1000000000) := by
  have h := checkLog_sound (w := (166666666667 / 2166666666667)) (n := 12)
    (lo := (154150679 / 1000000000)) (hi := (3853767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166666666667 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1166666666667 / 1000000000000) = 1/(500000000000 / 1166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (847297859 / 1000000000) (847297861 / 1000000000) (Real.log (1166666666667 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1166666666667 / 500000000000) = -Real.log (500000000000 / 1166666666667) := by
    rw [show ((1166666666667 / 500000000000) : ℝ) = ((500000000000 / 1166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (585014827 / 1000000000) ≤ -Real.log (500000000000 / 897508800811) ∧
    -Real.log (500000000000 / 897508800811) ≤ (146253707 / 250000000) := by
  have h := checkLog_sound (w := (397508800811 / 1397508800811)) (n := 12)
    (lo := (585014827 / 1000000000)) (hi := (146253707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897508800811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897508800811 / 500000000000) = 1/(500000000000 / 897508800811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (585014827 / 1000000000) (146253707 / 250000000) (Real.log (897508800811 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (897508800811 / 500000000000) = -Real.log (500000000000 / 897508800811) := by
    rw [show ((897508800811 / 500000000000) : ℝ) = ((500000000000 / 897508800811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (292969887 / 500000000) ≤ -Real.log (50000000000 / 89833933221) ∧
    -Real.log (50000000000 / 89833933221) ≤ (23437591 / 40000000) := by
  have h := checkLog_sound (w := (39833933221 / 139833933221)) (n := 12)
    (lo := (292969887 / 500000000)) (hi := (23437591 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89833933221 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89833933221 / 50000000000) = 1/(50000000000 / 89833933221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (292969887 / 500000000) (23437591 / 40000000) (Real.log (89833933221 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (89833933221 / 50000000000) = -Real.log (50000000000 / 89833933221) := by
    rw [show ((89833933221 / 50000000000) : ℝ) = ((50000000000 / 89833933221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (417437901 / 1000000000) ≤ -Real.log (250000000000 / 379516782917) ∧
    -Real.log (250000000000 / 379516782917) ≤ (208718951 / 500000000) := by
  have h := checkLog_sound (w := (129516782917 / 629516782917)) (n := 12)
    (lo := (417437901 / 1000000000)) (hi := (208718951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379516782917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379516782917 / 250000000000) = 1/(250000000000 / 379516782917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (417437901 / 1000000000) (208718951 / 500000000) (Real.log (379516782917 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379516782917 / 250000000000) = -Real.log (250000000000 / 379516782917) := by
    rw [show ((379516782917 / 250000000000) : ℝ) = ((250000000000 / 379516782917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (104527081 / 250000000) ≤ -Real.log (500000000000 / 759542609697) ∧
    -Real.log (500000000000 / 759542609697) ≤ (16724333 / 40000000) := by
  have h := checkLog_sound (w := (259542609697 / 1259542609697)) (n := 12)
    (lo := (104527081 / 250000000)) (hi := (16724333 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759542609697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759542609697 / 500000000000) = 1/(500000000000 / 759542609697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (104527081 / 250000000) (16724333 / 40000000) (Real.log (759542609697 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (759542609697 / 500000000000) = -Real.log (500000000000 / 759542609697) := by
    rw [show ((759542609697 / 500000000000) : ℝ) = ((500000000000 / 759542609697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43388969 / 1000000000) ≤ -Real.log (957538864279 / 1000000000000) ∧
    -Real.log (957538864279 / 1000000000000) ≤ (4338897 / 100000000) := by
  have h := checkLog_sound (w := (42461135721 / 1957538864279)) (n := 12)
    (lo := (43388969 / 1000000000)) (hi := (4338897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957538864279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957538864279) = 1/(957538864279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4338897 / 100000000) (-43388969 / 1000000000) (Real.log (957538864279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (43250929 / 1000000000) ≤ -Real.log (2394177631 / 2500000000) ∧
    -Real.log (2394177631 / 2500000000) ≤ (4325093 / 100000000) := by
  have h := checkLog_sound (w := (105822369 / 4894177631)) (n := 12)
    (lo := (43250929 / 1000000000)) (hi := (4325093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2394177631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2394177631) = 1/(2394177631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4325093 / 100000000) (-43250929 / 1000000000) (Real.log (2394177631 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell255
