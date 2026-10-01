import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell239
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

theorem reflection_log_1_neg : (164876643 / 500000000) ≤ -Real.log (64 / 89) ∧
    -Real.log (64 / 89) ≤ (329753287 / 1000000000) := by
  have h := checkLog_sound (w := (25 / 153)) (n := 12)
    (lo := (164876643 / 500000000)) (hi := (329753287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89 / 64) = 1/(64 / 89) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164876643 / 500000000) (329753287 / 1000000000) (Real.log (89 / 64)) := by
  have h := reflection_log_1_neg
  have he : Real.log (89 / 64) = -Real.log (64 / 89) := by
    rw [show ((89 / 64) : ℝ) = ((64 / 89) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (495321437 / 1000000000) ≤ -Real.log (39 / 64) ∧
    -Real.log (39 / 64) ≤ (247660719 / 500000000) := by
  have h := checkLog_sound (w := (25 / 103)) (n := 12)
    (lo := (495321437 / 1000000000)) (hi := (247660719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 39) = 1/(39 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-247660719 / 500000000) (-495321437 / 1000000000) (Real.log (39 / 64)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (329331849 / 1000000000) ≤ -Real.log (5120 / 7117) ∧
    -Real.log (5120 / 7117) ≤ (6586637 / 20000000) := by
  have h := checkLog_sound (w := (1997 / 12237)) (n := 12)
    (lo := (329331849 / 1000000000)) (hi := (6586637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7117 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7117 / 5120) = 1/(5120 / 7117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (329331849 / 1000000000) (6586637 / 20000000) (Real.log (7117 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7117 / 5120) = -Real.log (5120 / 7117) := by
    rw [show ((7117 / 5120) : ℝ) = ((5120 / 7117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (12359009 / 25000000) ≤ -Real.log (3123 / 5120) ∧
    -Real.log (3123 / 5120) ≤ (494360361 / 1000000000) := by
  have h := checkLog_sound (w := (1997 / 8243)) (n := 12)
    (lo := (12359009 / 25000000)) (hi := (494360361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3123) = 1/(3123 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-494360361 / 1000000000) (-12359009 / 25000000) (Real.log (3123 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122517879 / 500000000) ≤ -Real.log (1000000 / 1277667) ∧
    -Real.log (1000000 / 1277667) ≤ (245035759 / 1000000000) := by
  have h := checkLog_sound (w := (277667 / 2277667)) (n := 12)
    (lo := (122517879 / 500000000)) (hi := (245035759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277667 / 1000000) = 1/(1000000 / 1277667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122517879 / 500000000) (245035759 / 1000000000) (Real.log (1277667 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1277667 / 1000000) = -Real.log (1000000 / 1277667) := by
    rw [show ((1277667 / 1000000) : ℝ) = ((1000000 / 1277667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (325269027 / 1000000000) ≤ -Real.log (722333 / 1000000) ∧
    -Real.log (722333 / 1000000) ≤ (81317257 / 250000000) := by
  have h := checkLog_sound (w := (277667 / 1722333)) (n := 12)
    (lo := (325269027 / 1000000000)) (hi := (81317257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 722333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 722333) = 1/(722333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-81317257 / 250000000) (-325269027 / 1000000000) (Real.log (722333 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (122683779 / 500000000) ≤ -Real.log (1000000 / 1278091) ∧
    -Real.log (1000000 / 1278091) ≤ (245367559 / 1000000000) := by
  have h := checkLog_sound (w := (278091 / 2278091)) (n := 12)
    (lo := (122683779 / 500000000)) (hi := (245367559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278091 / 1000000) = 1/(1000000 / 1278091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (122683779 / 500000000) (245367559 / 1000000000) (Real.log (1278091 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1278091 / 1000000) = -Real.log (1000000 / 1278091) := by
    rw [show ((1278091 / 1000000) : ℝ) = ((1000000 / 1278091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (162928093 / 500000000) ≤ -Real.log (721909 / 1000000) ∧
    -Real.log (721909 / 1000000) ≤ (325856187 / 1000000000) := by
  have h := checkLog_sound (w := (278091 / 1721909)) (n := 12)
    (lo := (162928093 / 500000000)) (hi := (325856187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721909) = 1/(721909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-325856187 / 1000000000) (-162928093 / 500000000) (Real.log (721909 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (182841421 / 1000000000) ≤ -Real.log (62500 / 75039) ∧
    -Real.log (62500 / 75039) ≤ (91420711 / 500000000) := by
  have h := checkLog_sound (w := (12539 / 137539)) (n := 12)
    (lo := (182841421 / 1000000000)) (hi := (91420711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75039 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75039 / 62500) = 1/(62500 / 75039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (182841421 / 1000000000) (91420711 / 500000000) (Real.log (75039 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75039 / 62500) = -Real.log (62500 / 75039) := by
    rw [show ((75039 / 62500) : ℝ) = ((62500 / 75039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44784771 / 200000000) ≤ -Real.log (49961 / 62500) ∧
    -Real.log (49961 / 62500) ≤ (13995241 / 62500000) := by
  have h := checkLog_sound (w := (12539 / 112461)) (n := 12)
    (lo := (44784771 / 200000000)) (hi := (13995241 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49961) = 1/(49961 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13995241 / 62500000) (-44784771 / 200000000) (Real.log (49961 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (91553957 / 500000000) ≤ -Real.log (62500 / 75059) ∧
    -Real.log (62500 / 75059) ≤ (36621583 / 200000000) := by
  have h := checkLog_sound (w := (12559 / 137559)) (n := 12)
    (lo := (91553957 / 500000000)) (hi := (36621583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75059 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75059 / 62500) = 1/(62500 / 75059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (91553957 / 500000000) (36621583 / 200000000) (Real.log (75059 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (75059 / 62500) = -Real.log (62500 / 75059) := by
    rw [show ((75059 / 62500) : ℝ) = ((62500 / 75059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28040531 / 125000000) ≤ -Real.log (49941 / 62500) ∧
    -Real.log (49941 / 62500) ≤ (224324249 / 1000000000) := by
  have h := checkLog_sound (w := (12559 / 112441)) (n := 12)
    (lo := (28040531 / 125000000)) (hi := (224324249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49941) = 1/(49941 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-224324249 / 1000000000) (-28040531 / 125000000) (Real.log (49941 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (823692209 / 1000000000) ≤ -Real.log (250000000000 / 569724623759) ∧
    -Real.log (250000000000 / 569724623759) ≤ (823692211 / 1000000000) := by
  have h := checkLog_sound (w := (69724623759 / 1069724623759)) (n := 12)
    (lo := (130545029 / 1000000000)) (hi := (13054503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569724623759 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569724623759 / 500000000000) = 1/(250000000000 / 569724623759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (823692209 / 1000000000) (823692211 / 1000000000) (Real.log (569724623759 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (569724623759 / 250000000000) = -Real.log (250000000000 / 569724623759) := by
    rw [show ((569724623759 / 250000000000) : ℝ) = ((250000000000 / 569724623759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (825074723 / 1000000000) ≤ -Real.log (250000000000 / 570512820513) ∧
    -Real.log (250000000000 / 570512820513) ≤ (33002989 / 40000000) := by
  have h := checkLog_sound (w := (70512820513 / 1070512820513)) (n := 12)
    (lo := (131927543 / 1000000000)) (hi := (16490943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570512820513 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(570512820513 / 500000000000) = 1/(250000000000 / 570512820513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (825074723 / 1000000000) (33002989 / 40000000) (Real.log (570512820513 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (570512820513 / 250000000000) = -Real.log (250000000000 / 570512820513) := by
    rw [show ((570512820513 / 250000000000) : ℝ) = ((250000000000 / 570512820513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (285152393 / 500000000) ≤ -Real.log (500000000000 / 884403038487) ∧
    -Real.log (500000000000 / 884403038487) ≤ (570304787 / 1000000000) := by
  have h := checkLog_sound (w := (384403038487 / 1384403038487)) (n := 12)
    (lo := (285152393 / 500000000)) (hi := (570304787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884403038487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884403038487 / 500000000000) = 1/(500000000000 / 884403038487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (285152393 / 500000000) (570304787 / 1000000000) (Real.log (884403038487 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (884403038487 / 500000000000) = -Real.log (500000000000 / 884403038487) := by
    rw [show ((884403038487 / 500000000000) : ℝ) = ((500000000000 / 884403038487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114244749 / 200000000) ≤ -Real.log (500000000000 / 885216142201) ∧
    -Real.log (500000000000 / 885216142201) ≤ (285611873 / 500000000) := by
  have h := checkLog_sound (w := (385216142201 / 1385216142201)) (n := 12)
    (lo := (114244749 / 200000000)) (hi := (285611873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885216142201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885216142201 / 500000000000) = 1/(500000000000 / 885216142201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (114244749 / 200000000) (285611873 / 500000000) (Real.log (885216142201 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (885216142201 / 500000000000) = -Real.log (500000000000 / 885216142201) := by
    rw [show ((885216142201 / 500000000000) : ℝ) = ((500000000000 / 885216142201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (406765277 / 1000000000) ≤ -Real.log (500000000000 / 750975761093) ∧
    -Real.log (500000000000 / 750975761093) ≤ (203382639 / 500000000) := by
  have h := checkLog_sound (w := (250975761093 / 1250975761093)) (n := 12)
    (lo := (406765277 / 1000000000)) (hi := (203382639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750975761093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750975761093 / 500000000000) = 1/(500000000000 / 750975761093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (406765277 / 1000000000) (203382639 / 500000000) (Real.log (750975761093 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (750975761093 / 500000000000) = -Real.log (500000000000 / 750975761093) := by
    rw [show ((750975761093 / 500000000000) : ℝ) = ((500000000000 / 750975761093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (203716081 / 500000000) ≤ -Real.log (500000000000 / 751476742557) ∧
    -Real.log (500000000000 / 751476742557) ≤ (407432163 / 1000000000) := by
  have h := checkLog_sound (w := (251476742557 / 1251476742557)) (n := 12)
    (lo := (203716081 / 500000000)) (hi := (407432163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751476742557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751476742557 / 500000000000) = 1/(500000000000 / 751476742557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (203716081 / 500000000) (407432163 / 1000000000) (Real.log (751476742557 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (751476742557 / 500000000000) = -Real.log (500000000000 / 751476742557) := by
    rw [show ((751476742557 / 500000000000) : ℝ) = ((500000000000 / 751476742557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (41216333 / 1000000000) ≤ -Real.log (3748521519 / 3906250000) ∧
    -Real.log (3748521519 / 3906250000) ≤ (20608167 / 500000000) := by
  have h := checkLog_sound (w := (157728481 / 7654771519)) (n := 12)
    (lo := (41216333 / 1000000000)) (hi := (20608167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3748521519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3748521519) = 1/(3748521519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20608167 / 500000000) (-41216333 / 1000000000) (Real.log (3748521519 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20541217 / 500000000) ≤ -Real.log (3749023479 / 3906250000) ∧
    -Real.log (3749023479 / 3906250000) ≤ (8216487 / 200000000) := by
  have h := checkLog_sound (w := (157226521 / 7655273479)) (n := 12)
    (lo := (20541217 / 500000000)) (hi := (8216487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3749023479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3749023479) = 1/(3749023479 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8216487 / 200000000) (-20541217 / 500000000) (Real.log (3749023479 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell239
