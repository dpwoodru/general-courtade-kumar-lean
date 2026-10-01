import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell151
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

theorem reflection_log_1_neg : (145984871 / 500000000) ≤ -Real.log (640 / 857) ∧
    -Real.log (640 / 857) ≤ (291969743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1497)) (n := 12)
    (lo := (145984871 / 500000000)) (hi := (291969743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857 / 640) = 1/(640 / 857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (145984871 / 500000000) (291969743 / 1000000000) (Real.log (857 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (857 / 640) = -Real.log (640 / 857) := by
    rw [show ((857 / 640) : ℝ) = ((640 / 857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (414095997 / 1000000000) ≤ -Real.log (423 / 640) ∧
    -Real.log (423 / 640) ≤ (207047999 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 423) = 1/(423 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-207047999 / 500000000) (-414095997 / 1000000000) (Real.log (423 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291532073 / 1000000000) ≤ -Real.log (5120 / 6853) ∧
    -Real.log (5120 / 6853) ≤ (145766037 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 11973)) (n := 12)
    (lo := (291532073 / 1000000000)) (hi := (145766037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6853 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6853 / 5120) = 1/(5120 / 6853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291532073 / 1000000000) (145766037 / 500000000) (Real.log (6853 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6853 / 5120) = -Real.log (5120 / 6853) := by
    rw [show ((6853 / 5120) : ℝ) = ((5120 / 6853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82641973 / 200000000) ≤ -Real.log (3387 / 5120) ∧
    -Real.log (3387 / 5120) ≤ (206604933 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 8507)) (n := 12)
    (lo := (82641973 / 200000000)) (hi := (206604933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3387) = 1/(3387 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-206604933 / 500000000) (-82641973 / 200000000) (Real.log (3387 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (107772981 / 500000000) ≤ -Real.log (1000000 / 1240539) ∧
    -Real.log (1000000 / 1240539) ≤ (215545963 / 1000000000) := by
  have h := checkLog_sound (w := (240539 / 2240539)) (n := 12)
    (lo := (107772981 / 500000000)) (hi := (215545963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240539 / 1000000) = 1/(1000000 / 1240539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (107772981 / 500000000) (215545963 / 1000000000) (Real.log (1240539 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1240539 / 1000000) = -Real.log (1000000 / 1240539) := by
    rw [show ((1240539 / 1000000) : ℝ) = ((1000000 / 1240539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (275146307 / 1000000000) ≤ -Real.log (759461 / 1000000) ∧
    -Real.log (759461 / 1000000) ≤ (68786577 / 250000000) := by
  have h := checkLog_sound (w := (240539 / 1759461)) (n := 12)
    (lo := (275146307 / 1000000000)) (hi := (68786577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759461) = 1/(759461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-68786577 / 250000000) (-275146307 / 1000000000) (Real.log (759461 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (215886079 / 1000000000) ≤ -Real.log (1000000 / 1240961) ∧
    -Real.log (1000000 / 1240961) ≤ (168661 / 781250) := by
  have h := checkLog_sound (w := (240961 / 2240961)) (n := 12)
    (lo := (215886079 / 1000000000)) (hi := (168661 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240961 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240961 / 1000000) = 1/(1000000 / 1240961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (215886079 / 1000000000) (168661 / 781250) (Real.log (1240961 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1240961 / 1000000) = -Real.log (1000000 / 1240961) := by
    rw [show ((1240961 / 1000000) : ℝ) = ((1000000 / 1240961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (275702119 / 1000000000) ≤ -Real.log (759039 / 1000000) ∧
    -Real.log (759039 / 1000000) ≤ (6892553 / 25000000) := by
  have h := checkLog_sound (w := (240961 / 1759039)) (n := 12)
    (lo := (275702119 / 1000000000)) (hi := (6892553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759039) = 1/(759039 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6892553 / 25000000) (-275702119 / 1000000000) (Real.log (759039 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39860663 / 250000000) ≤ -Real.log (1000000 / 1172857) ∧
    -Real.log (1000000 / 1172857) ≤ (159442653 / 1000000000) := by
  have h := checkLog_sound (w := (172857 / 2172857)) (n := 12)
    (lo := (39860663 / 250000000)) (hi := (159442653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1172857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1172857 / 1000000) = 1/(1000000 / 1172857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39860663 / 250000000) (159442653 / 1000000000) (Real.log (1172857 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1172857 / 1000000) = -Real.log (1000000 / 1172857) := by
    rw [show ((1172857 / 1000000) : ℝ) = ((1000000 / 1172857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (47444421 / 250000000) ≤ -Real.log (827143 / 1000000) ∧
    -Real.log (827143 / 1000000) ≤ (37955537 / 200000000) := by
  have h := checkLog_sound (w := (172857 / 1827143)) (n := 12)
    (lo := (47444421 / 250000000)) (hi := (37955537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 827143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 827143) = 1/(827143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37955537 / 200000000) (-47444421 / 250000000) (Real.log (827143 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (159710339 / 1000000000) ≤ -Real.log (1000000 / 1173171) ∧
    -Real.log (1000000 / 1173171) ≤ (7985517 / 50000000) := by
  have h := checkLog_sound (w := (173171 / 2173171)) (n := 12)
    (lo := (159710339 / 1000000000)) (hi := (7985517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1173171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1173171 / 1000000) = 1/(1000000 / 1173171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (159710339 / 1000000000) (7985517 / 50000000) (Real.log (1173171 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1173171 / 1000000) = -Real.log (1000000 / 1173171) := by
    rw [show ((1173171 / 1000000) : ℝ) = ((1000000 / 1173171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2971209 / 15625000) ≤ -Real.log (826829 / 1000000) ∧
    -Real.log (826829 / 1000000) ≤ (190157377 / 1000000000) := by
  have h := checkLog_sound (w := (173171 / 1826829)) (n := 12)
    (lo := (2971209 / 15625000)) (hi := (190157377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 826829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 826829) = 1/(826829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-190157377 / 1000000000) (-2971209 / 15625000) (Real.log (826829 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (352370969 / 500000000) ≤ -Real.log (31250000000 / 63228889873) ∧
    -Real.log (31250000000 / 63228889873) ≤ (35237097 / 50000000) := by
  have h := checkLog_sound (w := (728889873 / 125728889873)) (n := 12)
    (lo := (5797379 / 500000000)) (hi := (11594759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63228889873 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63228889873 / 62500000000) = 1/(31250000000 / 63228889873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (352370969 / 500000000) (35237097 / 50000000) (Real.log (63228889873 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63228889873 / 31250000000) = -Real.log (31250000000 / 63228889873) := by
    rw [show ((63228889873 / 31250000000) : ℝ) = ((31250000000 / 63228889873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353032869 / 500000000) ≤ -Real.log (500000000000 / 1013002364067) ∧
    -Real.log (500000000000 / 1013002364067) ≤ (35303287 / 50000000) := by
  have h := checkLog_sound (w := (13002364067 / 2013002364067)) (n := 12)
    (lo := (6459279 / 500000000)) (hi := (12918559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013002364067 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1013002364067 / 1000000000000) = 1/(500000000000 / 1013002364067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (353032869 / 500000000) (35303287 / 50000000) (Real.log (1013002364067 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1013002364067 / 500000000000) = -Real.log (500000000000 / 1013002364067) := by
    rw [show ((1013002364067 / 500000000000) : ℝ) = ((500000000000 / 1013002364067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (49069227 / 100000000) ≤ -Real.log (250000000000 / 408361653857) ∧
    -Real.log (250000000000 / 408361653857) ≤ (490692271 / 1000000000) := by
  have h := checkLog_sound (w := (158361653857 / 658361653857)) (n := 12)
    (lo := (49069227 / 100000000)) (hi := (490692271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408361653857 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408361653857 / 250000000000) = 1/(250000000000 / 408361653857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49069227 / 100000000) (490692271 / 1000000000) (Real.log (408361653857 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (408361653857 / 250000000000) = -Real.log (250000000000 / 408361653857) := by
    rw [show ((408361653857 / 250000000000) : ℝ) = ((250000000000 / 408361653857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245794099 / 500000000) ≤ -Real.log (500000000000 / 817455361319) ∧
    -Real.log (500000000000 / 817455361319) ≤ (491588199 / 1000000000) := by
  have h := checkLog_sound (w := (317455361319 / 1317455361319)) (n := 12)
    (lo := (245794099 / 500000000)) (hi := (491588199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817455361319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817455361319 / 500000000000) = 1/(500000000000 / 817455361319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (245794099 / 500000000) (491588199 / 1000000000) (Real.log (817455361319 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (817455361319 / 500000000000) = -Real.log (500000000000 / 817455361319) := by
    rw [show ((817455361319 / 500000000000) : ℝ) = ((500000000000 / 817455361319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (349220337 / 1000000000) ≤ -Real.log (250000000000 / 354490396461) ∧
    -Real.log (250000000000 / 354490396461) ≤ (174610169 / 500000000) := by
  have h := checkLog_sound (w := (104490396461 / 604490396461)) (n := 12)
    (lo := (349220337 / 1000000000)) (hi := (174610169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354490396461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354490396461 / 250000000000) = 1/(250000000000 / 354490396461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (349220337 / 1000000000) (174610169 / 500000000) (Real.log (354490396461 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (354490396461 / 250000000000) = -Real.log (250000000000 / 354490396461) := by
    rw [show ((354490396461 / 250000000000) : ℝ) = ((250000000000 / 354490396461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69973543 / 200000000) ≤ -Real.log (125000000000 / 177359980117) ∧
    -Real.log (125000000000 / 177359980117) ≤ (87466929 / 250000000) := by
  have h := checkLog_sound (w := (52359980117 / 302359980117)) (n := 12)
    (lo := (69973543 / 200000000)) (hi := (87466929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177359980117 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177359980117 / 125000000000) = 1/(125000000000 / 177359980117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69973543 / 200000000) (87466929 / 250000000) (Real.log (177359980117 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (177359980117 / 125000000000) = -Real.log (125000000000 / 177359980117) := by
    rw [show ((177359980117 / 125000000000) : ℝ) = ((125000000000 / 177359980117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (30447037 / 1000000000) ≤ -Real.log (970011804759 / 1000000000000) ∧
    -Real.log (970011804759 / 1000000000000) ≤ (15223519 / 500000000) := by
  have h := checkLog_sound (w := (29988195241 / 1970011804759)) (n := 12)
    (lo := (30447037 / 1000000000)) (hi := (15223519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970011804759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970011804759) = 1/(970011804759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-15223519 / 500000000) (-30447037 / 1000000000) (Real.log (970011804759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3791879 / 125000000) ≤ -Real.log (970120457551 / 1000000000000) ∧
    -Real.log (970120457551 / 1000000000000) ≤ (30335033 / 1000000000) := by
  have h := checkLog_sound (w := (29879542449 / 1970120457551)) (n := 12)
    (lo := (3791879 / 125000000)) (hi := (30335033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970120457551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970120457551) = 1/(970120457551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30335033 / 1000000000) (-3791879 / 125000000) (Real.log (970120457551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell151
