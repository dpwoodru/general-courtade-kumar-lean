import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell096
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

theorem reflection_log_1_neg : (2676089 / 10000000) ≤ -Real.log (5120 / 6691) ∧
    -Real.log (5120 / 6691) ≤ (267608901 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 11811)) (n := 12)
    (lo := (2676089 / 10000000)) (hi := (267608901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6691 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6691 / 5120) = 1/(5120 / 6691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2676089 / 10000000) (267608901 / 1000000000) (Real.log (6691 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6691 / 5120) = -Real.log (5120 / 6691) := by
    rw [show ((6691 / 5120) : ℝ) = ((5120 / 6691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73297713 / 200000000) ≤ -Real.log (3549 / 5120) ∧
    -Real.log (3549 / 5120) ≤ (183244283 / 500000000) := by
  have h := checkLog_sound (w := (1571 / 8669)) (n := 12)
    (lo := (73297713 / 200000000)) (hi := (183244283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3549) = 1/(3549 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-183244283 / 500000000) (-73297713 / 200000000) (Real.log (3549 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66790109 / 250000000) ≤ -Real.log (160 / 209) ∧
    -Real.log (160 / 209) ≤ (267160437 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 369)) (n := 12)
    (lo := (66790109 / 250000000)) (hi := (267160437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209 / 160) = 1/(160 / 209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66790109 / 250000000) (267160437 / 1000000000) (Real.log (209 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (209 / 160) = -Real.log (160 / 209) := by
    rw [show ((209 / 160) : ℝ) = ((160 / 209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (365643613 / 1000000000) ≤ -Real.log (111 / 160) ∧
    -Real.log (111 / 160) ≤ (182821807 / 500000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 111) = 1/(111 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-182821807 / 500000000) (-365643613 / 1000000000) (Real.log (111 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (98371861 / 500000000) ≤ -Real.log (125000 / 152179) ∧
    -Real.log (125000 / 152179) ≤ (196743723 / 1000000000) := by
  have h := checkLog_sound (w := (27179 / 277179)) (n := 12)
    (lo := (98371861 / 500000000)) (hi := (196743723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152179 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152179 / 125000) = 1/(125000 / 152179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (98371861 / 500000000) (196743723 / 1000000000) (Real.log (152179 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (152179 / 125000) = -Real.log (125000 / 152179) := by
    rw [show ((152179 / 125000) : ℝ) = ((125000 / 152179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245174459 / 1000000000) ≤ -Real.log (97821 / 125000) ∧
    -Real.log (97821 / 125000) ≤ (12258723 / 50000000) := by
  have h := checkLog_sound (w := (27179 / 222821)) (n := 12)
    (lo := (245174459 / 1000000000)) (hi := (12258723 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97821) = 1/(97821 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12258723 / 50000000) (-245174459 / 1000000000) (Real.log (97821 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197088651 / 1000000000) ≤ -Real.log (250000 / 304463) ∧
    -Real.log (250000 / 304463) ≤ (49272163 / 250000000) := by
  have h := checkLog_sound (w := (54463 / 554463)) (n := 12)
    (lo := (197088651 / 1000000000)) (hi := (49272163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304463 / 250000) = 1/(250000 / 304463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197088651 / 1000000000) (49272163 / 250000000) (Real.log (304463 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (304463 / 250000) = -Real.log (250000 / 304463) := by
    rw [show ((304463 / 250000) : ℝ) = ((250000 / 304463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (122855649 / 500000000) ≤ -Real.log (195537 / 250000) ∧
    -Real.log (195537 / 250000) ≤ (245711299 / 1000000000) := by
  have h := checkLog_sound (w := (54463 / 445537)) (n := 12)
    (lo := (122855649 / 500000000)) (hi := (245711299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195537) = 1/(195537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-245711299 / 1000000000) (-122855649 / 500000000) (Real.log (195537 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72391181 / 500000000) ≤ -Real.log (250000 / 288947) ∧
    -Real.log (250000 / 288947) ≤ (144782363 / 1000000000) := by
  have h := checkLog_sound (w := (38947 / 538947)) (n := 12)
    (lo := (72391181 / 500000000)) (hi := (144782363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288947 / 250000) = 1/(250000 / 288947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72391181 / 500000000) (144782363 / 1000000000) (Real.log (288947 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (288947 / 250000) = -Real.log (250000 / 288947) := by
    rw [show ((288947 / 250000) : ℝ) = ((250000 / 288947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (169351631 / 1000000000) ≤ -Real.log (211053 / 250000) ∧
    -Real.log (211053 / 250000) ≤ (10584477 / 62500000) := by
  have h := checkLog_sound (w := (38947 / 461053)) (n := 12)
    (lo := (169351631 / 1000000000)) (hi := (10584477 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211053) = 1/(211053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-10584477 / 62500000) (-169351631 / 1000000000) (Real.log (211053 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145050541 / 1000000000) ≤ -Real.log (500000 / 578049) ∧
    -Real.log (500000 / 578049) ≤ (72525271 / 500000000) := by
  have h := checkLog_sound (w := (78049 / 1078049)) (n := 12)
    (lo := (145050541 / 1000000000)) (hi := (72525271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578049 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578049 / 500000) = 1/(500000 / 578049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145050541 / 1000000000) (72525271 / 500000000) (Real.log (578049 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (578049 / 500000) = -Real.log (500000 / 578049) := by
    rw [show ((578049 / 500000) : ℝ) = ((500000 / 578049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21214863 / 125000000) ≤ -Real.log (421951 / 500000) ∧
    -Real.log (421951 / 500000) ≤ (33943781 / 200000000) := by
  have h := checkLog_sound (w := (78049 / 921951)) (n := 12)
    (lo := (21214863 / 125000000)) (hi := (33943781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421951) = 1/(421951 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33943781 / 200000000) (-21214863 / 125000000) (Real.log (421951 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (12656081 / 20000000) ≤ -Real.log (500000000000 / 941441441441) ∧
    -Real.log (500000000000 / 941441441441) ≤ (632804051 / 1000000000) := by
  have h := checkLog_sound (w := (441441441441 / 1441441441441)) (n := 12)
    (lo := (12656081 / 20000000)) (hi := (632804051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941441441441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941441441441 / 500000000000) = 1/(500000000000 / 941441441441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (12656081 / 20000000) (632804051 / 1000000000) (Real.log (941441441441 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (941441441441 / 500000000000) = -Real.log (500000000000 / 941441441441) := by
    rw [show ((941441441441 / 500000000000) : ℝ) = ((500000000000 / 941441441441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (317048733 / 500000000) ≤ -Real.log (500000000000 / 942659904199) ∧
    -Real.log (500000000000 / 942659904199) ≤ (634097467 / 1000000000) := by
  have h := checkLog_sound (w := (442659904199 / 1442659904199)) (n := 12)
    (lo := (317048733 / 500000000)) (hi := (634097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((942659904199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(942659904199 / 500000000000) = 1/(500000000000 / 942659904199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (317048733 / 500000000) (634097467 / 1000000000) (Real.log (942659904199 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (942659904199 / 500000000000) = -Real.log (500000000000 / 942659904199) := by
    rw [show ((942659904199 / 500000000000) : ℝ) = ((500000000000 / 942659904199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (441918181 / 1000000000) ≤ -Real.log (500000000000 / 777844225677) ∧
    -Real.log (500000000000 / 777844225677) ≤ (220959091 / 500000000) := by
  have h := checkLog_sound (w := (277844225677 / 1277844225677)) (n := 12)
    (lo := (441918181 / 1000000000)) (hi := (220959091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777844225677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777844225677 / 500000000000) = 1/(500000000000 / 777844225677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (441918181 / 1000000000) (220959091 / 500000000) (Real.log (777844225677 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (777844225677 / 500000000000) = -Real.log (500000000000 / 777844225677) := by
    rw [show ((777844225677 / 500000000000) : ℝ) = ((500000000000 / 777844225677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (442799949 / 1000000000) ≤ -Real.log (500000000000 / 778530406011) ∧
    -Real.log (500000000000 / 778530406011) ≤ (8855999 / 20000000) := by
  have h := checkLog_sound (w := (278530406011 / 1278530406011)) (n := 12)
    (lo := (442799949 / 1000000000)) (hi := (8855999 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778530406011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(778530406011 / 500000000000) = 1/(500000000000 / 778530406011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (442799949 / 1000000000) (8855999 / 20000000) (Real.log (778530406011 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (778530406011 / 500000000000) = -Real.log (500000000000 / 778530406011) := by
    rw [show ((778530406011 / 500000000000) : ℝ) = ((500000000000 / 778530406011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (314133993 / 1000000000) ≤ -Real.log (125000000000 / 171134146399) ∧
    -Real.log (125000000000 / 171134146399) ≤ (157066997 / 500000000) := by
  have h := checkLog_sound (w := (46134146399 / 296134146399)) (n := 12)
    (lo := (314133993 / 1000000000)) (hi := (157066997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171134146399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171134146399 / 125000000000) = 1/(125000000000 / 171134146399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (314133993 / 1000000000) (157066997 / 500000000) (Real.log (171134146399 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171134146399 / 125000000000) = -Real.log (125000000000 / 171134146399) := by
    rw [show ((171134146399 / 125000000000) : ℝ) = ((125000000000 / 171134146399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (157384723 / 500000000) ≤ -Real.log (250000000000 / 342485857363) ∧
    -Real.log (250000000000 / 342485857363) ≤ (314769447 / 1000000000) := by
  have h := checkLog_sound (w := (92485857363 / 592485857363)) (n := 12)
    (lo := (157384723 / 500000000)) (hi := (314769447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342485857363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342485857363 / 250000000000) = 1/(250000000000 / 342485857363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (157384723 / 500000000) (314769447 / 1000000000) (Real.log (342485857363 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342485857363 / 250000000000) = -Real.log (250000000000 / 342485857363) := by
    rw [show ((342485857363 / 250000000000) : ℝ) = ((250000000000 / 342485857363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (24668363 / 1000000000) ≤ -Real.log (243908353599 / 250000000000) ∧
    -Real.log (243908353599 / 250000000000) ≤ (6167091 / 250000000) := by
  have h := checkLog_sound (w := (6091646401 / 493908353599)) (n := 12)
    (lo := (24668363 / 1000000000)) (hi := (6167091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243908353599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243908353599) = 1/(243908353599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6167091 / 250000000) (-24668363 / 1000000000) (Real.log (243908353599 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6142317 / 250000000) ≤ -Real.log (60983131191 / 62500000000) ∧
    -Real.log (60983131191 / 62500000000) ≤ (24569269 / 1000000000) := by
  have h := checkLog_sound (w := (1516868809 / 123483131191)) (n := 12)
    (lo := (6142317 / 250000000)) (hi := (24569269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60983131191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60983131191) = 1/(60983131191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-24569269 / 1000000000) (-6142317 / 250000000) (Real.log (60983131191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell096
