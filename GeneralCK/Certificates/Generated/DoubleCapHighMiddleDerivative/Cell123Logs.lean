import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell123
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

theorem reflection_log_1_neg : (11185681 / 40000000) ≤ -Real.log (1280 / 1693) ∧
    -Real.log (1280 / 1693) ≤ (139821013 / 500000000) := by
  have h := checkLog_sound (w := (413 / 2973)) (n := 12)
    (lo := (11185681 / 40000000)) (hi := (139821013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693 / 1280) = 1/(1280 / 1693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11185681 / 40000000) (139821013 / 500000000) (Real.log (1693 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1693 / 1280) = -Real.log (1280 / 1693) := by
    rw [show ((1693 / 1280) : ℝ) = ((1280 / 1693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19478819 / 50000000) ≤ -Real.log (867 / 1280) ∧
    -Real.log (867 / 1280) ≤ (389576381 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2147)) (n := 12)
    (lo := (19478819 / 50000000)) (hi := (389576381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 867) = 1/(867 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-389576381 / 1000000000) (-19478819 / 50000000) (Real.log (867 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (139599463 / 500000000) ≤ -Real.log (5120 / 6769) ∧
    -Real.log (5120 / 6769) ≤ (279198927 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 11889)) (n := 12)
    (lo := (139599463 / 500000000)) (hi := (279198927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6769 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6769 / 5120) = 1/(5120 / 6769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (139599463 / 500000000) (279198927 / 1000000000) (Real.log (6769 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6769 / 5120) = -Real.log (5120 / 6769) := by
    rw [show ((6769 / 5120) : ℝ) = ((5120 / 6769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (194355851 / 500000000) ≤ -Real.log (3471 / 5120) ∧
    -Real.log (3471 / 5120) ≤ (388711703 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 8591)) (n := 12)
    (lo := (194355851 / 500000000)) (hi := (388711703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3471) = 1/(3471 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-388711703 / 1000000000) (-194355851 / 500000000) (Real.log (3471 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (206011227 / 1000000000) ≤ -Real.log (1000000 / 1228767) ∧
    -Real.log (1000000 / 1228767) ≤ (51502807 / 250000000) := by
  have h := checkLog_sound (w := (228767 / 2228767)) (n := 12)
    (lo := (206011227 / 1000000000)) (hi := (51502807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228767 / 1000000) = 1/(1000000 / 1228767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (206011227 / 1000000000) (51502807 / 250000000) (Real.log (1228767 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1228767 / 1000000) = -Real.log (1000000 / 1228767) := by
    rw [show ((1228767 / 1000000) : ℝ) = ((1000000 / 1228767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (129882373 / 500000000) ≤ -Real.log (771233 / 1000000) ∧
    -Real.log (771233 / 1000000) ≤ (259764747 / 1000000000) := by
  have h := checkLog_sound (w := (228767 / 1771233)) (n := 12)
    (lo := (129882373 / 500000000)) (hi := (259764747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771233) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771233) = 1/(771233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259764747 / 1000000000) (-129882373 / 500000000) (Real.log (771233 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (51588447 / 250000000) ≤ -Real.log (250000 / 307297) ∧
    -Real.log (250000 / 307297) ≤ (206353789 / 1000000000) := by
  have h := checkLog_sound (w := (57297 / 557297)) (n := 12)
    (lo := (51588447 / 250000000)) (hi := (206353789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307297 / 250000) = 1/(250000 / 307297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (51588447 / 250000000) (206353789 / 1000000000) (Real.log (307297 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307297 / 250000) = -Real.log (250000 / 307297) := by
    rw [show ((307297 / 250000) : ℝ) = ((250000 / 307297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (130155387 / 500000000) ≤ -Real.log (192703 / 250000) ∧
    -Real.log (192703 / 250000) ≤ (10412431 / 40000000) := by
  have h := checkLog_sound (w := (57297 / 442703)) (n := 12)
    (lo := (130155387 / 500000000)) (hi := (10412431 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192703) = 1/(192703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10412431 / 40000000) (-130155387 / 500000000) (Real.log (192703 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151985193 / 1000000000) ≤ -Real.log (1000000 / 1164143) ∧
    -Real.log (1000000 / 1164143) ≤ (75992597 / 500000000) := by
  have h := checkLog_sound (w := (164143 / 2164143)) (n := 12)
    (lo := (151985193 / 1000000000)) (hi := (75992597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164143 / 1000000) = 1/(1000000 / 1164143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151985193 / 1000000000) (75992597 / 500000000) (Real.log (1164143 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164143 / 1000000) = -Real.log (1000000 / 1164143) := by
    rw [show ((1164143 / 1000000) : ℝ) = ((1000000 / 1164143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (179297733 / 1000000000) ≤ -Real.log (835857 / 1000000) ∧
    -Real.log (835857 / 1000000) ≤ (89648867 / 500000000) := by
  have h := checkLog_sound (w := (164143 / 1835857)) (n := 12)
    (lo := (179297733 / 1000000000)) (hi := (89648867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835857) = 1/(835857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-89648867 / 500000000) (-179297733 / 1000000000) (Real.log (835857 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152252307 / 1000000000) ≤ -Real.log (500000 / 582227) ∧
    -Real.log (500000 / 582227) ≤ (38063077 / 250000000) := by
  have h := checkLog_sound (w := (82227 / 1082227)) (n := 12)
    (lo := (152252307 / 1000000000)) (hi := (38063077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582227 / 500000) = 1/(500000 / 582227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152252307 / 1000000000) (38063077 / 250000000) (Real.log (582227 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (582227 / 500000) = -Real.log (500000 / 582227) := by
    rw [show ((582227 / 500000) : ℝ) = ((500000 / 582227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1437359 / 8000000) ≤ -Real.log (417773 / 500000) ∧
    -Real.log (417773 / 500000) ≤ (44917469 / 250000000) := by
  have h := checkLog_sound (w := (82227 / 917773)) (n := 12)
    (lo := (1437359 / 8000000)) (hi := (44917469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417773) = 1/(417773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-44917469 / 250000000) (-1437359 / 8000000) (Real.log (417773 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166977657 / 250000000) ≤ -Real.log (31250000000 / 60942451743) ∧
    -Real.log (31250000000 / 60942451743) ≤ (667910629 / 1000000000) := by
  have h := checkLog_sound (w := (29692451743 / 92192451743)) (n := 12)
    (lo := (166977657 / 250000000)) (hi := (667910629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60942451743 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60942451743 / 31250000000) = 1/(31250000000 / 60942451743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166977657 / 250000000) (667910629 / 1000000000) (Real.log (60942451743 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60942451743 / 31250000000) = -Real.log (31250000000 / 60942451743) := by
    rw [show ((60942451743 / 31250000000) : ℝ) = ((31250000000 / 60942451743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133843681 / 200000000) ≤ -Real.log (250000000000 / 488177623991) ∧
    -Real.log (250000000000 / 488177623991) ≤ (334609203 / 500000000) := by
  have h := checkLog_sound (w := (238177623991 / 738177623991)) (n := 12)
    (lo := (133843681 / 200000000)) (hi := (334609203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488177623991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488177623991 / 250000000000) = 1/(250000000000 / 488177623991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (133843681 / 200000000) (334609203 / 500000000) (Real.log (488177623991 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (488177623991 / 250000000000) = -Real.log (250000000000 / 488177623991) := by
    rw [show ((488177623991 / 250000000000) : ℝ) = ((250000000000 / 488177623991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (465775973 / 1000000000) ≤ -Real.log (500000000000 / 796625014749) ∧
    -Real.log (500000000000 / 796625014749) ≤ (232887987 / 500000000) := by
  have h := checkLog_sound (w := (296625014749 / 1296625014749)) (n := 12)
    (lo := (465775973 / 1000000000)) (hi := (232887987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796625014749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796625014749 / 500000000000) = 1/(500000000000 / 796625014749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (465775973 / 1000000000) (232887987 / 500000000) (Real.log (796625014749 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (796625014749 / 500000000000) = -Real.log (500000000000 / 796625014749) := by
    rw [show ((796625014749 / 500000000000) : ℝ) = ((500000000000 / 796625014749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (466664563 / 1000000000) ≤ -Real.log (500000000000 / 797333201871) ∧
    -Real.log (500000000000 / 797333201871) ≤ (116666141 / 250000000) := by
  have h := checkLog_sound (w := (297333201871 / 1297333201871)) (n := 12)
    (lo := (466664563 / 1000000000)) (hi := (116666141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797333201871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797333201871 / 500000000000) = 1/(500000000000 / 797333201871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (466664563 / 1000000000) (116666141 / 250000000) (Real.log (797333201871 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (797333201871 / 500000000000) = -Real.log (500000000000 / 797333201871) := by
    rw [show ((797333201871 / 500000000000) : ℝ) = ((500000000000 / 797333201871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (331282927 / 1000000000) ≤ -Real.log (500000000000 / 696376892219) ∧
    -Real.log (500000000000 / 696376892219) ≤ (20705183 / 62500000) := by
  have h := checkLog_sound (w := (196376892219 / 1196376892219)) (n := 12)
    (lo := (331282927 / 1000000000)) (hi := (20705183 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696376892219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696376892219 / 500000000000) = 1/(500000000000 / 696376892219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (331282927 / 1000000000) (20705183 / 62500000) (Real.log (696376892219 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (696376892219 / 500000000000) = -Real.log (500000000000 / 696376892219) := by
    rw [show ((696376892219 / 500000000000) : ℝ) = ((500000000000 / 696376892219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (331922183 / 1000000000) ≤ -Real.log (500000000000 / 696822197701) ∧
    -Real.log (500000000000 / 696822197701) ≤ (41490273 / 125000000) := by
  have h := checkLog_sound (w := (196822197701 / 1196822197701)) (n := 12)
    (lo := (331922183 / 1000000000)) (hi := (41490273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696822197701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696822197701 / 500000000000) = 1/(500000000000 / 696822197701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (331922183 / 1000000000) (41490273 / 125000000) (Real.log (696822197701 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (696822197701 / 500000000000) = -Real.log (500000000000 / 696822197701) := by
    rw [show ((696822197701 / 500000000000) : ℝ) = ((500000000000 / 696822197701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27417567 / 1000000000) ≤ -Real.log (243238720471 / 250000000000) ∧
    -Real.log (243238720471 / 250000000000) ≤ (856799 / 31250000) := by
  have h := checkLog_sound (w := (6761279529 / 493238720471)) (n := 12)
    (lo := (27417567 / 1000000000)) (hi := (856799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243238720471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243238720471) = 1/(243238720471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-856799 / 31250000) (-27417567 / 1000000000) (Real.log (243238720471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27312539 / 1000000000) ≤ -Real.log (973057075551 / 1000000000000) ∧
    -Real.log (973057075551 / 1000000000000) ≤ (1365627 / 50000000) := by
  have h := checkLog_sound (w := (26942924449 / 1973057075551)) (n := 12)
    (lo := (27312539 / 1000000000)) (hi := (1365627 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973057075551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973057075551) = 1/(973057075551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1365627 / 50000000) (-27312539 / 1000000000) (Real.log (973057075551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell123
