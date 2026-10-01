import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell100
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

theorem reflection_log_1_neg : (67350187 / 250000000) ≤ -Real.log (5120 / 6703) ∧
    -Real.log (5120 / 6703) ≤ (269400749 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 11823)) (n := 12)
    (lo := (67350187 / 250000000)) (hi := (269400749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6703 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6703 / 5120) = 1/(5120 / 6703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67350187 / 250000000) (269400749 / 1000000000) (Real.log (6703 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6703 / 5120) = -Real.log (5120 / 6703) := by
    rw [show ((6703 / 5120) : ℝ) = ((5120 / 6703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (46234441 / 125000000) ≤ -Real.log (3537 / 5120) ∧
    -Real.log (3537 / 5120) ≤ (369875529 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 8657)) (n := 12)
    (lo := (46234441 / 125000000)) (hi := (369875529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3537) = 1/(3537 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-369875529 / 1000000000) (-46234441 / 125000000) (Real.log (3537 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (268953087 / 1000000000) ≤ -Real.log (256 / 335) ∧
    -Real.log (256 / 335) ≤ (525299 / 1953125) := by
  have h := checkLog_sound (w := (79 / 591)) (n := 12)
    (lo := (268953087 / 1000000000)) (hi := (525299 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335 / 256) = 1/(256 / 335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (268953087 / 1000000000) (525299 / 1953125) (Real.log (335 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (335 / 256) = -Real.log (256 / 335) := by
    rw [show ((335 / 256) : ℝ) = ((256 / 335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (369027711 / 1000000000) ≤ -Real.log (177 / 256) ∧
    -Real.log (177 / 256) ≤ (2883029 / 7812500) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 177) = 1/(177 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2883029 / 7812500) (-369027711 / 1000000000) (Real.log (177 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (198119443 / 1000000000) ≤ -Real.log (250000 / 304777) ∧
    -Real.log (250000 / 304777) ≤ (49529861 / 250000000) := by
  have h := checkLog_sound (w := (54777 / 554777)) (n := 12)
    (lo := (198119443 / 1000000000)) (hi := (49529861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304777 / 250000) = 1/(250000 / 304777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (198119443 / 1000000000) (49529861 / 250000000) (Real.log (304777 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (304777 / 250000) = -Real.log (250000 / 304777) := by
    rw [show ((304777 / 250000) : ℝ) = ((250000 / 304777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (123659211 / 500000000) ≤ -Real.log (195223 / 250000) ∧
    -Real.log (195223 / 250000) ≤ (247318423 / 1000000000) := by
  have h := checkLog_sound (w := (54777 / 445223)) (n := 12)
    (lo := (123659211 / 500000000)) (hi := (247318423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 195223) = 1/(195223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247318423 / 1000000000) (-123659211 / 500000000) (Real.log (195223 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99233999 / 500000000) ≤ -Real.log (1000000 / 1219533) ∧
    -Real.log (1000000 / 1219533) ≤ (198467999 / 1000000000) := by
  have h := checkLog_sound (w := (219533 / 2219533)) (n := 12)
    (lo := (99233999 / 500000000)) (hi := (198467999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1219533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1219533 / 1000000) = 1/(1000000 / 1219533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99233999 / 500000000) (198467999 / 1000000000) (Real.log (1219533 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1219533 / 1000000) = -Real.log (1000000 / 1219533) := by
    rw [show ((1219533 / 1000000) : ℝ) = ((1000000 / 1219533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12393141 / 50000000) ≤ -Real.log (780467 / 1000000) ∧
    -Real.log (780467 / 1000000) ≤ (247862821 / 1000000000) := by
  have h := checkLog_sound (w := (219533 / 1780467)) (n := 12)
    (lo := (12393141 / 50000000)) (hi := (247862821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 780467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 780467) = 1/(780467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-247862821 / 1000000000) (-12393141 / 50000000) (Real.log (780467 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145850327 / 1000000000) ≤ -Real.log (1000000 / 1157023) ∧
    -Real.log (1000000 / 1157023) ≤ (18231291 / 125000000) := by
  have h := checkLog_sound (w := (157023 / 2157023)) (n := 12)
    (lo := (145850327 / 1000000000)) (hi := (18231291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157023 / 1000000) = 1/(1000000 / 1157023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145850327 / 1000000000) (18231291 / 125000000) (Real.log (1157023 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1157023 / 1000000) = -Real.log (1000000 / 1157023) := by
    rw [show ((1157023 / 1000000) : ℝ) = ((1000000 / 1157023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (42703901 / 250000000) ≤ -Real.log (842977 / 1000000) ∧
    -Real.log (842977 / 1000000) ≤ (34163121 / 200000000) := by
  have h := checkLog_sound (w := (157023 / 1842977)) (n := 12)
    (lo := (42703901 / 250000000)) (hi := (34163121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842977) = 1/(842977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-34163121 / 200000000) (-42703901 / 250000000) (Real.log (842977 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7305911 / 50000000) ≤ -Real.log (1000000 / 1157333) ∧
    -Real.log (1000000 / 1157333) ≤ (146118221 / 1000000000) := by
  have h := checkLog_sound (w := (157333 / 2157333)) (n := 12)
    (lo := (7305911 / 50000000)) (hi := (146118221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157333 / 1000000) = 1/(1000000 / 1157333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7305911 / 50000000) (146118221 / 1000000000) (Real.log (1157333 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1157333 / 1000000) = -Real.log (1000000 / 1157333) := by
    rw [show ((1157333 / 1000000) : ℝ) = ((1000000 / 1157333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21397927 / 125000000) ≤ -Real.log (842667 / 1000000) ∧
    -Real.log (842667 / 1000000) ≤ (171183417 / 1000000000) := by
  have h := checkLog_sound (w := (157333 / 1842667)) (n := 12)
    (lo := (21397927 / 125000000)) (hi := (171183417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 842667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 842667) = 1/(842667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171183417 / 1000000000) (-21397927 / 125000000) (Real.log (842667 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (637980799 / 1000000000) ≤ -Real.log (100000000000 / 189265536723) ∧
    -Real.log (100000000000 / 189265536723) ≤ (199369 / 312500) := by
  have h := checkLog_sound (w := (89265536723 / 289265536723)) (n := 12)
    (lo := (637980799 / 1000000000)) (hi := (199369 / 312500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189265536723 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189265536723 / 100000000000) = 1/(100000000000 / 189265536723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (637980799 / 1000000000) (199369 / 312500) (Real.log (189265536723 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (189265536723 / 100000000000) = -Real.log (100000000000 / 189265536723) := by
    rw [show ((189265536723 / 100000000000) : ℝ) = ((100000000000 / 189265536723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (639276277 / 1000000000) ≤ -Real.log (250000000000 / 473777212327) ∧
    -Real.log (250000000000 / 473777212327) ≤ (319638139 / 500000000) := by
  have h := checkLog_sound (w := (223777212327 / 723777212327)) (n := 12)
    (lo := (639276277 / 1000000000)) (hi := (319638139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((473777212327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(473777212327 / 250000000000) = 1/(250000000000 / 473777212327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (639276277 / 1000000000) (319638139 / 500000000) (Real.log (473777212327 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (473777212327 / 250000000000) = -Real.log (250000000000 / 473777212327) := by
    rw [show ((473777212327 / 250000000000) : ℝ) = ((250000000000 / 473777212327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (222718933 / 500000000) ≤ -Real.log (250000000000 / 390293408051) ∧
    -Real.log (250000000000 / 390293408051) ≤ (445437867 / 1000000000) := by
  have h := checkLog_sound (w := (140293408051 / 640293408051)) (n := 12)
    (lo := (222718933 / 500000000)) (hi := (445437867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390293408051 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390293408051 / 250000000000) = 1/(250000000000 / 390293408051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222718933 / 500000000) (445437867 / 1000000000) (Real.log (390293408051 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390293408051 / 250000000000) = -Real.log (250000000000 / 390293408051) := by
    rw [show ((390293408051 / 250000000000) : ℝ) = ((250000000000 / 390293408051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (446330819 / 1000000000) ≤ -Real.log (500000000000 / 781284154231) ∧
    -Real.log (500000000000 / 781284154231) ≤ (22316541 / 50000000) := by
  have h := checkLog_sound (w := (281284154231 / 1281284154231)) (n := 12)
    (lo := (446330819 / 1000000000)) (hi := (22316541 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781284154231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781284154231 / 500000000000) = 1/(500000000000 / 781284154231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (446330819 / 1000000000) (22316541 / 50000000) (Real.log (781284154231 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (781284154231 / 500000000000) = -Real.log (500000000000 / 781284154231) := by
    rw [show ((781284154231 / 500000000000) : ℝ) = ((500000000000 / 781284154231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (316665931 / 1000000000) ≤ -Real.log (125000000000 / 171567996517) ∧
    -Real.log (125000000000 / 171567996517) ≤ (79166483 / 250000000) := by
  have h := checkLog_sound (w := (46567996517 / 296567996517)) (n := 12)
    (lo := (316665931 / 1000000000)) (hi := (79166483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171567996517 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171567996517 / 125000000000) = 1/(125000000000 / 171567996517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (316665931 / 1000000000) (79166483 / 250000000) (Real.log (171567996517 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (171567996517 / 125000000000) = -Real.log (125000000000 / 171567996517) := by
    rw [show ((171567996517 / 125000000000) : ℝ) = ((125000000000 / 171567996517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79325409 / 250000000) ≤ -Real.log (250000000000 / 343354195667) ∧
    -Real.log (250000000000 / 343354195667) ≤ (317301637 / 1000000000) := by
  have h := checkLog_sound (w := (93354195667 / 593354195667)) (n := 12)
    (lo := (79325409 / 250000000)) (hi := (317301637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343354195667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343354195667 / 250000000000) = 1/(250000000000 / 343354195667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79325409 / 250000000) (317301637 / 1000000000) (Real.log (343354195667 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (343354195667 / 250000000000) = -Real.log (250000000000 / 343354195667) := by
    rw [show ((343354195667 / 250000000000) : ℝ) = ((250000000000 / 343354195667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6266299 / 250000000) ≤ -Real.log (975246327111 / 1000000000000) ∧
    -Real.log (975246327111 / 1000000000000) ≤ (25065197 / 1000000000) := by
  have h := checkLog_sound (w := (24753672889 / 1975246327111)) (n := 12)
    (lo := (6266299 / 250000000)) (hi := (25065197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975246327111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975246327111) = 1/(975246327111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25065197 / 1000000000) (-6266299 / 250000000) (Real.log (975246327111 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (24965277 / 1000000000) ≤ -Real.log (975343777471 / 1000000000000) ∧
    -Real.log (975343777471 / 1000000000000) ≤ (12482639 / 500000000) := by
  have h := checkLog_sound (w := (24656222529 / 1975343777471)) (n := 12)
    (lo := (24965277 / 1000000000)) (hi := (12482639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975343777471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975343777471) = 1/(975343777471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-12482639 / 500000000) (-24965277 / 1000000000) (Real.log (975343777471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell100
