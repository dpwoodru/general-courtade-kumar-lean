import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell147
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

theorem reflection_log_1_neg : (72554479 / 250000000) ≤ -Real.log (1280 / 1711) ∧
    -Real.log (1280 / 1711) ≤ (290217917 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2991)) (n := 12)
    (lo := (72554479 / 250000000)) (hi := (290217917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711 / 1280) = 1/(1280 / 1711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72554479 / 250000000) (290217917 / 1000000000) (Real.log (1711 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1711 / 1280) = -Real.log (1280 / 1711) := by
    rw [show ((1711 / 1280) : ℝ) = ((1280 / 1711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41055617 / 100000000) ≤ -Real.log (849 / 1280) ∧
    -Real.log (849 / 1280) ≤ (410556171 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2129)) (n := 12)
    (lo := (41055617 / 100000000)) (hi := (410556171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 849) = 1/(849 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-410556171 / 1000000000) (-41055617 / 100000000) (Real.log (849 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7244487 / 25000000) ≤ -Real.log (5120 / 6841) ∧
    -Real.log (5120 / 6841) ≤ (289779481 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 11961)) (n := 12)
    (lo := (7244487 / 25000000)) (hi := (289779481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6841 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6841 / 5120) = 1/(5120 / 6841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7244487 / 25000000) (289779481 / 1000000000) (Real.log (6841 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6841 / 5120) = -Real.log (5120 / 6841) := by
    rw [show ((6841 / 5120) : ℝ) = ((5120 / 6841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (25604573 / 62500000) ≤ -Real.log (3399 / 5120) ∧
    -Real.log (3399 / 5120) ≤ (409673169 / 1000000000) := by
  have h := checkLog_sound (w := (1721 / 8519)) (n := 12)
    (lo := (25604573 / 62500000)) (hi := (409673169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3399) = 1/(3399 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-409673169 / 1000000000) (-25604573 / 62500000) (Real.log (3399 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (214188373 / 1000000000) ≤ -Real.log (125000 / 154857) ∧
    -Real.log (125000 / 154857) ≤ (107094187 / 500000000) := by
  have h := checkLog_sound (w := (29857 / 279857)) (n := 12)
    (lo := (214188373 / 1000000000)) (hi := (107094187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154857 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154857 / 125000) = 1/(125000 / 154857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (214188373 / 1000000000) (107094187 / 500000000) (Real.log (154857 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (154857 / 125000) = -Real.log (125000 / 154857) := by
    rw [show ((154857 / 125000) : ℝ) = ((125000 / 154857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136466357 / 500000000) ≤ -Real.log (95143 / 125000) ∧
    -Real.log (95143 / 125000) ≤ (54586543 / 200000000) := by
  have h := checkLog_sound (w := (29857 / 220143)) (n := 12)
    (lo := (136466357 / 500000000)) (hi := (54586543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95143) = 1/(95143 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54586543 / 200000000) (-136466357 / 500000000) (Real.log (95143 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (214528951 / 1000000000) ≤ -Real.log (500000 / 619639) ∧
    -Real.log (500000 / 619639) ≤ (26816119 / 125000000) := by
  have h := checkLog_sound (w := (119639 / 1119639)) (n := 12)
    (lo := (214528951 / 1000000000)) (hi := (26816119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619639 / 500000) = 1/(500000 / 619639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (214528951 / 1000000000) (26816119 / 125000000) (Real.log (619639 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619639 / 500000) = -Real.log (500000 / 619639) := by
    rw [show ((619639 / 500000) : ℝ) = ((500000 / 619639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4273239 / 15625000) ≤ -Real.log (380361 / 500000) ∧
    -Real.log (380361 / 500000) ≤ (273487297 / 1000000000) := by
  have h := checkLog_sound (w := (119639 / 880361)) (n := 12)
    (lo := (4273239 / 15625000)) (hi := (273487297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380361) = 1/(380361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-273487297 / 1000000000) (-4273239 / 15625000) (Real.log (380361 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (158378017 / 1000000000) ≤ -Real.log (1000000 / 1171609) ∧
    -Real.log (1000000 / 1171609) ≤ (79189009 / 500000000) := by
  have h := checkLog_sound (w := (171609 / 2171609)) (n := 12)
    (lo := (158378017 / 1000000000)) (hi := (79189009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1171609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1171609 / 1000000) = 1/(1000000 / 1171609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (158378017 / 1000000000) (79189009 / 500000000) (Real.log (1171609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1171609 / 1000000) = -Real.log (1000000 / 1171609) := by
    rw [show ((1171609 / 1000000) : ℝ) = ((1000000 / 1171609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (188270013 / 1000000000) ≤ -Real.log (828391 / 1000000) ∧
    -Real.log (828391 / 1000000) ≤ (94135007 / 500000000) := by
  have h := checkLog_sound (w := (171609 / 1828391)) (n := 12)
    (lo := (188270013 / 1000000000)) (hi := (94135007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 828391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 828391) = 1/(828391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94135007 / 500000000) (-188270013 / 1000000000) (Real.log (828391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9915321 / 62500000) ≤ -Real.log (500000 / 585961) ∧
    -Real.log (500000 / 585961) ≤ (158645137 / 1000000000) := by
  have h := checkLog_sound (w := (85961 / 1085961)) (n := 12)
    (lo := (9915321 / 62500000)) (hi := (158645137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585961 / 500000) = 1/(500000 / 585961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9915321 / 62500000) (158645137 / 1000000000) (Real.log (585961 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585961 / 500000) = -Real.log (500000 / 585961) := by
    rw [show ((585961 / 500000) : ℝ) = ((500000 / 585961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (94323963 / 500000000) ≤ -Real.log (414039 / 500000) ∧
    -Real.log (414039 / 500000) ≤ (188647927 / 1000000000) := by
  have h := checkLog_sound (w := (85961 / 914039)) (n := 12)
    (lo := (94323963 / 500000000)) (hi := (188647927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414039) = 1/(414039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-188647927 / 1000000000) (-94323963 / 500000000) (Real.log (414039 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87431581 / 125000000) ≤ -Real.log (25000000000 / 50316269491) ∧
    -Real.log (25000000000 / 50316269491) ≤ (13989053 / 20000000) := by
  have h := checkLog_sound (w := (316269491 / 100316269491)) (n := 12)
    (lo := (1576367 / 250000000)) (hi := (6305469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50316269491 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50316269491 / 50000000000) = 1/(25000000000 / 50316269491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87431581 / 125000000) (13989053 / 20000000) (Real.log (50316269491 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50316269491 / 25000000000) = -Real.log (25000000000 / 50316269491) := by
    rw [show ((50316269491 / 25000000000) : ℝ) = ((25000000000 / 50316269491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (700774087 / 1000000000) ≤ -Real.log (12500000000 / 25191401649) ∧
    -Real.log (12500000000 / 25191401649) ≤ (700774089 / 1000000000) := by
  have h := checkLog_sound (w := (191401649 / 50191401649)) (n := 12)
    (lo := (7626907 / 1000000000)) (hi := (1906727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25191401649 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25191401649 / 25000000000) = 1/(12500000000 / 25191401649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (700774087 / 1000000000) (700774089 / 1000000000) (Real.log (25191401649 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (25191401649 / 12500000000) = -Real.log (12500000000 / 25191401649) := by
    rw [show ((25191401649 / 12500000000) : ℝ) = ((12500000000 / 25191401649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (487121087 / 1000000000) ≤ -Real.log (500000000000 / 813811841123) ∧
    -Real.log (500000000000 / 813811841123) ≤ (7611267 / 15625000) := by
  have h := checkLog_sound (w := (313811841123 / 1313811841123)) (n := 12)
    (lo := (487121087 / 1000000000)) (hi := (7611267 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813811841123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813811841123 / 500000000000) = 1/(500000000000 / 813811841123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (487121087 / 1000000000) (7611267 / 15625000) (Real.log (813811841123 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (813811841123 / 500000000000) = -Real.log (500000000000 / 813811841123) := by
    rw [show ((813811841123 / 500000000000) : ℝ) = ((500000000000 / 813811841123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61002031 / 125000000) ≤ -Real.log (250000000000 / 407270330029) ∧
    -Real.log (250000000000 / 407270330029) ≤ (488016249 / 1000000000) := by
  have h := checkLog_sound (w := (157270330029 / 657270330029)) (n := 12)
    (lo := (61002031 / 125000000)) (hi := (488016249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407270330029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407270330029 / 250000000000) = 1/(250000000000 / 407270330029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61002031 / 125000000) (488016249 / 1000000000) (Real.log (407270330029 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (407270330029 / 250000000000) = -Real.log (250000000000 / 407270330029) := by
    rw [show ((407270330029 / 250000000000) : ℝ) = ((250000000000 / 407270330029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (346648031 / 1000000000) ≤ -Real.log (250000000000 / 353579710547) ∧
    -Real.log (250000000000 / 353579710547) ≤ (10832751 / 31250000) := by
  have h := checkLog_sound (w := (103579710547 / 603579710547)) (n := 12)
    (lo := (346648031 / 1000000000)) (hi := (10832751 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353579710547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353579710547 / 250000000000) = 1/(250000000000 / 353579710547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (346648031 / 1000000000) (10832751 / 31250000) (Real.log (353579710547 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353579710547 / 250000000000) = -Real.log (250000000000 / 353579710547) := by
    rw [show ((353579710547 / 250000000000) : ℝ) = ((250000000000 / 353579710547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (173646531 / 500000000) ≤ -Real.log (5000000000 / 7076157077) ∧
    -Real.log (5000000000 / 7076157077) ≤ (347293063 / 1000000000) := by
  have h := checkLog_sound (w := (2076157077 / 12076157077)) (n := 12)
    (lo := (173646531 / 500000000)) (hi := (347293063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7076157077 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7076157077 / 5000000000) = 1/(5000000000 / 7076157077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (173646531 / 500000000) (347293063 / 1000000000) (Real.log (7076157077 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7076157077 / 5000000000) = -Real.log (5000000000 / 7076157077) := by
    rw [show ((7076157077 / 5000000000) : ℝ) = ((5000000000 / 7076157077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3000279 / 100000000) ≤ -Real.log (242610706479 / 250000000000) ∧
    -Real.log (242610706479 / 250000000000) ≤ (30002791 / 1000000000) := by
  have h := checkLog_sound (w := (7389293521 / 492610706479)) (n := 12)
    (lo := (3000279 / 100000000)) (hi := (30002791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242610706479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242610706479) = 1/(242610706479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30002791 / 1000000000) (-3000279 / 100000000) (Real.log (242610706479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7472999 / 250000000) ≤ -Real.log (970550351119 / 1000000000000) ∧
    -Real.log (970550351119 / 1000000000000) ≤ (29891997 / 1000000000) := by
  have h := checkLog_sound (w := (29449648881 / 1970550351119)) (n := 12)
    (lo := (7472999 / 250000000)) (hi := (29891997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970550351119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970550351119) = 1/(970550351119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-29891997 / 1000000000) (-7472999 / 250000000) (Real.log (970550351119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell147
