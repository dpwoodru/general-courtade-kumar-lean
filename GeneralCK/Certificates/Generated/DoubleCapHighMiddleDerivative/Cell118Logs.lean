import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell118
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

theorem reflection_log_1_neg : (55484913 / 200000000) ≤ -Real.log (5120 / 6757) ∧
    -Real.log (5120 / 6757) ≤ (138712283 / 500000000) := by
  have h := checkLog_sound (w := (1637 / 11877)) (n := 12)
    (lo := (55484913 / 200000000)) (hi := (138712283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6757 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6757 / 5120) = 1/(5120 / 6757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55484913 / 200000000) (138712283 / 500000000) (Real.log (6757 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6757 / 5120) = -Real.log (5120 / 6757) := by
    rw [show ((6757 / 5120) : ℝ) = ((5120 / 6757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (385260447 / 1000000000) ≤ -Real.log (3483 / 5120) ∧
    -Real.log (3483 / 5120) ≤ (12039389 / 31250000) := by
  have h := checkLog_sound (w := (1637 / 8603)) (n := 12)
    (lo := (385260447 / 1000000000)) (hi := (12039389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3483) = 1/(3483 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12039389 / 31250000) (-385260447 / 1000000000) (Real.log (3483 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (138490241 / 500000000) ≤ -Real.log (2560 / 3377) ∧
    -Real.log (2560 / 3377) ≤ (276980483 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 5937)) (n := 12)
    (lo := (138490241 / 500000000)) (hi := (276980483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3377 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3377 / 2560) = 1/(2560 / 3377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (138490241 / 500000000) (276980483 / 1000000000) (Real.log (3377 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3377 / 2560) = -Real.log (2560 / 3377) := by
    rw [show ((3377 / 2560) : ℝ) = ((2560 / 3377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (384399491 / 1000000000) ≤ -Real.log (1743 / 2560) ∧
    -Real.log (1743 / 2560) ≤ (96099873 / 250000000) := by
  have h := checkLog_sound (w := (817 / 4303)) (n := 12)
    (lo := (384399491 / 1000000000)) (hi := (96099873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1743) = 1/(1743 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-96099873 / 250000000) (-384399491 / 1000000000) (Real.log (1743 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2553749 / 12500000) ≤ -Real.log (500000 / 613333) ∧
    -Real.log (500000 / 613333) ≤ (204299921 / 1000000000) := by
  have h := checkLog_sound (w := (113333 / 1113333)) (n := 12)
    (lo := (2553749 / 12500000)) (hi := (204299921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613333 / 500000) = 1/(500000 / 613333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2553749 / 12500000) (204299921 / 1000000000) (Real.log (613333 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613333 / 500000) = -Real.log (500000 / 613333) := by
    rw [show ((613333 / 500000) : ℝ) = ((500000 / 613333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3213053 / 12500000) ≤ -Real.log (386667 / 500000) ∧
    -Real.log (386667 / 500000) ≤ (257044241 / 1000000000) := by
  have h := checkLog_sound (w := (113333 / 886667)) (n := 12)
    (lo := (3213053 / 12500000)) (hi := (257044241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386667) = 1/(386667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-257044241 / 1000000000) (-3213053 / 12500000) (Real.log (386667 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (204643067 / 1000000000) ≤ -Real.log (1000000 / 1227087) ∧
    -Real.log (1000000 / 1227087) ≤ (51160767 / 250000000) := by
  have h := checkLog_sound (w := (227087 / 2227087)) (n := 12)
    (lo := (204643067 / 1000000000)) (hi := (51160767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227087 / 1000000) = 1/(1000000 / 1227087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (204643067 / 1000000000) (51160767 / 250000000) (Real.log (1227087 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227087 / 1000000) = -Real.log (1000000 / 1227087) := by
    rw [show ((1227087 / 1000000) : ℝ) = ((1000000 / 1227087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (51517757 / 200000000) ≤ -Real.log (772913 / 1000000) ∧
    -Real.log (772913 / 1000000) ≤ (128794393 / 500000000) := by
  have h := checkLog_sound (w := (227087 / 1772913)) (n := 12)
    (lo := (51517757 / 200000000)) (hi := (128794393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772913) = 1/(772913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128794393 / 500000000) (-51517757 / 200000000) (Real.log (772913 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30130399 / 200000000) ≤ -Real.log (31250 / 36331) ∧
    -Real.log (31250 / 36331) ≤ (37662999 / 250000000) := by
  have h := checkLog_sound (w := (5081 / 67581)) (n := 12)
    (lo := (30130399 / 200000000)) (hi := (37662999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36331 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36331 / 31250) = 1/(31250 / 36331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30130399 / 200000000) (37662999 / 250000000) (Real.log (36331 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36331 / 31250) = -Real.log (31250 / 36331) := by
    rw [show ((36331 / 31250) : ℝ) = ((31250 / 36331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5545121 / 31250000) ≤ -Real.log (26169 / 31250) ∧
    -Real.log (26169 / 31250) ≤ (177443873 / 1000000000) := by
  have h := checkLog_sound (w := (5081 / 57419)) (n := 12)
    (lo := (5545121 / 31250000)) (hi := (177443873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26169) = 1/(26169 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177443873 / 1000000000) (-5545121 / 31250000) (Real.log (26169 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30183893 / 200000000) ≤ -Real.log (1000000 / 1162903) ∧
    -Real.log (1000000 / 1162903) ≤ (75459733 / 500000000) := by
  have h := checkLog_sound (w := (162903 / 2162903)) (n := 12)
    (lo := (30183893 / 200000000)) (hi := (75459733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162903 / 1000000) = 1/(1000000 / 1162903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30183893 / 200000000) (75459733 / 500000000) (Real.log (1162903 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162903 / 1000000) = -Real.log (1000000 / 1162903) := by
    rw [show ((1162903 / 1000000) : ℝ) = ((1000000 / 1162903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7112613 / 40000000) ≤ -Real.log (837097 / 1000000) ∧
    -Real.log (837097 / 1000000) ≤ (88907663 / 500000000) := by
  have h := checkLog_sound (w := (162903 / 1837097)) (n := 12)
    (lo := (7112613 / 40000000)) (hi := (88907663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837097) = 1/(837097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88907663 / 500000000) (-7112613 / 40000000) (Real.log (837097 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (330689987 / 500000000) ≤ -Real.log (500000000000 / 968732071141) ∧
    -Real.log (500000000000 / 968732071141) ≤ (26455199 / 40000000) := by
  have h := checkLog_sound (w := (468732071141 / 1468732071141)) (n := 12)
    (lo := (330689987 / 500000000)) (hi := (26455199 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968732071141 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968732071141 / 500000000000) = 1/(500000000000 / 968732071141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (330689987 / 500000000) (26455199 / 40000000) (Real.log (968732071141 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (968732071141 / 500000000000) = -Real.log (500000000000 / 968732071141) := by
    rw [show ((968732071141 / 500000000000) : ℝ) = ((500000000000 / 968732071141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (662685013 / 1000000000) ≤ -Real.log (31250000000 / 60624820557) ∧
    -Real.log (31250000000 / 60624820557) ≤ (331342507 / 500000000) := by
  have h := checkLog_sound (w := (29374820557 / 91874820557)) (n := 12)
    (lo := (662685013 / 1000000000)) (hi := (331342507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60624820557 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60624820557 / 31250000000) = 1/(31250000000 / 60624820557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (662685013 / 1000000000) (331342507 / 500000000) (Real.log (60624820557 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (60624820557 / 31250000000) = -Real.log (31250000000 / 60624820557) := by
    rw [show ((60624820557 / 31250000000) : ℝ) = ((31250000000 / 60624820557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (2883401 / 6250000) ≤ -Real.log (125000000000 / 198275583383) ∧
    -Real.log (125000000000 / 198275583383) ≤ (461344161 / 1000000000) := by
  have h := checkLog_sound (w := (73275583383 / 323275583383)) (n := 12)
    (lo := (2883401 / 6250000)) (hi := (461344161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198275583383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198275583383 / 125000000000) = 1/(125000000000 / 198275583383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2883401 / 6250000) (461344161 / 1000000000) (Real.log (198275583383 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (198275583383 / 125000000000) = -Real.log (125000000000 / 198275583383) := by
    rw [show ((198275583383 / 125000000000) : ℝ) = ((125000000000 / 198275583383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (462231853 / 1000000000) ≤ -Real.log (500000000000 / 793806676819) ∧
    -Real.log (500000000000 / 793806676819) ≤ (231115927 / 500000000) := by
  have h := checkLog_sound (w := (293806676819 / 1293806676819)) (n := 12)
    (lo := (462231853 / 1000000000)) (hi := (231115927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793806676819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793806676819 / 500000000000) = 1/(500000000000 / 793806676819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (462231853 / 1000000000) (231115927 / 500000000) (Real.log (793806676819 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (793806676819 / 500000000000) = -Real.log (500000000000 / 793806676819) := by
    rw [show ((793806676819 / 500000000000) : ℝ) = ((500000000000 / 793806676819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (328095867 / 1000000000) ≤ -Real.log (250000000000 / 347080515113) ∧
    -Real.log (250000000000 / 347080515113) ≤ (82023967 / 250000000) := by
  have h := checkLog_sound (w := (97080515113 / 597080515113)) (n := 12)
    (lo := (328095867 / 1000000000)) (hi := (82023967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347080515113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347080515113 / 250000000000) = 1/(250000000000 / 347080515113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (328095867 / 1000000000) (82023967 / 250000000) (Real.log (347080515113 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (347080515113 / 250000000000) = -Real.log (250000000000 / 347080515113) := by
    rw [show ((347080515113 / 250000000000) : ℝ) = ((250000000000 / 347080515113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32873479 / 100000000) ≤ -Real.log (50000000000 / 69460468739) ∧
    -Real.log (50000000000 / 69460468739) ≤ (328734791 / 1000000000) := by
  have h := checkLog_sound (w := (19460468739 / 119460468739)) (n := 12)
    (lo := (32873479 / 100000000)) (hi := (328734791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69460468739 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69460468739 / 50000000000) = 1/(50000000000 / 69460468739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32873479 / 100000000) (328734791 / 1000000000) (Real.log (69460468739 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (69460468739 / 50000000000) = -Real.log (50000000000 / 69460468739) := by
    rw [show ((69460468739 / 50000000000) : ℝ) = ((50000000000 / 69460468739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1344793 / 50000000) ≤ -Real.log (973462612591 / 1000000000000) ∧
    -Real.log (973462612591 / 1000000000000) ≤ (26895861 / 1000000000) := by
  have h := checkLog_sound (w := (26537387409 / 1973462612591)) (n := 12)
    (lo := (1344793 / 50000000)) (hi := (26895861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973462612591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973462612591) = 1/(973462612591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26895861 / 1000000000) (-1344793 / 50000000) (Real.log (973462612591 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6697969 / 250000000) ≤ -Real.log (950745939 / 976562500) ∧
    -Real.log (950745939 / 976562500) ≤ (26791877 / 1000000000) := by
  have h := checkLog_sound (w := (25816561 / 1927308439)) (n := 12)
    (lo := (6697969 / 250000000)) (hi := (26791877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 950745939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 950745939) = 1/(950745939 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26791877 / 1000000000) (-6697969 / 250000000) (Real.log (950745939 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell118
