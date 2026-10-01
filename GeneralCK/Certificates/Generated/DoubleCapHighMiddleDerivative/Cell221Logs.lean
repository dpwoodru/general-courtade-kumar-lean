import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell221
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

theorem reflection_log_1_neg : (322140109 / 1000000000) ≤ -Real.log (2560 / 3533) ∧
    -Real.log (2560 / 3533) ≤ (32214011 / 100000000) := by
  have h := checkLog_sound (w := (973 / 6093)) (n := 12)
    (lo := (322140109 / 1000000000)) (hi := (32214011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3533 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3533 / 2560) = 1/(2560 / 3533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (322140109 / 1000000000) (32214011 / 100000000) (Real.log (3533 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3533 / 2560) = -Real.log (2560 / 3533) := by
    rw [show ((3533 / 2560) : ℝ) = ((2560 / 3533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (59770227 / 125000000) ≤ -Real.log (1587 / 2560) ∧
    -Real.log (1587 / 2560) ≤ (478161817 / 1000000000) := by
  have h := checkLog_sound (w := (973 / 4147)) (n := 12)
    (lo := (59770227 / 125000000)) (hi := (478161817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1587) = 1/(1587 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-478161817 / 1000000000) (-59770227 / 125000000) (Real.log (1587 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (321715451 / 1000000000) ≤ -Real.log (5120 / 7063) ∧
    -Real.log (5120 / 7063) ≤ (80428863 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 12183)) (n := 12)
    (lo := (321715451 / 1000000000)) (hi := (80428863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7063 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7063 / 5120) = 1/(5120 / 7063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (321715451 / 1000000000) (80428863 / 250000000) (Real.log (7063 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7063 / 5120) = -Real.log (5120 / 7063) := by
    rw [show ((7063 / 5120) : ℝ) = ((5120 / 7063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (477217083 / 1000000000) ≤ -Real.log (3177 / 5120) ∧
    -Real.log (3177 / 5120) ≤ (119304271 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 8297)) (n := 12)
    (lo := (477217083 / 1000000000)) (hi := (119304271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3177) = 1/(3177 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-119304271 / 250000000) (-477217083 / 1000000000) (Real.log (3177 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119530103 / 500000000) ≤ -Real.log (200000 / 254011) ∧
    -Real.log (200000 / 254011) ≤ (239060207 / 1000000000) := by
  have h := checkLog_sound (w := (54011 / 454011)) (n := 12)
    (lo := (119530103 / 500000000)) (hi := (239060207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254011 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254011 / 200000) = 1/(200000 / 254011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119530103 / 500000000) (239060207 / 1000000000) (Real.log (254011 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (254011 / 200000) = -Real.log (200000 / 254011) := by
    rw [show ((254011 / 200000) : ℝ) = ((200000 / 254011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31478609 / 100000000) ≤ -Real.log (145989 / 200000) ∧
    -Real.log (145989 / 200000) ≤ (314786091 / 1000000000) := by
  have h := checkLog_sound (w := (54011 / 345989)) (n := 12)
    (lo := (31478609 / 100000000)) (hi := (314786091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145989) = 1/(145989 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-314786091 / 1000000000) (-31478609 / 100000000) (Real.log (145989 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119696997 / 500000000) ≤ -Real.log (1000000 / 1270479) ∧
    -Real.log (1000000 / 1270479) ≤ (47878799 / 200000000) := by
  have h := checkLog_sound (w := (270479 / 2270479)) (n := 12)
    (lo := (119696997 / 500000000)) (hi := (47878799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270479 / 1000000) = 1/(1000000 / 1270479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119696997 / 500000000) (47878799 / 200000000) (Real.log (1270479 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1270479 / 1000000) = -Real.log (1000000 / 1270479) := by
    rw [show ((1270479 / 1000000) : ℝ) = ((1000000 / 1270479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (78841781 / 250000000) ≤ -Real.log (729521 / 1000000) ∧
    -Real.log (729521 / 1000000) ≤ (2522937 / 8000000) := by
  have h := checkLog_sound (w := (270479 / 1729521)) (n := 12)
    (lo := (78841781 / 250000000)) (hi := (2522937 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729521) = 1/(729521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2522937 / 8000000) (-78841781 / 250000000) (Real.log (729521 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35611663 / 200000000) ≤ -Real.log (200000 / 238979) ∧
    -Real.log (200000 / 238979) ≤ (44514579 / 250000000) := by
  have h := checkLog_sound (w := (38979 / 438979)) (n := 12)
    (lo := (35611663 / 200000000)) (hi := (44514579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238979 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238979 / 200000) = 1/(200000 / 238979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35611663 / 200000000) (44514579 / 250000000) (Real.log (238979 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (238979 / 200000) = -Real.log (200000 / 238979) := by
    rw [show ((238979 / 200000) : ℝ) = ((200000 / 238979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8671303 / 40000000) ≤ -Real.log (161021 / 200000) ∧
    -Real.log (161021 / 200000) ≤ (13548911 / 62500000) := by
  have h := checkLog_sound (w := (38979 / 361021)) (n := 12)
    (lo := (8671303 / 40000000)) (hi := (13548911 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161021) = 1/(161021 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13548911 / 62500000) (-8671303 / 40000000) (Real.log (161021 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (44581103 / 250000000) ≤ -Real.log (1000000 / 1195213) ∧
    -Real.log (1000000 / 1195213) ≤ (178324413 / 1000000000) := by
  have h := checkLog_sound (w := (195213 / 2195213)) (n := 12)
    (lo := (44581103 / 250000000)) (hi := (178324413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195213 / 1000000) = 1/(1000000 / 1195213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (44581103 / 250000000) (178324413 / 1000000000) (Real.log (1195213 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195213 / 1000000) = -Real.log (1000000 / 1195213) := by
    rw [show ((1195213 / 1000000) : ℝ) = ((1000000 / 1195213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6786801 / 31250000) ≤ -Real.log (804787 / 1000000) ∧
    -Real.log (804787 / 1000000) ≤ (217177633 / 1000000000) := by
  have h := checkLog_sound (w := (195213 / 1804787)) (n := 12)
    (lo := (6786801 / 31250000)) (hi := (217177633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804787) = 1/(804787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217177633 / 1000000000) (-6786801 / 31250000) (Real.log (804787 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (399466267 / 500000000) ≤ -Real.log (250000000000 / 555791627321) ∧
    -Real.log (250000000000 / 555791627321) ≤ (99866567 / 125000000) := by
  have h := checkLog_sound (w := (55791627321 / 1055791627321)) (n := 12)
    (lo := (52892677 / 500000000)) (hi := (21157071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555791627321 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555791627321 / 500000000000) = 1/(250000000000 / 555791627321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (399466267 / 500000000) (99866567 / 125000000) (Real.log (555791627321 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (555791627321 / 250000000000) = -Real.log (250000000000 / 555791627321) := by
    rw [show ((555791627321 / 250000000000) : ℝ) = ((250000000000 / 555791627321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (400150963 / 500000000) ≤ -Real.log (250000000000 / 556553245117) ∧
    -Real.log (250000000000 / 556553245117) ≤ (100037741 / 125000000) := by
  have h := checkLog_sound (w := (56553245117 / 1056553245117)) (n := 12)
    (lo := (53577373 / 500000000)) (hi := (107154747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556553245117 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556553245117 / 500000000000) = 1/(250000000000 / 556553245117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (400150963 / 500000000) (100037741 / 125000000) (Real.log (556553245117 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (556553245117 / 250000000000) = -Real.log (250000000000 / 556553245117) := by
    rw [show ((556553245117 / 250000000000) : ℝ) = ((250000000000 / 556553245117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (69230787 / 125000000) ≤ -Real.log (125000000000 / 217491557583) ∧
    -Real.log (125000000000 / 217491557583) ≤ (553846297 / 1000000000) := by
  have h := checkLog_sound (w := (92491557583 / 342491557583)) (n := 12)
    (lo := (69230787 / 125000000)) (hi := (553846297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217491557583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217491557583 / 125000000000) = 1/(125000000000 / 217491557583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (69230787 / 125000000) (553846297 / 1000000000) (Real.log (217491557583 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (217491557583 / 125000000000) = -Real.log (125000000000 / 217491557583) := by
    rw [show ((217491557583 / 125000000000) : ℝ) = ((125000000000 / 217491557583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (554761119 / 1000000000) ≤ -Real.log (500000000000 / 870762459203) ∧
    -Real.log (500000000000 / 870762459203) ≤ (3467257 / 6250000) := by
  have h := checkLog_sound (w := (370762459203 / 1370762459203)) (n := 12)
    (lo := (554761119 / 1000000000)) (hi := (3467257 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870762459203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870762459203 / 500000000000) = 1/(500000000000 / 870762459203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (554761119 / 1000000000) (3467257 / 6250000) (Real.log (870762459203 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (870762459203 / 500000000000) = -Real.log (500000000000 / 870762459203) := by
    rw [show ((870762459203 / 500000000000) : ℝ) = ((500000000000 / 870762459203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (39484089 / 100000000) ≤ -Real.log (50000000000 / 74207401519) ∧
    -Real.log (50000000000 / 74207401519) ≤ (394840891 / 1000000000) := by
  have h := checkLog_sound (w := (24207401519 / 124207401519)) (n := 12)
    (lo := (39484089 / 100000000)) (hi := (394840891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74207401519 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74207401519 / 50000000000) = 1/(50000000000 / 74207401519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (39484089 / 100000000) (394840891 / 1000000000) (Real.log (74207401519 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (74207401519 / 50000000000) = -Real.log (50000000000 / 74207401519) := by
    rw [show ((74207401519 / 50000000000) : ℝ) = ((50000000000 / 74207401519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79100409 / 200000000) ≤ -Real.log (500000000000 / 742564802861) ∧
    -Real.log (500000000000 / 742564802861) ≤ (197751023 / 500000000) := by
  have h := checkLog_sound (w := (242564802861 / 1242564802861)) (n := 12)
    (lo := (79100409 / 200000000)) (hi := (197751023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742564802861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742564802861 / 500000000000) = 1/(500000000000 / 742564802861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79100409 / 200000000) (197751023 / 500000000) (Real.log (742564802861 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (742564802861 / 500000000000) = -Real.log (500000000000 / 742564802861) := by
    rw [show ((742564802861 / 500000000000) : ℝ) = ((500000000000 / 742564802861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1942661 / 50000000) ≤ -Real.log (961891884631 / 1000000000000) ∧
    -Real.log (961891884631 / 1000000000000) ≤ (38853221 / 1000000000) := by
  have h := checkLog_sound (w := (38108115369 / 1961891884631)) (n := 12)
    (lo := (1942661 / 50000000)) (hi := (38853221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961891884631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961891884631) = 1/(961891884631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38853221 / 1000000000) (-1942661 / 50000000) (Real.log (961891884631 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38724259 / 1000000000) ≤ -Real.log (38480637559 / 40000000000) ∧
    -Real.log (38480637559 / 40000000000) ≤ (1936213 / 50000000) := by
  have h := checkLog_sound (w := (1519362441 / 78480637559)) (n := 12)
    (lo := (38724259 / 1000000000)) (hi := (1936213 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38480637559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38480637559) = 1/(38480637559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1936213 / 50000000) (-38724259 / 1000000000) (Real.log (38480637559 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell221
