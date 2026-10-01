import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0226
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (253915209 / 1000000000) ≤ -Real.log (128 / 165) ∧
    -Real.log (128 / 165) ≤ (25391521 / 100000000) := by
  have h := checkLog_sound (w := (37 / 293)) (n := 12)
    (lo := (253915209 / 1000000000)) (hi := (25391521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165 / 128) = 1/(128 / 165) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253915209 / 1000000000) (25391521 / 100000000) (Real.log (165 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (165 / 128) = -Real.log (128 / 165) := by
    rw [show ((165 / 128) : ℝ) = ((128 / 165) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (341170757 / 1000000000) ≤ -Real.log (91 / 128) ∧
    -Real.log (91 / 128) ≤ (170585379 / 500000000) := by
  have h := checkLog_sound (w := (37 / 219)) (n := 12)
    (lo := (341170757 / 1000000000)) (hi := (170585379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 91) = 1/(91 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170585379 / 500000000) (-341170757 / 1000000000) (Real.log (91 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253460561 / 1000000000) ≤ -Real.log (5120 / 6597) ∧
    -Real.log (5120 / 6597) ≤ (126730281 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 11717)) (n := 12)
    (lo := (253460561 / 1000000000)) (hi := (126730281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6597 / 5120) = 1/(5120 / 6597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253460561 / 1000000000) (126730281 / 500000000) (Real.log (6597 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6597 / 5120) = -Real.log (5120 / 6597) := by
    rw [show ((6597 / 5120) : ℝ) = ((5120 / 6597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (340346921 / 1000000000) ≤ -Real.log (3643 / 5120) ∧
    -Real.log (3643 / 5120) ≤ (170173461 / 500000000) := by
  have h := checkLog_sound (w := (1477 / 8763)) (n := 12)
    (lo := (340346921 / 1000000000)) (hi := (170173461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3643) = 1/(3643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170173461 / 500000000) (-340346921 / 1000000000) (Real.log (3643 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (456237433 / 1000000000) ≤ -Real.log (64 / 101) ∧
    -Real.log (64 / 101) ≤ (228118717 / 500000000) := by
  have h := checkLog_sound (w := (37 / 165)) (n := 12)
    (lo := (456237433 / 1000000000)) (hi := (228118717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101 / 64) = 1/(64 / 101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (456237433 / 1000000000) (228118717 / 500000000) (Real.log (101 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (101 / 64) = -Real.log (64 / 101) := by
    rw [show ((101 / 64) : ℝ) = ((64 / 101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (107880777 / 125000000) ≤ -Real.log (27 / 64) ∧
    -Real.log (27 / 64) ≤ (431523109 / 500000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 27) = 1/(27 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-431523109 / 500000000) (-107880777 / 125000000) (Real.log (27 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (455494583 / 1000000000) ≤ -Real.log (2560 / 4037) ∧
    -Real.log (2560 / 4037) ≤ (56936823 / 125000000) := by
  have h := checkLog_sound (w := (1477 / 6597)) (n := 12)
    (lo := (455494583 / 1000000000)) (hi := (56936823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4037 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4037 / 2560) = 1/(2560 / 4037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (455494583 / 1000000000) (56936823 / 125000000) (Real.log (4037 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4037 / 2560) = -Real.log (2560 / 4037) := by
    rw [show ((4037 / 2560) : ℝ) = ((2560 / 4037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (860272289 / 1000000000) ≤ -Real.log (1083 / 2560) ∧
    -Real.log (1083 / 2560) ≤ (860272291 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2363)) (n := 12)
    (lo := (167125109 / 1000000000)) (hi := (16712511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1083) = 1/(1083 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-860272291 / 1000000000) (-860272289 / 1000000000) (Real.log (1083 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (86709227 / 250000000) ≤ -Real.log (500000 / 707293) ∧
    -Real.log (500000 / 707293) ≤ (346836909 / 1000000000) := by
  have h := checkLog_sound (w := (207293 / 1207293)) (n := 12)
    (lo := (86709227 / 250000000)) (hi := (346836909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707293 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707293 / 500000) = 1/(500000 / 707293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (86709227 / 250000000) (346836909 / 1000000000) (Real.log (707293 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (707293 / 500000) = -Real.log (500000 / 707293) := by
    rw [show ((707293 / 500000) : ℝ) = ((500000 / 707293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (535435989 / 1000000000) ≤ -Real.log (292707 / 500000) ∧
    -Real.log (292707 / 500000) ≤ (53543599 / 100000000) := by
  have h := checkLog_sound (w := (207293 / 792707)) (n := 12)
    (lo := (535435989 / 1000000000)) (hi := (53543599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292707) = 1/(292707 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-53543599 / 100000000) (-535435989 / 1000000000) (Real.log (292707 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (347455273 / 1000000000) ≤ -Real.log (1000000 / 1415461) ∧
    -Real.log (1000000 / 1415461) ≤ (173727637 / 500000000) := by
  have h := checkLog_sound (w := (415461 / 2415461)) (n := 12)
    (lo := (347455273 / 1000000000)) (hi := (173727637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415461 / 1000000) = 1/(1000000 / 1415461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (347455273 / 1000000000) (173727637 / 500000000) (Real.log (1415461 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1415461 / 1000000) = -Real.log (1000000 / 1415461) := by
    rw [show ((1415461 / 1000000) : ℝ) = ((1000000 / 1415461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8389559 / 15625000) ≤ -Real.log (584539 / 1000000) ∧
    -Real.log (584539 / 1000000) ≤ (536931777 / 1000000000) := by
  have h := checkLog_sound (w := (415461 / 1584539)) (n := 12)
    (lo := (8389559 / 15625000)) (hi := (536931777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 584539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 584539) = 1/(584539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-536931777 / 1000000000) (-8389559 / 15625000) (Real.log (584539 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (268328749 / 1000000000) ≤ -Real.log (1000000 / 1307777) ∧
    -Real.log (1000000 / 1307777) ≤ (214663 / 800000) := by
  have h := checkLog_sound (w := (307777 / 2307777)) (n := 12)
    (lo := (268328749 / 1000000000)) (hi := (214663 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307777 / 1000000) = 1/(1000000 / 1307777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (268328749 / 1000000000) (214663 / 800000) (Real.log (1307777 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1307777 / 1000000) = -Real.log (1000000 / 1307777) := by
    rw [show ((1307777 / 1000000) : ℝ) = ((1000000 / 1307777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4598089 / 12500000) ≤ -Real.log (692223 / 1000000) ∧
    -Real.log (692223 / 1000000) ≤ (367847121 / 1000000000) := by
  have h := checkLog_sound (w := (307777 / 1692223)) (n := 12)
    (lo := (4598089 / 12500000)) (hi := (367847121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 692223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 692223) = 1/(692223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-367847121 / 1000000000) (-4598089 / 12500000) (Real.log (692223 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67218641 / 250000000) ≤ -Real.log (1000000 / 1308491) ∧
    -Real.log (1000000 / 1308491) ≤ (53774913 / 200000000) := by
  have h := checkLog_sound (w := (308491 / 2308491)) (n := 12)
    (lo := (67218641 / 250000000)) (hi := (53774913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1308491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1308491 / 1000000) = 1/(1000000 / 1308491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67218641 / 250000000) (53774913 / 200000000) (Real.log (1308491 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1308491 / 1000000) = -Real.log (1000000 / 1308491) := by
    rw [show ((1308491 / 1000000) : ℝ) = ((1000000 / 1308491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (46109889 / 125000000) ≤ -Real.log (691509 / 1000000) ∧
    -Real.log (691509 / 1000000) ≤ (368879113 / 1000000000) := by
  have h := checkLog_sound (w := (308491 / 1691509)) (n := 12)
    (lo := (46109889 / 125000000)) (hi := (368879113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 691509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 691509) = 1/(691509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-368879113 / 1000000000) (-46109889 / 125000000) (Real.log (691509 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (882272897 / 1000000000) ≤ -Real.log (62500000000 / 151024104309) ∧
    -Real.log (62500000000 / 151024104309) ≤ (882272899 / 1000000000) := by
  have h := checkLog_sound (w := (26024104309 / 276024104309)) (n := 12)
    (lo := (189125717 / 1000000000)) (hi := (94562859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151024104309 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(151024104309 / 125000000000) = 1/(62500000000 / 151024104309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (882272897 / 1000000000) (882272899 / 1000000000) (Real.log (151024104309 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (151024104309 / 62500000000) = -Real.log (62500000000 / 151024104309) := by
    rw [show ((151024104309 / 62500000000) : ℝ) = ((62500000000 / 151024104309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (884387049 / 1000000000) ≤ -Real.log (250000000000 / 605374919381) ∧
    -Real.log (250000000000 / 605374919381) ≤ (884387051 / 1000000000) := by
  have h := checkLog_sound (w := (105374919381 / 1105374919381)) (n := 12)
    (lo := (191239869 / 1000000000)) (hi := (19123987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605374919381 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(605374919381 / 500000000000) = 1/(250000000000 / 605374919381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (884387049 / 1000000000) (884387051 / 1000000000) (Real.log (605374919381 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (605374919381 / 250000000000) = -Real.log (250000000000 / 605374919381) := by
    rw [show ((605374919381 / 250000000000) : ℝ) = ((250000000000 / 605374919381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (63617587 / 100000000) ≤ -Real.log (500000000000 / 944621169767) ∧
    -Real.log (500000000000 / 944621169767) ≤ (636175871 / 1000000000) := by
  have h := checkLog_sound (w := (444621169767 / 1444621169767)) (n := 12)
    (lo := (63617587 / 100000000)) (hi := (636175871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((944621169767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(944621169767 / 500000000000) = 1/(500000000000 / 944621169767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (63617587 / 100000000) (636175871 / 1000000000) (Real.log (944621169767 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (944621169767 / 500000000000) = -Real.log (500000000000 / 944621169767) := by
    rw [show ((944621169767 / 500000000000) : ℝ) = ((500000000000 / 944621169767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (637753677 / 1000000000) ≤ -Real.log (500000000000 / 946112776551) ∧
    -Real.log (500000000000 / 946112776551) ≤ (318876839 / 500000000) := by
  have h := checkLog_sound (w := (446112776551 / 1446112776551)) (n := 12)
    (lo := (637753677 / 1000000000)) (hi := (318876839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((946112776551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(946112776551 / 500000000000) = 1/(500000000000 / 946112776551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (637753677 / 1000000000) (318876839 / 500000000) (Real.log (946112776551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (946112776551 / 500000000000) = -Real.log (500000000000 / 946112776551) := by
    rw [show ((946112776551 / 500000000000) : ℝ) = ((500000000000 / 946112776551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0226
