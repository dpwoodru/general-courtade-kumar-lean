import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0159
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

theorem reflection_log_1_neg : (283915221 / 1000000000) ≤ -Real.log (5120 / 6801) ∧
    -Real.log (5120 / 6801) ≤ (141957611 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 11921)) (n := 12)
    (lo := (283915221 / 1000000000)) (hi := (141957611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6801 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6801 / 5120) = 1/(5120 / 6801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (283915221 / 1000000000) (141957611 / 500000000) (Real.log (6801 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6801 / 5120) = -Real.log (5120 / 6801) := by
    rw [show ((6801 / 5120) : ℝ) = ((5120 / 6801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (397973707 / 1000000000) ≤ -Real.log (3439 / 5120) ∧
    -Real.log (3439 / 5120) ≤ (99493427 / 250000000) := by
  have h := checkLog_sound (w := (1681 / 8559)) (n := 12)
    (lo := (397973707 / 1000000000)) (hi := (99493427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3439) = 1/(3439 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-99493427 / 250000000) (-397973707 / 1000000000) (Real.log (3439 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (70868503 / 250000000) ≤ -Real.log (2560 / 3399) ∧
    -Real.log (2560 / 3399) ≤ (283474013 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 5959)) (n := 12)
    (lo := (70868503 / 250000000)) (hi := (283474013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3399 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3399 / 2560) = 1/(2560 / 3399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (70868503 / 250000000) (283474013 / 1000000000) (Real.log (3399 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3399 / 2560) = -Real.log (2560 / 3399) := by
    rw [show ((3399 / 2560) : ℝ) = ((2560 / 3399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (397101741 / 1000000000) ≤ -Real.log (1721 / 2560) ∧
    -Real.log (1721 / 2560) ≤ (198550871 / 500000000) := by
  have h := checkLog_sound (w := (839 / 4281)) (n := 12)
    (lo := (397101741 / 1000000000)) (hi := (198550871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1721) = 1/(1721 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-198550871 / 500000000) (-397101741 / 1000000000) (Real.log (1721 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (63098979 / 125000000) ≤ -Real.log (2560 / 4241) ∧
    -Real.log (2560 / 4241) ≤ (504791833 / 1000000000) := by
  have h := checkLog_sound (w := (1681 / 6801)) (n := 12)
    (lo := (63098979 / 125000000)) (hi := (504791833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4241 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4241 / 2560) = 1/(2560 / 4241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (63098979 / 125000000) (504791833 / 1000000000) (Real.log (4241 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4241 / 2560) = -Real.log (2560 / 4241) := by
    rw [show ((4241 / 2560) : ℝ) = ((2560 / 4241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1068977639 / 1000000000) ≤ -Real.log (879 / 2560) ∧
    -Real.log (879 / 2560) ≤ (1068977641 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 879) = 1/(879 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1068977641 / 1000000000) (-1068977639 / 1000000000) (Real.log (879 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (504084201 / 1000000000) ≤ -Real.log (1280 / 2119) ∧
    -Real.log (1280 / 2119) ≤ (252042101 / 500000000) := by
  have h := checkLog_sound (w := (839 / 3399)) (n := 12)
    (lo := (504084201 / 1000000000)) (hi := (252042101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2119 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2119 / 1280) = 1/(1280 / 2119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (504084201 / 1000000000) (252042101 / 500000000) (Real.log (2119 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2119 / 1280) = -Real.log (1280 / 2119) := by
    rw [show ((2119 / 1280) : ℝ) = ((1280 / 2119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (13319631 / 12500000) ≤ -Real.log (441 / 1280) ∧
    -Real.log (441 / 1280) ≤ (532785241 / 500000000) := by
  have h := checkLog_sound (w := (199 / 1081)) (n := 12)
    (lo := (3724233 / 10000000)) (hi := (372423301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 441) = 1/(441 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-532785241 / 500000000) (-13319631 / 12500000) (Real.log (441 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (387805423 / 1000000000) ≤ -Real.log (1000000 / 1473743) ∧
    -Real.log (1000000 / 1473743) ≤ (24237839 / 62500000) := by
  have h := checkLog_sound (w := (473743 / 2473743)) (n := 12)
    (lo := (387805423 / 1000000000)) (hi := (24237839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473743 / 1000000) = 1/(1000000 / 1473743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (387805423 / 1000000000) (24237839 / 62500000) (Real.log (1473743 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1473743 / 1000000) = -Real.log (1000000 / 1473743) := by
    rw [show ((1473743 / 1000000) : ℝ) = ((1000000 / 1473743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (80245699 / 125000000) ≤ -Real.log (526257 / 1000000) ∧
    -Real.log (526257 / 1000000) ≤ (641965593 / 1000000000) := by
  have h := checkLog_sound (w := (473743 / 1526257)) (n := 12)
    (lo := (80245699 / 125000000)) (hi := (641965593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 526257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 526257) = 1/(526257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-641965593 / 1000000000) (-80245699 / 125000000) (Real.log (526257 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (388411857 / 1000000000) ≤ -Real.log (1000000 / 1474637) ∧
    -Real.log (1000000 / 1474637) ≤ (194205929 / 500000000) := by
  have h := checkLog_sound (w := (474637 / 2474637)) (n := 12)
    (lo := (388411857 / 1000000000)) (hi := (194205929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1474637 / 1000000) = 1/(1000000 / 1474637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (388411857 / 1000000000) (194205929 / 500000000) (Real.log (1474637 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1474637 / 1000000) = -Real.log (1000000 / 1474637) := by
    rw [show ((1474637 / 1000000) : ℝ) = ((1000000 / 1474637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (321832913 / 500000000) ≤ -Real.log (525363 / 1000000) ∧
    -Real.log (525363 / 1000000) ≤ (643665827 / 1000000000) := by
  have h := checkLog_sound (w := (474637 / 1525363)) (n := 12)
    (lo := (321832913 / 500000000)) (hi := (643665827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 525363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 525363) = 1/(525363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-643665827 / 1000000000) (-321832913 / 500000000) (Real.log (525363 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (76338807 / 250000000) ≤ -Real.log (1000000 / 1357107) ∧
    -Real.log (1000000 / 1357107) ≤ (305355229 / 1000000000) := by
  have h := checkLog_sound (w := (357107 / 2357107)) (n := 12)
    (lo := (76338807 / 250000000)) (hi := (305355229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357107 / 1000000) = 1/(1000000 / 1357107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (76338807 / 250000000) (305355229 / 1000000000) (Real.log (1357107 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1357107 / 1000000) = -Real.log (1000000 / 1357107) := by
    rw [show ((1357107 / 1000000) : ℝ) = ((1000000 / 1357107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27611061 / 62500000) ≤ -Real.log (642893 / 1000000) ∧
    -Real.log (642893 / 1000000) ≤ (441776977 / 1000000000) := by
  have h := checkLog_sound (w := (357107 / 1642893)) (n := 12)
    (lo := (27611061 / 62500000)) (hi := (441776977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642893) = 1/(642893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-441776977 / 1000000000) (-27611061 / 62500000) (Real.log (642893 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61183459 / 200000000) ≤ -Real.log (100000 / 135787) ∧
    -Real.log (100000 / 135787) ≤ (19119831 / 62500000) := by
  have h := checkLog_sound (w := (35787 / 235787)) (n := 12)
    (lo := (61183459 / 200000000)) (hi := (19119831 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135787 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135787 / 100000) = 1/(100000 / 135787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61183459 / 200000000) (19119831 / 62500000) (Real.log (135787 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (135787 / 100000) = -Real.log (100000 / 135787) := by
    rw [show ((135787 / 100000) : ℝ) = ((100000 / 135787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (442964503 / 1000000000) ≤ -Real.log (64213 / 100000) ∧
    -Real.log (64213 / 100000) ≤ (55370563 / 125000000) := by
  have h := checkLog_sound (w := (35787 / 164213)) (n := 12)
    (lo := (442964503 / 1000000000)) (hi := (55370563 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64213) = 1/(64213 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-55370563 / 125000000) (-442964503 / 1000000000) (Real.log (64213 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (514885507 / 500000000) ≤ -Real.log (125000000000 / 350053063427) ∧
    -Real.log (125000000000 / 350053063427) ≤ (128721377 / 125000000) := by
  have h := checkLog_sound (w := (100053063427 / 600053063427)) (n := 12)
    (lo := (168311917 / 500000000)) (hi := (67324767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350053063427 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(350053063427 / 250000000000) = 1/(125000000000 / 350053063427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (514885507 / 500000000) (128721377 / 125000000) (Real.log (350053063427 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (350053063427 / 125000000000) = -Real.log (125000000000 / 350053063427) := by
    rw [show ((350053063427 / 125000000000) : ℝ) = ((125000000000 / 350053063427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1032077683 / 1000000000) ≤ -Real.log (500000000000 / 1403445807947) ∧
    -Real.log (500000000000 / 1403445807947) ≤ (206415537 / 200000000) := by
  have h := checkLog_sound (w := (403445807947 / 2403445807947)) (n := 12)
    (lo := (338930503 / 1000000000)) (hi := (42366313 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403445807947 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1403445807947 / 1000000000000) = 1/(500000000000 / 1403445807947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1032077683 / 1000000000) (206415537 / 200000000) (Real.log (1403445807947 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1403445807947 / 500000000000) = -Real.log (500000000000 / 1403445807947) := by
    rw [show ((1403445807947 / 500000000000) : ℝ) = ((500000000000 / 1403445807947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (747132203 / 1000000000) ≤ -Real.log (250000000000 / 527734397481) ∧
    -Real.log (250000000000 / 527734397481) ≤ (149426441 / 200000000) := by
  have h := checkLog_sound (w := (27734397481 / 1027734397481)) (n := 12)
    (lo := (53985023 / 1000000000)) (hi := (210879 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((527734397481 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(527734397481 / 500000000000) = 1/(250000000000 / 527734397481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (747132203 / 1000000000) (149426441 / 200000000) (Real.log (527734397481 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (527734397481 / 250000000000) = -Real.log (250000000000 / 527734397481) := by
    rw [show ((527734397481 / 250000000000) : ℝ) = ((250000000000 / 527734397481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (374440899 / 500000000) ≤ -Real.log (25000000000 / 52865852709) ∧
    -Real.log (25000000000 / 52865852709) ≤ (3744409 / 5000000) := by
  have h := checkLog_sound (w := (2865852709 / 102865852709)) (n := 12)
    (lo := (27867309 / 500000000)) (hi := (55734619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52865852709 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(52865852709 / 50000000000) = 1/(25000000000 / 52865852709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (374440899 / 500000000) (3744409 / 5000000) (Real.log (52865852709 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (52865852709 / 25000000000) = -Real.log (25000000000 / 52865852709) := by
    rw [show ((52865852709 / 25000000000) : ℝ) = ((25000000000 / 52865852709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0159
