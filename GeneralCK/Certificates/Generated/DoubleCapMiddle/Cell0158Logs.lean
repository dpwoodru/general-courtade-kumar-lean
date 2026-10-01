import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0158
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

theorem reflection_log_1_neg : (56871247 / 200000000) ≤ -Real.log (1280 / 1701) ∧
    -Real.log (1280 / 1701) ≤ (71089059 / 250000000) := by
  have h := checkLog_sound (w := (421 / 2981)) (n := 12)
    (lo := (56871247 / 200000000)) (hi := (71089059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1280) = 1/(1280 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56871247 / 200000000) (71089059 / 250000000) (Real.log (1701 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1701 / 1280) = -Real.log (1280 / 1701) := by
    rw [show ((1701 / 1280) : ℝ) = ((1280 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (199423217 / 500000000) ≤ -Real.log (859 / 1280) ∧
    -Real.log (859 / 1280) ≤ (79769287 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2139)) (n := 12)
    (lo := (199423217 / 500000000)) (hi := (79769287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 859) = 1/(859 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-79769287 / 200000000) (-199423217 / 500000000) (Real.log (859 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (283915221 / 1000000000) ≤ -Real.log (5120 / 6801) ∧
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


theorem reflection_log_3 : Bounds (283915221 / 1000000000) (141957611 / 500000000) (Real.log (6801 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6801 / 5120) = -Real.log (5120 / 6801) := by
    rw [show ((6801 / 5120) : ℝ) = ((5120 / 6801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (397973707 / 1000000000) ≤ -Real.log (3439 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-99493427 / 250000000) (-397973707 / 1000000000) (Real.log (3439 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (252749481 / 500000000) ≤ -Real.log (640 / 1061) ∧
    -Real.log (640 / 1061) ≤ (505498963 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1701)) (n := 12)
    (lo := (252749481 / 500000000)) (hi := (505498963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1061 / 640) = 1/(640 / 1061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (252749481 / 500000000) (505498963 / 1000000000) (Real.log (1061 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1061 / 640) = -Real.log (640 / 1061) := by
    rw [show ((1061 / 640) : ℝ) = ((640 / 1061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214479289 / 200000000) ≤ -Real.log (219 / 640) ∧
    -Real.log (219 / 640) ≤ (1072396447 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 219) = 1/(219 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1072396447 / 1000000000) (-214479289 / 200000000) (Real.log (219 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (63098979 / 125000000) ≤ -Real.log (2560 / 4241) ∧
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


theorem reflection_log_7 : Bounds (63098979 / 125000000) (504791833 / 1000000000) (Real.log (4241 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4241 / 2560) = -Real.log (2560 / 4241) := by
    rw [show ((4241 / 2560) : ℝ) = ((2560 / 4241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1068977639 / 1000000000) ≤ -Real.log (879 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-1068977641 / 1000000000) (-1068977639 / 1000000000) (Real.log (879 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (388411179 / 1000000000) ≤ -Real.log (250000 / 368659) ∧
    -Real.log (250000 / 368659) ≤ (19420559 / 50000000) := by
  have h := checkLog_sound (w := (118659 / 618659)) (n := 12)
    (lo := (388411179 / 1000000000)) (hi := (19420559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368659 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368659 / 250000) = 1/(250000 / 368659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (388411179 / 1000000000) (19420559 / 50000000) (Real.log (368659 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (368659 / 250000) = -Real.log (250000 / 368659) := by
    rw [show ((368659 / 250000) : ℝ) = ((250000 / 368659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (643663923 / 1000000000) ≤ -Real.log (131341 / 250000) ∧
    -Real.log (131341 / 250000) ≤ (160915981 / 250000000) := by
  have h := checkLog_sound (w := (118659 / 381341)) (n := 12)
    (lo := (643663923 / 1000000000)) (hi := (160915981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 131341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 131341) = 1/(131341 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-160915981 / 250000000) (-643663923 / 1000000000) (Real.log (131341 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (389017247 / 1000000000) ≤ -Real.log (100000 / 147553) ∧
    -Real.log (100000 / 147553) ≤ (12156789 / 31250000) := by
  have h := checkLog_sound (w := (47553 / 247553)) (n := 12)
    (lo := (389017247 / 1000000000)) (hi := (12156789 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147553 / 100000) = 1/(100000 / 147553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (389017247 / 1000000000) (12156789 / 31250000) (Real.log (147553 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (147553 / 100000) = -Real.log (100000 / 147553) := by
    rw [show ((147553 / 100000) : ℝ) = ((100000 / 147553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (12907341 / 20000000) ≤ -Real.log (52447 / 100000) ∧
    -Real.log (52447 / 100000) ≤ (645367051 / 1000000000) := by
  have h := checkLog_sound (w := (47553 / 152447)) (n := 12)
    (lo := (12907341 / 20000000)) (hi := (645367051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 52447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 52447) = 1/(52447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-645367051 / 1000000000) (-12907341 / 20000000) (Real.log (52447 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305916559 / 1000000000) ≤ -Real.log (1000000 / 1357869) ∧
    -Real.log (1000000 / 1357869) ≤ (3823957 / 12500000) := by
  have h := checkLog_sound (w := (357869 / 2357869)) (n := 12)
    (lo := (305916559 / 1000000000)) (hi := (3823957 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357869 / 1000000) = 1/(1000000 / 1357869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305916559 / 1000000000) (3823957 / 12500000) (Real.log (1357869 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1357869 / 1000000) = -Real.log (1000000 / 1357869) := by
    rw [show ((1357869 / 1000000) : ℝ) = ((1000000 / 1357869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (221481473 / 500000000) ≤ -Real.log (642131 / 1000000) ∧
    -Real.log (642131 / 1000000) ≤ (442962947 / 1000000000) := by
  have h := checkLog_sound (w := (357869 / 1642131)) (n := 12)
    (lo := (221481473 / 500000000)) (hi := (442962947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642131) = 1/(642131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-442962947 / 1000000000) (-221481473 / 500000000) (Real.log (642131 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (306479047 / 1000000000) ≤ -Real.log (1000000 / 1358633) ∧
    -Real.log (1000000 / 1358633) ≤ (38309881 / 125000000) := by
  have h := checkLog_sound (w := (358633 / 2358633)) (n := 12)
    (lo := (306479047 / 1000000000)) (hi := (38309881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358633 / 1000000) = 1/(1000000 / 1358633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (306479047 / 1000000000) (38309881 / 125000000) (Real.log (1358633 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1358633 / 1000000) = -Real.log (1000000 / 1358633) := by
    rw [show ((1358633 / 1000000) : ℝ) = ((1000000 / 1358633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (222076721 / 500000000) ≤ -Real.log (641367 / 1000000) ∧
    -Real.log (641367 / 1000000) ≤ (444153443 / 1000000000) := by
  have h := checkLog_sound (w := (358633 / 1641367)) (n := 12)
    (lo := (222076721 / 500000000)) (hi := (444153443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641367) = 1/(641367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-444153443 / 1000000000) (-222076721 / 500000000) (Real.log (641367 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (516037551 / 500000000) ≤ -Real.log (500000000000 / 1403442184847) ∧
    -Real.log (500000000000 / 1403442184847) ≤ (32252347 / 31250000) := by
  have h := checkLog_sound (w := (403442184847 / 2403442184847)) (n := 12)
    (lo := (169463961 / 500000000)) (hi := (338927923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403442184847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1403442184847 / 1000000000000) = 1/(500000000000 / 1403442184847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (516037551 / 500000000) (32252347 / 31250000) (Real.log (1403442184847 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1403442184847 / 500000000000) = -Real.log (500000000000 / 1403442184847) := by
    rw [show ((1403442184847 / 500000000000) : ℝ) = ((500000000000 / 1403442184847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (129298037 / 125000000) ≤ -Real.log (250000000000 / 703343375217) ∧
    -Real.log (250000000000 / 703343375217) ≤ (517192149 / 500000000) := by
  have h := checkLog_sound (w := (203343375217 / 1203343375217)) (n := 12)
    (lo := (85309279 / 250000000)) (hi := (341237117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703343375217 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(703343375217 / 500000000000) = 1/(250000000000 / 703343375217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (129298037 / 125000000) (517192149 / 500000000) (Real.log (703343375217 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (703343375217 / 250000000000) = -Real.log (250000000000 / 703343375217) := by
    rw [show ((703343375217 / 250000000000) : ℝ) = ((250000000000 / 703343375217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (46804969 / 62500000) ≤ -Real.log (250000000000 / 528657314473) ∧
    -Real.log (250000000000 / 528657314473) ≤ (374439753 / 500000000) := by
  have h := checkLog_sound (w := (28657314473 / 1028657314473)) (n := 12)
    (lo := (13933081 / 250000000)) (hi := (2229293 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528657314473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528657314473 / 500000000000) = 1/(250000000000 / 528657314473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (46804969 / 62500000) (374439753 / 500000000) (Real.log (528657314473 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (528657314473 / 250000000000) = -Real.log (250000000000 / 528657314473) := by
    rw [show ((528657314473 / 250000000000) : ℝ) = ((250000000000 / 528657314473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (750632489 / 1000000000) ≤ -Real.log (250000000000 / 529584855473) ∧
    -Real.log (250000000000 / 529584855473) ≤ (750632491 / 1000000000) := by
  have h := checkLog_sound (w := (29584855473 / 1029584855473)) (n := 12)
    (lo := (57485309 / 1000000000)) (hi := (5748531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529584855473 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529584855473 / 500000000000) = 1/(250000000000 / 529584855473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (750632489 / 1000000000) (750632491 / 1000000000) (Real.log (529584855473 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (529584855473 / 250000000000) = -Real.log (250000000000 / 529584855473) := by
    rw [show ((529584855473 / 250000000000) : ℝ) = ((250000000000 / 529584855473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0158
