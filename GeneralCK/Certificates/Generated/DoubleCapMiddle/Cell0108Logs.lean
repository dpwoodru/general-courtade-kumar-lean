import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0108
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

theorem reflection_log_1_neg : (65331723 / 200000000) ≤ -Real.log (2560 / 3549) ∧
    -Real.log (2560 / 3549) ≤ (40832327 / 125000000) := by
  have h := checkLog_sound (w := (989 / 6109)) (n := 12)
    (lo := (65331723 / 200000000)) (hi := (40832327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3549 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3549 / 2560) = 1/(2560 / 3549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65331723 / 200000000) (40832327 / 125000000) (Real.log (3549 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3549 / 2560) = -Real.log (2560 / 3549) := by
    rw [show ((3549 / 2560) : ℝ) = ((2560 / 3549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (488294899 / 1000000000) ≤ -Real.log (1571 / 2560) ∧
    -Real.log (1571 / 2560) ≤ (4882949 / 10000000) := by
  have h := checkLog_sound (w := (989 / 4131)) (n := 12)
    (lo := (488294899 / 1000000000)) (hi := (4882949 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1571) = 1/(1571 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4882949 / 10000000) (-488294899 / 1000000000) (Real.log (1571 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325812949 / 1000000000) ≤ -Real.log (1280 / 1773) ∧
    -Real.log (1280 / 1773) ≤ (6516259 / 20000000) := by
  have h := checkLog_sound (w := (493 / 3053)) (n := 12)
    (lo := (325812949 / 1000000000)) (hi := (6516259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1280) = 1/(1280 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325812949 / 1000000000) (6516259 / 20000000) (Real.log (1773 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1773 / 1280) = -Real.log (1280 / 1773) := by
    rw [show ((1773 / 1280) : ℝ) = ((1280 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121596777 / 250000000) ≤ -Real.log (787 / 1280) ∧
    -Real.log (787 / 1280) ≤ (486387109 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2067)) (n := 12)
    (lo := (121596777 / 250000000)) (hi := (486387109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 787) = 1/(787 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-486387109 / 1000000000) (-121596777 / 250000000) (Real.log (787 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (572479127 / 1000000000) ≤ -Real.log (1280 / 2269) ∧
    -Real.log (1280 / 2269) ≤ (71559891 / 125000000) := by
  have h := checkLog_sound (w := (989 / 3549)) (n := 12)
    (lo := (572479127 / 1000000000)) (hi := (71559891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2269 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2269 / 1280) = 1/(1280 / 2269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (572479127 / 1000000000) (71559891 / 125000000) (Real.log (2269 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2269 / 1280) = -Real.log (1280 / 2269) := by
    rw [show ((2269 / 1280) : ℝ) = ((1280 / 2269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (185161511 / 125000000) ≤ -Real.log (291 / 1280) ∧
    -Real.log (291 / 1280) ≤ (1481292091 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 291) = 1/(291 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1481292091 / 1000000000) (-185161511 / 125000000) (Real.log (291 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (142789021 / 250000000) ≤ -Real.log (640 / 1133) ∧
    -Real.log (640 / 1133) ≤ (114231217 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1773)) (n := 12)
    (lo := (142789021 / 250000000)) (hi := (114231217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133 / 640) = 1/(640 / 1133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (142789021 / 250000000) (114231217 / 200000000) (Real.log (1133 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1133 / 640) = -Real.log (640 / 1133) := by
    rw [show ((1133 / 640) : ℝ) = ((640 / 1133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (367758897 / 250000000) ≤ -Real.log (147 / 640) ∧
    -Real.log (147 / 640) ≤ (1471035591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 147) = 1/(147 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1471035591 / 1000000000) (-367758897 / 250000000) (Real.log (147 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (446774663 / 1000000000) ≤ -Real.log (500000 / 781631) ∧
    -Real.log (500000 / 781631) ≤ (55846833 / 125000000) := by
  have h := checkLog_sound (w := (281631 / 1281631)) (n := 12)
    (lo := (446774663 / 1000000000)) (hi := (55846833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781631 / 500000) = 1/(500000 / 781631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (446774663 / 1000000000) (55846833 / 125000000) (Real.log (781631 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (781631 / 500000) = -Real.log (500000 / 781631) := by
    rw [show ((781631 / 500000) : ℝ) = ((500000 / 781631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (165684361 / 200000000) ≤ -Real.log (218369 / 500000) ∧
    -Real.log (218369 / 500000) ≤ (828421807 / 1000000000) := by
  have h := checkLog_sound (w := (31631 / 468369)) (n := 12)
    (lo := (1082197 / 8000000)) (hi := (67637313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 218369) = 1/(218369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-828421807 / 1000000000) (-165684361 / 200000000) (Real.log (218369 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89595183 / 200000000) ≤ -Real.log (1000000 / 1565141) ∧
    -Real.log (1000000 / 1565141) ≤ (111993979 / 250000000) := by
  have h := checkLog_sound (w := (565141 / 2565141)) (n := 12)
    (lo := (89595183 / 200000000)) (hi := (111993979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1565141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1565141 / 1000000) = 1/(1000000 / 1565141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89595183 / 200000000) (111993979 / 250000000) (Real.log (1565141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1565141 / 1000000) = -Real.log (1000000 / 1565141) := by
    rw [show ((1565141 / 1000000) : ℝ) = ((1000000 / 1565141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (832733437 / 1000000000) ≤ -Real.log (434859 / 1000000) ∧
    -Real.log (434859 / 1000000) ≤ (832733439 / 1000000000) := by
  have h := checkLog_sound (w := (65141 / 934859)) (n := 12)
    (lo := (139586257 / 1000000000)) (hi := (69793129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434859) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 434859) = 1/(434859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-832733439 / 1000000000) (-832733437 / 1000000000) (Real.log (434859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (362133021 / 1000000000) ≤ -Real.log (100000 / 143639) ∧
    -Real.log (100000 / 143639) ≤ (181066511 / 500000000) := by
  have h := checkLog_sound (w := (43639 / 243639)) (n := 12)
    (lo := (362133021 / 1000000000)) (hi := (181066511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143639 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143639 / 100000) = 1/(100000 / 143639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (362133021 / 1000000000) (181066511 / 500000000) (Real.log (143639 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (143639 / 100000) = -Real.log (100000 / 143639) := by
    rw [show ((143639 / 100000) : ℝ) = ((100000 / 143639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (143348189 / 250000000) ≤ -Real.log (56361 / 100000) ∧
    -Real.log (56361 / 100000) ≤ (573392757 / 1000000000) := by
  have h := checkLog_sound (w := (43639 / 156361)) (n := 12)
    (lo := (143348189 / 250000000)) (hi := (573392757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56361) = 1/(56361 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-573392757 / 1000000000) (-143348189 / 250000000) (Real.log (56361 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (363338791 / 1000000000) ≤ -Real.log (1000000 / 1438123) ∧
    -Real.log (1000000 / 1438123) ≤ (45417349 / 125000000) := by
  have h := checkLog_sound (w := (438123 / 2438123)) (n := 12)
    (lo := (363338791 / 1000000000)) (hi := (45417349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1438123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1438123 / 1000000) = 1/(1000000 / 1438123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (363338791 / 1000000000) (45417349 / 125000000) (Real.log (1438123 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1438123 / 1000000) = -Real.log (1000000 / 1438123) := by
    rw [show ((1438123 / 1000000) : ℝ) = ((1000000 / 1438123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (288236157 / 500000000) ≤ -Real.log (561877 / 1000000) ∧
    -Real.log (561877 / 1000000) ≤ (115294463 / 200000000) := by
  have h := checkLog_sound (w := (438123 / 1561877)) (n := 12)
    (lo := (288236157 / 500000000)) (hi := (115294463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 561877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 561877) = 1/(561877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115294463 / 200000000) (-288236157 / 500000000) (Real.log (561877 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1275196469 / 1000000000) ≤ -Real.log (500000000000 / 1789702292907) ∧
    -Real.log (500000000000 / 1789702292907) ≤ (1275196471 / 1000000000) := by
  have h := checkLog_sound (w := (789702292907 / 2789702292907)) (n := 12)
    (lo := (582049289 / 1000000000)) (hi := (58204929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789702292907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1789702292907 / 1000000000000) = 1/(500000000000 / 1789702292907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1275196469 / 1000000000) (1275196471 / 1000000000) (Real.log (1789702292907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1789702292907 / 500000000000) = -Real.log (500000000000 / 1789702292907) := by
    rw [show ((1789702292907 / 500000000000) : ℝ) = ((500000000000 / 1789702292907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1280709353 / 1000000000) ≤ -Real.log (50000000000 / 179959596099) ∧
    -Real.log (50000000000 / 179959596099) ≤ (256141871 / 200000000) := by
  have h := checkLog_sound (w := (79959596099 / 279959596099)) (n := 12)
    (lo := (587562173 / 1000000000)) (hi := (293781087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179959596099 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(179959596099 / 100000000000) = 1/(50000000000 / 179959596099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1280709353 / 1000000000) (256141871 / 200000000) (Real.log (179959596099 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179959596099 / 50000000000) = -Real.log (50000000000 / 179959596099) := by
    rw [show ((179959596099 / 50000000000) : ℝ) = ((50000000000 / 179959596099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (58470361 / 62500000) ≤ -Real.log (500000000000 / 1274276538741) ∧
    -Real.log (500000000000 / 1274276538741) ≤ (467762889 / 500000000) := by
  have h := checkLog_sound (w := (274276538741 / 2274276538741)) (n := 12)
    (lo := (60594649 / 250000000)) (hi := (242378597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274276538741 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274276538741 / 1000000000000) = 1/(500000000000 / 1274276538741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (58470361 / 62500000) (467762889 / 500000000) (Real.log (1274276538741 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1274276538741 / 500000000000) = -Real.log (500000000000 / 1274276538741) := by
    rw [show ((1274276538741 / 500000000000) : ℝ) = ((500000000000 / 1274276538741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29369097 / 31250000) ≤ -Real.log (250000000000 / 639874474307) ∧
    -Real.log (250000000000 / 639874474307) ≤ (469905553 / 500000000) := by
  have h := checkLog_sound (w := (139874474307 / 1139874474307)) (n := 12)
    (lo := (61665981 / 250000000)) (hi := (9866557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639874474307 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(639874474307 / 500000000000) = 1/(250000000000 / 639874474307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29369097 / 31250000) (469905553 / 500000000) (Real.log (639874474307 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (639874474307 / 250000000000) = -Real.log (250000000000 / 639874474307) := by
    rw [show ((639874474307 / 250000000000) : ℝ) = ((250000000000 / 639874474307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0108
