import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0161
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

theorem reflection_log_1_neg : (8844769 / 31250000) ≤ -Real.log (1024 / 1359) ∧
    -Real.log (1024 / 1359) ≤ (283032609 / 1000000000) := by
  have h := checkLog_sound (w := (335 / 2383)) (n := 12)
    (lo := (8844769 / 31250000)) (hi := (283032609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1024) = 1/(1024 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8844769 / 31250000) (283032609 / 1000000000) (Real.log (1359 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1359 / 1024) = -Real.log (1024 / 1359) := by
    rw [show ((1359 / 1024) : ℝ) = ((1024 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (198115267 / 500000000) ≤ -Real.log (689 / 1024) ∧
    -Real.log (689 / 1024) ≤ (79246107 / 200000000) := by
  have h := checkLog_sound (w := (335 / 1713)) (n := 12)
    (lo := (198115267 / 500000000)) (hi := (79246107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 689) = 1/(689 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-79246107 / 200000000) (-198115267 / 500000000) (Real.log (689 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (282591009 / 1000000000) ≤ -Real.log (640 / 849) ∧
    -Real.log (640 / 849) ≤ (28259101 / 100000000) := by
  have h := checkLog_sound (w := (209 / 1489)) (n := 12)
    (lo := (282591009 / 1000000000)) (hi := (28259101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 640) = 1/(640 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (282591009 / 1000000000) (28259101 / 100000000) (Real.log (849 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (849 / 640) = -Real.log (640 / 849) := by
    rw [show ((849 / 640) : ℝ) = ((640 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197680043 / 500000000) ≤ -Real.log (431 / 640) ∧
    -Real.log (431 / 640) ≤ (395360087 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1071)) (n := 12)
    (lo := (197680043 / 500000000)) (hi := (395360087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 431) = 1/(431 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-395360087 / 1000000000) (-197680043 / 500000000) (Real.log (431 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (503376069 / 1000000000) ≤ -Real.log (512 / 847) ∧
    -Real.log (512 / 847) ≤ (50337607 / 100000000) := by
  have h := checkLog_sound (w := (335 / 1359)) (n := 12)
    (lo := (503376069 / 1000000000)) (hi := (50337607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847 / 512) = 1/(512 / 847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (503376069 / 1000000000) (50337607 / 100000000) (Real.log (847 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (847 / 512) = -Real.log (512 / 847) := by
    rw [show ((847 / 512) : ℝ) = ((512 / 847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1062174891 / 1000000000) ≤ -Real.log (177 / 512) ∧
    -Real.log (177 / 512) ≤ (1062174893 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 433)) (n := 12)
    (lo := (369027711 / 1000000000)) (hi := (2883029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 177) = 1/(177 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1062174893 / 1000000000) (-1062174891 / 1000000000) (Real.log (177 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125666859 / 250000000) ≤ -Real.log (320 / 529) ∧
    -Real.log (320 / 529) ≤ (502667437 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 849)) (n := 12)
    (lo := (125666859 / 250000000)) (hi := (502667437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(529 / 320) = 1/(320 / 529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125666859 / 250000000) (502667437 / 1000000000) (Real.log (529 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (529 / 320) = -Real.log (320 / 529) := by
    rw [show ((529 / 320) : ℝ) = ((320 / 529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1058790793 / 1000000000) ≤ -Real.log (111 / 320) ∧
    -Real.log (111 / 320) ≤ (211758159 / 200000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 111) = 1/(111 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-211758159 / 200000000) (-1058790793 / 1000000000) (Real.log (111 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (386592807 / 1000000000) ≤ -Real.log (1000000 / 1471957) ∧
    -Real.log (1000000 / 1471957) ≤ (48324101 / 125000000) := by
  have h := checkLog_sound (w := (471957 / 2471957)) (n := 12)
    (lo := (386592807 / 1000000000)) (hi := (48324101 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1471957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1471957 / 1000000) = 1/(1000000 / 1471957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (386592807 / 1000000000) (48324101 / 125000000) (Real.log (1471957 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1471957 / 1000000) = -Real.log (1000000 / 1471957) := by
    rw [show ((1471957 / 1000000) : ℝ) = ((1000000 / 1471957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (638577559 / 1000000000) ≤ -Real.log (528043 / 1000000) ∧
    -Real.log (528043 / 1000000) ≤ (15964439 / 25000000) := by
  have h := checkLog_sound (w := (471957 / 1528043)) (n := 12)
    (lo := (638577559 / 1000000000)) (hi := (15964439 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 528043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 528043) = 1/(528043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15964439 / 25000000) (-638577559 / 1000000000) (Real.log (528043 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (193599989 / 500000000) ≤ -Real.log (1000000 / 1472851) ∧
    -Real.log (1000000 / 1472851) ≤ (387199979 / 1000000000) := by
  have h := checkLog_sound (w := (472851 / 2472851)) (n := 12)
    (lo := (193599989 / 500000000)) (hi := (387199979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1472851 / 1000000) = 1/(1000000 / 1472851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (193599989 / 500000000) (387199979 / 1000000000) (Real.log (1472851 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1472851 / 1000000) = -Real.log (1000000 / 1472851) := by
    rw [show ((1472851 / 1000000) : ℝ) = ((1000000 / 1472851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (640272037 / 1000000000) ≤ -Real.log (527149 / 1000000) ∧
    -Real.log (527149 / 1000000) ≤ (320136019 / 500000000) := by
  have h := checkLog_sound (w := (472851 / 1527149)) (n := 12)
    (lo := (640272037 / 1000000000)) (hi := (320136019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 527149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 527149) = 1/(527149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-320136019 / 500000000) (-640272037 / 1000000000) (Real.log (527149 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (60846619 / 200000000) ≤ -Real.log (200000 / 271117) ∧
    -Real.log (200000 / 271117) ≤ (38029137 / 125000000) := by
  have h := checkLog_sound (w := (71117 / 471117)) (n := 12)
    (lo := (60846619 / 200000000)) (hi := (38029137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271117 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271117 / 200000) = 1/(200000 / 271117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (60846619 / 200000000) (38029137 / 125000000) (Real.log (271117 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (271117 / 200000) = -Real.log (200000 / 271117) := by
    rw [show ((271117 / 200000) : ℝ) = ((200000 / 271117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (8788247 / 20000000) ≤ -Real.log (128883 / 200000) ∧
    -Real.log (128883 / 200000) ≤ (439412351 / 1000000000) := by
  have h := checkLog_sound (w := (71117 / 328883)) (n := 12)
    (lo := (8788247 / 20000000)) (hi := (439412351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 128883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 128883) = 1/(128883 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-439412351 / 1000000000) (-8788247 / 20000000) (Real.log (128883 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19049691 / 62500000) ≤ -Real.log (1000000 / 1356347) ∧
    -Real.log (1000000 / 1356347) ≤ (304795057 / 1000000000) := by
  have h := checkLog_sound (w := (356347 / 2356347)) (n := 12)
    (lo := (19049691 / 62500000)) (hi := (304795057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356347 / 1000000) = 1/(1000000 / 1356347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19049691 / 62500000) (304795057 / 1000000000) (Real.log (1356347 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1356347 / 1000000) = -Real.log (1000000 / 1356347) := by
    rw [show ((1356347 / 1000000) : ℝ) = ((1000000 / 1356347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (440595517 / 1000000000) ≤ -Real.log (643653 / 1000000) ∧
    -Real.log (643653 / 1000000) ≤ (220297759 / 500000000) := by
  have h := checkLog_sound (w := (356347 / 1643653)) (n := 12)
    (lo := (440595517 / 1000000000)) (hi := (220297759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643653) = 1/(643653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-220297759 / 500000000) (-440595517 / 1000000000) (Real.log (643653 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (512585183 / 500000000) ≤ -Real.log (500000000000 / 1393785165223) ∧
    -Real.log (500000000000 / 1393785165223) ≤ (16018287 / 15625000) := by
  have h := checkLog_sound (w := (393785165223 / 2393785165223)) (n := 12)
    (lo := (166011593 / 500000000)) (hi := (332023187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393785165223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393785165223 / 1000000000000) = 1/(500000000000 / 1393785165223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (512585183 / 500000000) (16018287 / 15625000) (Real.log (1393785165223 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1393785165223 / 500000000000) = -Real.log (500000000000 / 1393785165223) := by
    rw [show ((1393785165223 / 500000000000) : ℝ) = ((500000000000 / 1393785165223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (205494403 / 200000000) ≤ -Real.log (100000000000 / 279399372853) ∧
    -Real.log (100000000000 / 279399372853) ≤ (1027472017 / 1000000000) := by
  have h := checkLog_sound (w := (79399372853 / 479399372853)) (n := 12)
    (lo := (66864967 / 200000000)) (hi := (83581209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279399372853 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279399372853 / 200000000000) = 1/(100000000000 / 279399372853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (205494403 / 200000000) (1027472017 / 1000000000) (Real.log (279399372853 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279399372853 / 100000000000) = -Real.log (100000000000 / 279399372853) := by
    rw [show ((279399372853 / 100000000000) : ℝ) = ((100000000000 / 279399372853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (148729089 / 200000000) ≤ -Real.log (500000000000 / 1051795038911) ∧
    -Real.log (500000000000 / 1051795038911) ≤ (743645447 / 1000000000) := by
  have h := checkLog_sound (w := (51795038911 / 2051795038911)) (n := 12)
    (lo := (10099653 / 200000000)) (hi := (25249133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051795038911 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1051795038911 / 1000000000000) = 1/(500000000000 / 1051795038911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (148729089 / 200000000) (743645447 / 1000000000) (Real.log (1051795038911 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1051795038911 / 500000000000) = -Real.log (500000000000 / 1051795038911) := by
    rw [show ((1051795038911 / 500000000000) : ℝ) = ((500000000000 / 1051795038911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (745390573 / 1000000000) ≤ -Real.log (500000000000 / 1053632158943) ∧
    -Real.log (500000000000 / 1053632158943) ≤ (29815623 / 40000000) := by
  have h := checkLog_sound (w := (53632158943 / 2053632158943)) (n := 12)
    (lo := (52243393 / 1000000000)) (hi := (26121697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053632158943 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1053632158943 / 1000000000000) = 1/(500000000000 / 1053632158943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (745390573 / 1000000000) (29815623 / 40000000) (Real.log (1053632158943 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1053632158943 / 500000000000) = -Real.log (500000000000 / 1053632158943) := by
    rw [show ((1053632158943 / 500000000000) : ℝ) = ((500000000000 / 1053632158943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0161
