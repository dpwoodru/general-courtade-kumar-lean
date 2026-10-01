import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12416_neg : (490879 / 1000000000) ≤ -Real.log (1000000 / 1000491) ∧
    -Real.log (1000000 / 1000491) ≤ (767 / 1562500) := by
  have h := checkLog_sound (w := (491 / 2000491)) (n := 12)
    (lo := (490879 / 1000000000)) (hi := (767 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000491 / 1000000) = 1/(1000000 / 1000491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12416 : Bounds (490879 / 1000000000) (767 / 1562500) (Real.log (1000491 / 1000000)) := by
  have h := reflection_log_12416_neg
  have he : Real.log (1000491 / 1000000) = -Real.log (1000000 / 1000491) := by
    rw [show ((1000491 / 1000000) : ℝ) = ((1000000 / 1000491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12417_neg : (6139 / 12500000) ≤ -Real.log (999509 / 1000000) ∧
    -Real.log (999509 / 1000000) ≤ (491121 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1999509)) (n := 12)
    (lo := (6139 / 12500000)) (hi := (491121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999509) = 1/(999509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12417 : Bounds (-491121 / 1000000000) (-6139 / 12500000) (Real.log (999509 / 1000000)) := by
  have h := reflection_log_12417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12418_neg : (228097659 / 1000000000) ≤ -Real.log (62500 / 78513) ∧
    -Real.log (62500 / 78513) ≤ (11404883 / 50000000) := by
  have h := checkLog_sound (w := (16013 / 141013)) (n := 12)
    (lo := (228097659 / 1000000000)) (hi := (11404883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78513 / 62500) = 1/(62500 / 78513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12418 : Bounds (228097659 / 1000000000) (11404883 / 50000000) (Real.log (78513 / 62500)) := by
  have h := reflection_log_12418_neg
  have he : Real.log (78513 / 62500) = -Real.log (62500 / 78513) := by
    rw [show ((78513 / 62500) : ℝ) = ((62500 / 78513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12419_neg : (295993853 / 1000000000) ≤ -Real.log (46487 / 62500) ∧
    -Real.log (46487 / 62500) ≤ (147996927 / 500000000) := by
  have h := checkLog_sound (w := (16013 / 108987)) (n := 12)
    (lo := (295993853 / 1000000000)) (hi := (147996927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46487) = 1/(46487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12419 : Bounds (-147996927 / 500000000) (-295993853 / 1000000000) (Real.log (46487 / 62500)) := by
  have h := reflection_log_12419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12420_neg : (114463 / 500000) ≤ -Real.log (1000000 / 1257249) ∧
    -Real.log (1000000 / 1257249) ≤ (228926001 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 2257249)) (n := 12)
    (lo := (114463 / 500000)) (hi := (228926001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257249 / 1000000) = 1/(1000000 / 1257249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12420 : Bounds (114463 / 500000) (228926001 / 1000000000) (Real.log (1257249 / 1000000)) := by
  have h := reflection_log_12420_neg
  have he : Real.log (1257249 / 1000000) = -Real.log (1000000 / 1257249) := by
    rw [show ((1257249 / 1000000) : ℝ) = ((1000000 / 1257249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12421_neg : (148697209 / 500000000) ≤ -Real.log (742751 / 1000000) ∧
    -Real.log (742751 / 1000000) ≤ (297394419 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 1742751)) (n := 12)
    (lo := (148697209 / 500000000)) (hi := (297394419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742751) = 1/(742751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12421 : Bounds (-297394419 / 1000000000) (-148697209 / 500000000) (Real.log (742751 / 1000000)) := by
  have h := reflection_log_12421_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12422_neg : (68468417 / 1000000000) ≤ -Real.log (933822951999 / 1000000000000) ∧
    -Real.log (933822951999 / 1000000000000) ≤ (34234209 / 500000000) := by
  have h := checkLog_sound (w := (66177048001 / 1933822951999)) (n := 12)
    (lo := (68468417 / 1000000000)) (hi := (34234209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 933822951999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 933822951999) = 1/(933822951999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12422 : Bounds (-34234209 / 500000000) (-68468417 / 1000000000) (Real.log (933822951999 / 1000000000000)) := by
  have h := reflection_log_12422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12423_neg : (67896193 / 1000000000) ≤ -Real.log (3649833831 / 3906250000) ∧
    -Real.log (3649833831 / 3906250000) ≤ (33948097 / 500000000) := by
  have h := checkLog_sound (w := (256416169 / 7556083831)) (n := 12)
    (lo := (67896193 / 1000000000)) (hi := (33948097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3649833831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3649833831) = 1/(3649833831 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12423 : Bounds (-33948097 / 500000000) (-67896193 / 1000000000) (Real.log (3649833831 / 3906250000)) := by
  have h := reflection_log_12423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12424_neg : (65511439 / 125000000) ≤ -Real.log (125000000000 / 211115473143) ∧
    -Real.log (125000000000 / 211115473143) ≤ (524091513 / 1000000000) := by
  have h := checkLog_sound (w := (86115473143 / 336115473143)) (n := 12)
    (lo := (65511439 / 125000000)) (hi := (524091513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211115473143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211115473143 / 125000000000) = 1/(125000000000 / 211115473143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12424 : Bounds (65511439 / 125000000) (524091513 / 1000000000) (Real.log (211115473143 / 125000000000)) := by
  have h := reflection_log_12424_neg
  have he : Real.log (211115473143 / 125000000000) = -Real.log (125000000000 / 211115473143) := by
    rw [show ((211115473143 / 125000000000) : ℝ) = ((125000000000 / 211115473143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12425_neg : (263160209 / 500000000) ≤ -Real.log (125000000000 / 211586554579) ∧
    -Real.log (125000000000 / 211586554579) ≤ (526320419 / 1000000000) := by
  have h := checkLog_sound (w := (86586554579 / 336586554579)) (n := 12)
    (lo := (263160209 / 500000000)) (hi := (526320419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211586554579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211586554579 / 125000000000) = 1/(125000000000 / 211586554579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12425 : Bounds (263160209 / 500000000) (526320419 / 1000000000) (Real.log (211586554579 / 125000000000)) := by
  have h := reflection_log_12425_neg
  have he : Real.log (211586554579 / 125000000000) = -Real.log (125000000000 / 211586554579) := by
    rw [show ((211586554579 / 125000000000) : ℝ) = ((125000000000 / 211586554579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12426_neg : (33503771 / 31250000) ≤ -Real.log (20000000000 / 58431372549) ∧
    -Real.log (20000000000 / 58431372549) ≤ (536060337 / 500000000) := by
  have h := checkLog_sound (w := (18431372549 / 98431372549)) (n := 12)
    (lo := (94743373 / 250000000)) (hi := (378973493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58431372549 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58431372549 / 40000000000) = 1/(20000000000 / 58431372549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12426 : Bounds (33503771 / 31250000) (536060337 / 500000000) (Real.log (58431372549 / 20000000000)) := by
  have h := reflection_log_12426_neg
  have he : Real.log (58431372549 / 20000000000) = -Real.log (20000000000 / 58431372549) := by
    rw [show ((58431372549 / 20000000000) : ℝ) = ((20000000000 / 58431372549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12427_neg : (1074754297 / 1000000000) ≤ -Real.log (3125000000 / 9153978389) ∧
    -Real.log (3125000000 / 9153978389) ≤ (1074754299 / 1000000000) := by
  have h := checkLog_sound (w := (2903978389 / 15403978389)) (n := 12)
    (lo := (381607117 / 1000000000)) (hi := (190803559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9153978389 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9153978389 / 6250000000) = 1/(3125000000 / 9153978389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12427 : Bounds (1074754297 / 1000000000) (1074754299 / 1000000000) (Real.log (9153978389 / 3125000000)) := by
  have h := reflection_log_12427_neg
  have he : Real.log (9153978389 / 3125000000) = -Real.log (3125000000 / 9153978389) := by
    rw [show ((9153978389 / 3125000000) : ℝ) = ((3125000000 / 9153978389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12428_neg : (400117501 / 1000000000) ≤ -Real.log (250 / 373) ∧
    -Real.log (250 / 373) ≤ (200058751 / 500000000) := by
  have h := checkLog_sound (w := (123 / 623)) (n := 12)
    (lo := (400117501 / 1000000000)) (hi := (200058751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373 / 250) = 1/(250 / 373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12428 : Bounds (400117501 / 1000000000) (200058751 / 500000000) (Real.log (373 / 250)) := by
  have h := reflection_log_12428_neg
  have he : Real.log (373 / 250) = -Real.log (250 / 373) := by
    rw [show ((373 / 250) : ℝ) = ((250 / 373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12429_neg : (677273831 / 1000000000) ≤ -Real.log (127 / 250) ∧
    -Real.log (127 / 250) ≤ (84659229 / 125000000) := by
  have h := checkLog_sound (w := (123 / 377)) (n := 12)
    (lo := (677273831 / 1000000000)) (hi := (84659229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 127) = 1/(127 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12429 : Bounds (-84659229 / 125000000) (-677273831 / 1000000000) (Real.log (127 / 250)) := by
  have h := reflection_log_12429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12430_neg : (491879 / 1000000000) ≤ -Real.log (250000 / 250123) ∧
    -Real.log (250000 / 250123) ≤ (12297 / 25000000) := by
  have h := checkLog_sound (w := (123 / 500123)) (n := 12)
    (lo := (491879 / 1000000000)) (hi := (12297 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250123 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250123 / 250000) = 1/(250000 / 250123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12430 : Bounds (491879 / 1000000000) (12297 / 25000000) (Real.log (250123 / 250000)) := by
  have h := reflection_log_12430_neg
  have he : Real.log (250123 / 250000) = -Real.log (250000 / 250123) := by
    rw [show ((250123 / 250000) : ℝ) = ((250000 / 250123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12431_neg : (492121 / 1000000000) ≤ -Real.log (249877 / 250000) ∧
    -Real.log (249877 / 250000) ≤ (246061 / 500000000) := by
  have h := checkLog_sound (w := (123 / 499877)) (n := 12)
    (lo := (492121 / 1000000000)) (hi := (246061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249877) = 1/(249877 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12431 : Bounds (-246061 / 500000000) (-492121 / 1000000000) (Real.log (249877 / 250000)) := by
  have h := reflection_log_12431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12432_neg : (45710897 / 200000000) ≤ -Real.log (500000 / 628391) ∧
    -Real.log (500000 / 628391) ≤ (114277243 / 500000000) := by
  have h := checkLog_sound (w := (128391 / 1128391)) (n := 12)
    (lo := (45710897 / 200000000)) (hi := (114277243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628391 / 500000) = 1/(500000 / 628391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12432 : Bounds (45710897 / 200000000) (114277243 / 500000000) (Real.log (628391 / 500000)) := by
  have h := reflection_log_12432_neg
  have he : Real.log (628391 / 500000) = -Real.log (500000 / 628391) := by
    rw [show ((628391 / 500000) : ℝ) = ((500000 / 628391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12433_neg : (18547867 / 62500000) ≤ -Real.log (371609 / 500000) ∧
    -Real.log (371609 / 500000) ≤ (296765873 / 1000000000) := by
  have h := checkLog_sound (w := (128391 / 871609)) (n := 12)
    (lo := (18547867 / 62500000)) (hi := (296765873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371609) = 1/(371609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12433 : Bounds (-296765873 / 1000000000) (-18547867 / 62500000) (Real.log (371609 / 500000)) := by
  have h := reflection_log_12433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12434_neg : (229383243 / 1000000000) ≤ -Real.log (31250 / 39307) ∧
    -Real.log (31250 / 39307) ≤ (57345811 / 250000000) := by
  have h := checkLog_sound (w := (8057 / 70557)) (n := 12)
    (lo := (229383243 / 1000000000)) (hi := (57345811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39307 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39307 / 31250) = 1/(31250 / 39307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12434 : Bounds (229383243 / 1000000000) (57345811 / 250000000) (Real.log (39307 / 31250)) := by
  have h := reflection_log_12434_neg
  have he : Real.log (39307 / 31250) = -Real.log (31250 / 39307) := by
    rw [show ((39307 / 31250) : ℝ) = ((31250 / 39307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12435_neg : (298168867 / 1000000000) ≤ -Real.log (23193 / 31250) ∧
    -Real.log (23193 / 31250) ≤ (74542217 / 250000000) := by
  have h := checkLog_sound (w := (8057 / 54443)) (n := 12)
    (lo := (298168867 / 1000000000)) (hi := (74542217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23193) = 1/(23193 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12435 : Bounds (-74542217 / 250000000) (-298168867 / 1000000000) (Real.log (23193 / 31250)) := by
  have h := reflection_log_12435_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12436_neg : (68785623 / 1000000000) ≤ -Real.log (911647251 / 976562500) ∧
    -Real.log (911647251 / 976562500) ≤ (8598203 / 125000000) := by
  have h := checkLog_sound (w := (64915249 / 1888209751)) (n := 12)
    (lo := (68785623 / 1000000000)) (hi := (8598203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 911647251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 911647251) = 1/(911647251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12436 : Bounds (-8598203 / 125000000) (-68785623 / 1000000000) (Real.log (911647251 / 976562500)) := by
  have h := reflection_log_12436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12437_neg : (34105693 / 500000000) ≤ -Real.log (233515751119 / 250000000000) ∧
    -Real.log (233515751119 / 250000000000) ≤ (68211387 / 1000000000) := by
  have h := checkLog_sound (w := (16484248881 / 483515751119)) (n := 12)
    (lo := (34105693 / 500000000)) (hi := (68211387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233515751119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233515751119) = 1/(233515751119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12437 : Bounds (-68211387 / 1000000000) (-34105693 / 500000000) (Real.log (233515751119 / 250000000000)) := by
  have h := reflection_log_12437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12438_neg : (525320357 / 1000000000) ≤ -Real.log (100000000000 / 169100048707) ∧
    -Real.log (100000000000 / 169100048707) ≤ (262660179 / 500000000) := by
  have h := checkLog_sound (w := (69100048707 / 269100048707)) (n := 12)
    (lo := (525320357 / 1000000000)) (hi := (262660179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169100048707 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169100048707 / 100000000000) = 1/(100000000000 / 169100048707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12438 : Bounds (525320357 / 1000000000) (262660179 / 500000000) (Real.log (169100048707 / 100000000000)) := by
  have h := reflection_log_12438_neg
  have he : Real.log (169100048707 / 100000000000) = -Real.log (100000000000 / 169100048707) := by
    rw [show ((169100048707 / 100000000000) : ℝ) = ((100000000000 / 169100048707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12439_neg : (527552111 / 1000000000) ≤ -Real.log (7812500000 / 13240457789) ∧
    -Real.log (7812500000 / 13240457789) ≤ (32972007 / 62500000) := by
  have h := checkLog_sound (w := (5427957789 / 21052957789)) (n := 12)
    (lo := (527552111 / 1000000000)) (hi := (32972007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13240457789 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13240457789 / 7812500000) = 1/(7812500000 / 13240457789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12439 : Bounds (527552111 / 1000000000) (32972007 / 62500000) (Real.log (13240457789 / 7812500000)) := by
  have h := reflection_log_12439_neg
  have he : Real.log (13240457789 / 7812500000) = -Real.log (7812500000 / 13240457789) := by
    rw [show ((13240457789 / 7812500000) : ℝ) = ((7812500000 / 13240457789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12440_neg : (1074754297 / 1000000000) ≤ -Real.log (500000000000 / 1464636542239) ∧
    -Real.log (500000000000 / 1464636542239) ≤ (1074754299 / 1000000000) := by
  have h := checkLog_sound (w := (464636542239 / 2464636542239)) (n := 12)
    (lo := (381607117 / 1000000000)) (hi := (190803559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1464636542239 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1464636542239 / 1000000000000) = 1/(500000000000 / 1464636542239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12440 : Bounds (1074754297 / 1000000000) (1074754299 / 1000000000) (Real.log (1464636542239 / 500000000000)) := by
  have h := reflection_log_12440_neg
  have he : Real.log (1464636542239 / 500000000000) = -Real.log (500000000000 / 1464636542239) := by
    rw [show ((1464636542239 / 500000000000) : ℝ) = ((500000000000 / 1464636542239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12441_neg : (269347833 / 250000000) ≤ -Real.log (31250000000 / 91781496063) ∧
    -Real.log (31250000000 / 91781496063) ≤ (538695667 / 500000000) := by
  have h := checkLog_sound (w := (29281496063 / 154281496063)) (n := 12)
    (lo := (48030519 / 125000000)) (hi := (384244153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91781496063 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(91781496063 / 62500000000) = 1/(31250000000 / 91781496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12441 : Bounds (269347833 / 250000000) (538695667 / 500000000) (Real.log (91781496063 / 31250000000)) := by
  have h := reflection_log_12441_neg
  have he : Real.log (91781496063 / 31250000000) = -Real.log (31250000000 / 91781496063) := by
    rw [show ((91781496063 / 31250000000) : ℝ) = ((31250000000 / 91781496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12442_neg : (200393759 / 500000000) ≤ -Real.log (1000 / 1493) ∧
    -Real.log (1000 / 1493) ≤ (400787519 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2493)) (n := 12)
    (lo := (200393759 / 500000000)) (hi := (400787519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1000) = 1/(1000 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12442 : Bounds (200393759 / 500000000) (400787519 / 1000000000) (Real.log (1493 / 1000)) := by
  have h := reflection_log_12442_neg
  have he : Real.log (1493 / 1000) = -Real.log (1000 / 1493) := by
    rw [show ((1493 / 1000) : ℝ) = ((1000 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12443_neg : (27169771 / 40000000) ≤ -Real.log (507 / 1000) ∧
    -Real.log (507 / 1000) ≤ (169811069 / 250000000) := by
  have h := checkLog_sound (w := (493 / 1507)) (n := 12)
    (lo := (27169771 / 40000000)) (hi := (169811069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 507) = 1/(507 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12443 : Bounds (-169811069 / 250000000) (-27169771 / 40000000) (Real.log (507 / 1000)) := by
  have h := reflection_log_12443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12444_neg : (246439 / 500000000) ≤ -Real.log (1000000 / 1000493) ∧
    -Real.log (1000000 / 1000493) ≤ (492879 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2000493)) (n := 12)
    (lo := (246439 / 500000000)) (hi := (492879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000493 / 1000000) = 1/(1000000 / 1000493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12444 : Bounds (246439 / 500000000) (492879 / 1000000000) (Real.log (1000493 / 1000000)) := by
  have h := reflection_log_12444_neg
  have he : Real.log (1000493 / 1000000) = -Real.log (1000000 / 1000493) := by
    rw [show ((1000493 / 1000000) : ℝ) = ((1000000 / 1000493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12445_neg : (493121 / 1000000000) ≤ -Real.log (999507 / 1000000) ∧
    -Real.log (999507 / 1000000) ≤ (246561 / 500000000) := by
  have h := checkLog_sound (w := (493 / 1999507)) (n := 12)
    (lo := (493121 / 1000000000)) (hi := (246561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999507) = 1/(999507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12445 : Bounds (-246561 / 500000000) (-493121 / 1000000000) (Real.log (999507 / 1000000)) := by
  have h := reflection_log_12445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12446_neg : (229011103 / 1000000000) ≤ -Real.log (250000 / 314339) ∧
    -Real.log (250000 / 314339) ≤ (7156597 / 31250000) := by
  have h := checkLog_sound (w := (64339 / 564339)) (n := 12)
    (lo := (229011103 / 1000000000)) (hi := (7156597 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314339 / 250000) = 1/(250000 / 314339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12446 : Bounds (229011103 / 1000000000) (7156597 / 31250000) (Real.log (314339 / 250000)) := by
  have h := reflection_log_12446_neg
  have he : Real.log (314339 / 250000) = -Real.log (250000 / 314339) := by
    rw [show ((314339 / 250000) : ℝ) = ((250000 / 314339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12447_neg : (297538487 / 1000000000) ≤ -Real.log (185661 / 250000) ∧
    -Real.log (185661 / 250000) ≤ (37192311 / 125000000) := by
  have h := checkLog_sound (w := (64339 / 435661)) (n := 12)
    (lo := (297538487 / 1000000000)) (hi := (37192311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185661) = 1/(185661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12447 : Bounds (-37192311 / 125000000) (-297538487 / 1000000000) (Real.log (185661 / 250000)) := by
  have h := reflection_log_12447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12448_neg : (114920139 / 500000000) ≤ -Real.log (1000000 / 1258399) ∧
    -Real.log (1000000 / 1258399) ≤ (229840279 / 1000000000) := by
  have h := checkLog_sound (w := (258399 / 2258399)) (n := 12)
    (lo := (114920139 / 500000000)) (hi := (229840279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1258399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1258399 / 1000000) = 1/(1000000 / 1258399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12448 : Bounds (114920139 / 500000000) (229840279 / 1000000000) (Real.log (1258399 / 1000000)) := by
  have h := reflection_log_12448_neg
  have he : Real.log (1258399 / 1000000) = -Real.log (1000000 / 1258399) := by
    rw [show ((1258399 / 1000000) : ℝ) = ((1000000 / 1258399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12449_neg : (74735979 / 250000000) ≤ -Real.log (741601 / 1000000) ∧
    -Real.log (741601 / 1000000) ≤ (298943917 / 1000000000) := by
  have h := checkLog_sound (w := (258399 / 1741601)) (n := 12)
    (lo := (74735979 / 250000000)) (hi := (298943917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 741601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 741601) = 1/(741601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12449 : Bounds (-298943917 / 1000000000) (-74735979 / 250000000) (Real.log (741601 / 1000000)) := by
  have h := reflection_log_12449_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12450_neg : (34551819 / 500000000) ≤ -Real.log (933229956799 / 1000000000000) ∧
    -Real.log (933229956799 / 1000000000000) ≤ (69103639 / 1000000000) := by
  have h := checkLog_sound (w := (66770043201 / 1933229956799)) (n := 12)
    (lo := (34551819 / 500000000)) (hi := (69103639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 933229956799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 933229956799) = 1/(933229956799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12450 : Bounds (-69103639 / 1000000000) (-34551819 / 500000000) (Real.log (933229956799 / 1000000000000)) := by
  have h := reflection_log_12450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12451_neg : (8565923 / 125000000) ≤ -Real.log (58360493079 / 62500000000) ∧
    -Real.log (58360493079 / 62500000000) ≤ (13705477 / 200000000) := by
  have h := checkLog_sound (w := (4139506921 / 120860493079)) (n := 12)
    (lo := (8565923 / 125000000)) (hi := (13705477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58360493079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58360493079) = 1/(58360493079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12451 : Bounds (-13705477 / 200000000) (-8565923 / 125000000) (Real.log (58360493079 / 62500000000)) := by
  have h := reflection_log_12451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12452_neg : (526549591 / 1000000000) ≤ -Real.log (500000000000 / 846540199611) ∧
    -Real.log (500000000000 / 846540199611) ≤ (65818699 / 125000000) := by
  have h := checkLog_sound (w := (346540199611 / 1346540199611)) (n := 12)
    (lo := (526549591 / 1000000000)) (hi := (65818699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846540199611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846540199611 / 500000000000) = 1/(500000000000 / 846540199611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12452 : Bounds (526549591 / 1000000000) (65818699 / 125000000) (Real.log (846540199611 / 500000000000)) := by
  have h := reflection_log_12452_neg
  have he : Real.log (846540199611 / 500000000000) = -Real.log (500000000000 / 846540199611) := by
    rw [show ((846540199611 / 500000000000) : ℝ) = ((500000000000 / 846540199611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12453_neg : (264392097 / 500000000) ≤ -Real.log (500000000000 / 848433996179) ∧
    -Real.log (500000000000 / 848433996179) ≤ (105756839 / 200000000) := by
  have h := checkLog_sound (w := (348433996179 / 1348433996179)) (n := 12)
    (lo := (264392097 / 500000000)) (hi := (105756839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848433996179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848433996179 / 500000000000) = 1/(500000000000 / 848433996179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12453 : Bounds (264392097 / 500000000) (105756839 / 200000000) (Real.log (848433996179 / 500000000000)) := by
  have h := reflection_log_12453_neg
  have he : Real.log (848433996179 / 500000000000) = -Real.log (500000000000 / 848433996179) := by
    rw [show ((848433996179 / 500000000000) : ℝ) = ((500000000000 / 848433996179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12454_neg : (269347833 / 250000000) ≤ -Real.log (500000000000 / 1468503937007) ∧
    -Real.log (500000000000 / 1468503937007) ≤ (538695667 / 500000000) := by
  have h := checkLog_sound (w := (468503937007 / 2468503937007)) (n := 12)
    (lo := (48030519 / 125000000)) (hi := (384244153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1468503937007 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1468503937007 / 1000000000000) = 1/(500000000000 / 1468503937007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12454 : Bounds (269347833 / 250000000) (538695667 / 500000000) (Real.log (1468503937007 / 500000000000)) := by
  have h := reflection_log_12454_neg
  have he : Real.log (1468503937007 / 500000000000) = -Real.log (500000000000 / 1468503937007) := by
    rw [show ((1468503937007 / 500000000000) : ℝ) = ((500000000000 / 1468503937007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12455_neg : (1080031793 / 1000000000) ≤ -Real.log (125000000000 / 368096646943) ∧
    -Real.log (125000000000 / 368096646943) ≤ (216006359 / 200000000) := by
  have h := checkLog_sound (w := (118096646943 / 618096646943)) (n := 12)
    (lo := (386884613 / 1000000000)) (hi := (193442307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368096646943 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(368096646943 / 250000000000) = 1/(125000000000 / 368096646943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12455 : Bounds (1080031793 / 1000000000) (216006359 / 200000000) (Real.log (368096646943 / 125000000000)) := by
  have h := reflection_log_12455_neg
  have he : Real.log (368096646943 / 125000000000) = -Real.log (125000000000 / 368096646943) := by
    rw [show ((368096646943 / 125000000000) : ℝ) = ((125000000000 / 368096646943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12456_neg : (200728543 / 500000000) ≤ -Real.log (500 / 747) ∧
    -Real.log (500 / 747) ≤ (401457087 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1247)) (n := 12)
    (lo := (200728543 / 500000000)) (hi := (401457087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 500) = 1/(500 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12456 : Bounds (200728543 / 500000000) (401457087 / 1000000000) (Real.log (747 / 500)) := by
  have h := reflection_log_12456_neg
  have he : Real.log (747 / 500) = -Real.log (500 / 747) := by
    rw [show ((747 / 500) : ℝ) = ((500 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12457_neg : (681218609 / 1000000000) ≤ -Real.log (253 / 500) ∧
    -Real.log (253 / 500) ≤ (68121861 / 100000000) := by
  have h := checkLog_sound (w := (247 / 753)) (n := 12)
    (lo := (681218609 / 1000000000)) (hi := (68121861 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 253) = 1/(253 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12457 : Bounds (-68121861 / 100000000) (-681218609 / 1000000000) (Real.log (253 / 500)) := by
  have h := reflection_log_12457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12458_neg : (246939 / 500000000) ≤ -Real.log (500000 / 500247) ∧
    -Real.log (500000 / 500247) ≤ (493879 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1000247)) (n := 12)
    (lo := (246939 / 500000000)) (hi := (493879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500247 / 500000) = 1/(500000 / 500247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12458 : Bounds (246939 / 500000000) (493879 / 1000000000) (Real.log (500247 / 500000)) := by
  have h := reflection_log_12458_neg
  have he : Real.log (500247 / 500000) = -Real.log (500000 / 500247) := by
    rw [show ((500247 / 500000) : ℝ) = ((500000 / 500247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12459_neg : (247061 / 500000000) ≤ -Real.log (499753 / 500000) ∧
    -Real.log (499753 / 500000) ≤ (494123 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 999753)) (n := 12)
    (lo := (247061 / 500000000)) (hi := (494123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499753) = 1/(499753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12459 : Bounds (-494123 / 1000000000) (-247061 / 500000000) (Real.log (499753 / 500000)) := by
  have h := reflection_log_12459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12460_neg : (28683439 / 125000000) ≤ -Real.log (100000 / 125793) ∧
    -Real.log (100000 / 125793) ≤ (229467513 / 1000000000) := by
  have h := checkLog_sound (w := (25793 / 225793)) (n := 12)
    (lo := (28683439 / 125000000)) (hi := (229467513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125793 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125793 / 100000) = 1/(100000 / 125793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12460 : Bounds (28683439 / 125000000) (229467513 / 1000000000) (Real.log (125793 / 100000)) := by
  have h := reflection_log_12460_neg
  have he : Real.log (125793 / 100000) = -Real.log (100000 / 125793) := by
    rw [show ((125793 / 100000) : ℝ) = ((100000 / 125793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12461_neg : (2983117 / 10000000) ≤ -Real.log (74207 / 100000) ∧
    -Real.log (74207 / 100000) ≤ (298311701 / 1000000000) := by
  have h := checkLog_sound (w := (25793 / 174207)) (n := 12)
    (lo := (2983117 / 10000000)) (hi := (298311701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74207) = 1/(74207 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12461 : Bounds (-298311701 / 1000000000) (-2983117 / 10000000) (Real.log (74207 / 100000)) := by
  have h := reflection_log_12461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12462_neg : (230297103 / 1000000000) ≤ -Real.log (500000 / 629487) ∧
    -Real.log (500000 / 629487) ≤ (14393569 / 62500000) := by
  have h := checkLog_sound (w := (129487 / 1129487)) (n := 12)
    (lo := (230297103 / 1000000000)) (hi := (14393569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629487 / 500000) = 1/(500000 / 629487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12462 : Bounds (230297103 / 1000000000) (14393569 / 62500000) (Real.log (629487 / 500000)) := by
  have h := reflection_log_12462_neg
  have he : Real.log (629487 / 500000) = -Real.log (500000 / 629487) := by
    rw [show ((629487 / 500000) : ℝ) = ((500000 / 629487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12463_neg : (149859783 / 500000000) ≤ -Real.log (370513 / 500000) ∧
    -Real.log (370513 / 500000) ≤ (299719567 / 1000000000) := by
  have h := checkLog_sound (w := (129487 / 870513)) (n := 12)
    (lo := (149859783 / 500000000)) (hi := (299719567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370513) = 1/(370513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12463 : Bounds (-299719567 / 1000000000) (-149859783 / 500000000) (Real.log (370513 / 500000)) := by
  have h := reflection_log_12463_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12464_neg : (69422463 / 1000000000) ≤ -Real.log (233233116831 / 250000000000) ∧
    -Real.log (233233116831 / 250000000000) ≤ (542363 / 7812500) := by
  have h := checkLog_sound (w := (16766883169 / 483233116831)) (n := 12)
    (lo := (69422463 / 1000000000)) (hi := (542363 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 233233116831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 233233116831) = 1/(233233116831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12464 : Bounds (-542363 / 7812500) (-69422463 / 1000000000) (Real.log (233233116831 / 250000000000)) := by
  have h := reflection_log_12464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12465_neg : (68844187 / 1000000000) ≤ -Real.log (9334721151 / 10000000000) ∧
    -Real.log (9334721151 / 10000000000) ≤ (17211047 / 250000000) := by
  have h := checkLog_sound (w := (665278849 / 19334721151)) (n := 12)
    (lo := (68844187 / 1000000000)) (hi := (17211047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9334721151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9334721151) = 1/(9334721151 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12465 : Bounds (-17211047 / 250000000) (-68844187 / 1000000000) (Real.log (9334721151 / 10000000000)) := by
  have h := reflection_log_12465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12466_neg : (527779213 / 1000000000) ≤ -Real.log (500000000000 / 847581764523) ∧
    -Real.log (500000000000 / 847581764523) ≤ (263889607 / 500000000) := by
  have h := checkLog_sound (w := (347581764523 / 1347581764523)) (n := 12)
    (lo := (527779213 / 1000000000)) (hi := (263889607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847581764523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847581764523 / 500000000000) = 1/(500000000000 / 847581764523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12466 : Bounds (527779213 / 1000000000) (263889607 / 500000000) (Real.log (847581764523 / 500000000000)) := by
  have h := reflection_log_12466_neg
  have he : Real.log (847581764523 / 500000000000) = -Real.log (500000000000 / 847581764523) := by
    rw [show ((847581764523 / 500000000000) : ℝ) = ((500000000000 / 847581764523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12467_neg : (53001667 / 100000000) ≤ -Real.log (500000000000 / 849480315131) ∧
    -Real.log (500000000000 / 849480315131) ≤ (530016671 / 1000000000) := by
  have h := checkLog_sound (w := (349480315131 / 1349480315131)) (n := 12)
    (lo := (53001667 / 100000000)) (hi := (530016671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849480315131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849480315131 / 500000000000) = 1/(500000000000 / 849480315131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12467 : Bounds (53001667 / 100000000) (530016671 / 1000000000) (Real.log (849480315131 / 500000000000)) := by
  have h := reflection_log_12467_neg
  have he : Real.log (849480315131 / 500000000000) = -Real.log (500000000000 / 849480315131) := by
    rw [show ((849480315131 / 500000000000) : ℝ) = ((500000000000 / 849480315131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12468_neg : (1080031793 / 1000000000) ≤ -Real.log (500000000000 / 1472386587771) ∧
    -Real.log (500000000000 / 1472386587771) ≤ (216006359 / 200000000) := by
  have h := checkLog_sound (w := (472386587771 / 2472386587771)) (n := 12)
    (lo := (386884613 / 1000000000)) (hi := (193442307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472386587771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1472386587771 / 1000000000000) = 1/(500000000000 / 1472386587771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12468 : Bounds (1080031793 / 1000000000) (216006359 / 200000000) (Real.log (1472386587771 / 500000000000)) := by
  have h := reflection_log_12468_neg
  have he : Real.log (1472386587771 / 500000000000) = -Real.log (500000000000 / 1472386587771) := by
    rw [show ((1472386587771 / 500000000000) : ℝ) = ((500000000000 / 1472386587771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12469_neg : (216535139 / 200000000) ≤ -Real.log (500000000000 / 1476284584981) ∧
    -Real.log (500000000000 / 1476284584981) ≤ (1082675697 / 1000000000) := by
  have h := checkLog_sound (w := (476284584981 / 2476284584981)) (n := 12)
    (lo := (77905703 / 200000000)) (hi := (97382129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1476284584981 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1476284584981 / 1000000000000) = 1/(500000000000 / 1476284584981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12469 : Bounds (216535139 / 200000000) (1082675697 / 1000000000) (Real.log (1476284584981 / 500000000000)) := by
  have h := reflection_log_12469_neg
  have he : Real.log (1476284584981 / 500000000000) = -Real.log (500000000000 / 1476284584981) := by
    rw [show ((1476284584981 / 500000000000) : ℝ) = ((500000000000 / 1476284584981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12470_neg : (201063103 / 500000000) ≤ -Real.log (200 / 299) ∧
    -Real.log (200 / 299) ≤ (402126207 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 499)) (n := 12)
    (lo := (201063103 / 500000000)) (hi := (402126207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 200) = 1/(200 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12470 : Bounds (201063103 / 500000000) (402126207 / 1000000000) (Real.log (299 / 200)) := by
  have h := reflection_log_12470_neg
  have he : Real.log (299 / 200) = -Real.log (200 / 299) := by
    rw [show ((299 / 200) : ℝ) = ((200 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12471_neg : (683196849 / 1000000000) ≤ -Real.log (101 / 200) ∧
    -Real.log (101 / 200) ≤ (13663937 / 20000000) := by
  have h := checkLog_sound (w := (99 / 301)) (n := 12)
    (lo := (683196849 / 1000000000)) (hi := (13663937 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 101) = 1/(101 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12471 : Bounds (-13663937 / 20000000) (-683196849 / 1000000000) (Real.log (101 / 200)) := by
  have h := reflection_log_12471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12472_neg : (494877 / 1000000000) ≤ -Real.log (200000 / 200099) ∧
    -Real.log (200000 / 200099) ≤ (247439 / 500000000) := by
  have h := checkLog_sound (w := (99 / 400099)) (n := 12)
    (lo := (494877 / 1000000000)) (hi := (247439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200099 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200099 / 200000) = 1/(200000 / 200099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12472 : Bounds (494877 / 1000000000) (247439 / 500000000) (Real.log (200099 / 200000)) := by
  have h := reflection_log_12472_neg
  have he : Real.log (200099 / 200000) = -Real.log (200000 / 200099) := by
    rw [show ((200099 / 200000) : ℝ) = ((200000 / 200099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12473_neg : (247561 / 500000000) ≤ -Real.log (199901 / 200000) ∧
    -Real.log (199901 / 200000) ≤ (495123 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 399901)) (n := 12)
    (lo := (247561 / 500000000)) (hi := (495123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199901) = 1/(199901 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12473 : Bounds (-495123 / 1000000000) (-247561 / 500000000) (Real.log (199901 / 200000)) := by
  have h := reflection_log_12473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12474_neg : (57481127 / 250000000) ≤ -Real.log (200000 / 251701) ∧
    -Real.log (200000 / 251701) ≤ (229924509 / 1000000000) := by
  have h := checkLog_sound (w := (51701 / 451701)) (n := 12)
    (lo := (57481127 / 250000000)) (hi := (229924509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251701 / 200000) = 1/(200000 / 251701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12474 : Bounds (57481127 / 250000000) (229924509 / 1000000000) (Real.log (251701 / 200000)) := by
  have h := reflection_log_12474_neg
  have he : Real.log (251701 / 200000) = -Real.log (200000 / 251701) := by
    rw [show ((251701 / 200000) : ℝ) = ((200000 / 251701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12475_neg : (14954343 / 50000000) ≤ -Real.log (148299 / 200000) ∧
    -Real.log (148299 / 200000) ≤ (299086861 / 1000000000) := by
  have h := checkLog_sound (w := (51701 / 348299)) (n := 12)
    (lo := (14954343 / 50000000)) (hi := (299086861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 148299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 148299) = 1/(148299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12475 : Bounds (-299086861 / 1000000000) (-14954343 / 50000000) (Real.log (148299 / 200000)) := by
  have h := reflection_log_12475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12476_neg : (115377257 / 500000000) ≤ -Real.log (20000 / 25191) ∧
    -Real.log (20000 / 25191) ≤ (46150903 / 200000000) := by
  have h := checkLog_sound (w := (5191 / 45191)) (n := 12)
    (lo := (115377257 / 500000000)) (hi := (46150903 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25191 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25191 / 20000) = 1/(20000 / 25191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12476 : Bounds (115377257 / 500000000) (46150903 / 200000000) (Real.log (25191 / 20000)) := by
  have h := reflection_log_12476_neg
  have he : Real.log (25191 / 20000) = -Real.log (20000 / 25191) := by
    rw [show ((25191 / 20000) : ℝ) = ((20000 / 25191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12477_neg : (300497169 / 1000000000) ≤ -Real.log (14809 / 20000) ∧
    -Real.log (14809 / 20000) ≤ (30049717 / 100000000) := by
  have h := checkLog_sound (w := (5191 / 34809)) (n := 12)
    (lo := (300497169 / 1000000000)) (hi := (30049717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 14809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 14809) = 1/(14809 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12477 : Bounds (-30049717 / 100000000) (-300497169 / 1000000000) (Real.log (14809 / 20000)) := by
  have h := reflection_log_12477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12478_neg : (13948531 / 200000000) ≤ -Real.log (373053519 / 400000000) ∧
    -Real.log (373053519 / 400000000) ≤ (1089729 / 15625000) := by
  have h := checkLog_sound (w := (26946481 / 773053519)) (n := 12)
    (lo := (13948531 / 200000000)) (hi := (1089729 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 373053519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 373053519) = 1/(373053519 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12478 : Bounds (-1089729 / 15625000) (-13948531 / 200000000) (Real.log (373053519 / 400000000)) := by
  have h := reflection_log_12478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12479_neg : (69162351 / 1000000000) ≤ -Real.log (37327006599 / 40000000000) ∧
    -Real.log (37327006599 / 40000000000) ≤ (4322647 / 62500000) := by
  have h := checkLog_sound (w := (2672993401 / 77327006599)) (n := 12)
    (lo := (69162351 / 1000000000)) (hi := (4322647 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37327006599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37327006599) = 1/(37327006599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12479 : Bounds (-4322647 / 62500000) (-69162351 / 1000000000) (Real.log (37327006599 / 40000000000)) := by
  have h := reflection_log_12479_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
