import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10560_neg : (149377387 / 200000000) ≤ -Real.log (7812500000 / 16487655521) ∧
    -Real.log (7812500000 / 16487655521) ≤ (746886937 / 1000000000) := by
  have h := checkLog_sound (w := (862655521 / 32112655521)) (n := 12)
    (lo := (10747951 / 200000000)) (hi := (13434939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16487655521 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16487655521 / 15625000000) = 1/(7812500000 / 16487655521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10560 : Bounds (149377387 / 200000000) (746886937 / 1000000000) (Real.log (16487655521 / 7812500000)) := by
  have h := reflection_log_10560_neg
  have he : Real.log (16487655521 / 7812500000) = -Real.log (7812500000 / 16487655521) := by
    rw [show ((16487655521 / 7812500000) : ℝ) = ((7812500000 / 16487655521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10561_neg : (306013029 / 1000000000) ≤ -Real.log (500 / 679) ∧
    -Real.log (500 / 679) ≤ (30601303 / 100000000) := by
  have h := checkLog_sound (w := (179 / 1179)) (n := 12)
    (lo := (306013029 / 1000000000)) (hi := (30601303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 500) = 1/(500 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10561 : Bounds (306013029 / 1000000000) (30601303 / 100000000) (Real.log (679 / 500)) := by
  have h := reflection_log_10561_neg
  have he : Real.log (679 / 500) = -Real.log (500 / 679) := by
    rw [show ((679 / 500) : ℝ) = ((500 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10562_neg : (17726679 / 40000000) ≤ -Real.log (321 / 500) ∧
    -Real.log (321 / 500) ≤ (1731121 / 3906250) := by
  have h := checkLog_sound (w := (179 / 821)) (n := 12)
    (lo := (17726679 / 40000000)) (hi := (1731121 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 321) = 1/(321 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10562 : Bounds (-1731121 / 3906250) (-17726679 / 40000000) (Real.log (321 / 500)) := by
  have h := reflection_log_10562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10563_neg : (71587 / 200000000) ≤ -Real.log (500000 / 500179) ∧
    -Real.log (500000 / 500179) ≤ (22371 / 62500000) := by
  have h := checkLog_sound (w := (179 / 1000179)) (n := 12)
    (lo := (71587 / 200000000)) (hi := (22371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500179 / 500000) = 1/(500000 / 500179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10563 : Bounds (71587 / 200000000) (22371 / 62500000) (Real.log (500179 / 500000)) := by
  have h := reflection_log_10563_neg
  have he : Real.log (500179 / 500000) = -Real.log (500000 / 500179) := by
    rw [show ((500179 / 500000) : ℝ) = ((500000 / 500179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10564_neg : (22379 / 62500000) ≤ -Real.log (499821 / 500000) ∧
    -Real.log (499821 / 500000) ≤ (71613 / 200000000) := by
  have h := checkLog_sound (w := (179 / 999821)) (n := 12)
    (lo := (22379 / 62500000)) (hi := (71613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499821) = 1/(499821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10564 : Bounds (-71613 / 200000000) (-22379 / 62500000) (Real.log (499821 / 500000)) := by
  have h := reflection_log_10564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10565_neg : (41926737 / 250000000) ≤ -Real.log (100000 / 118259) ∧
    -Real.log (100000 / 118259) ≤ (167706949 / 1000000000) := by
  have h := checkLog_sound (w := (18259 / 218259)) (n := 12)
    (lo := (41926737 / 250000000)) (hi := (167706949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118259 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118259 / 100000) = 1/(100000 / 118259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10565 : Bounds (41926737 / 250000000) (167706949 / 1000000000) (Real.log (118259 / 100000)) := by
  have h := reflection_log_10565_neg
  have he : Real.log (118259 / 100000) = -Real.log (100000 / 118259) := by
    rw [show ((118259 / 100000) : ℝ) = ((100000 / 118259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10566_neg : (100807237 / 500000000) ≤ -Real.log (81741 / 100000) ∧
    -Real.log (81741 / 100000) ≤ (8064579 / 40000000) := by
  have h := checkLog_sound (w := (18259 / 181741)) (n := 12)
    (lo := (100807237 / 500000000)) (hi := (8064579 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81741) = 1/(81741 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10566 : Bounds (-8064579 / 40000000) (-100807237 / 500000000) (Real.log (81741 / 100000)) := by
  have h := reflection_log_10566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10567_neg : (16845587 / 100000000) ≤ -Real.log (250000 / 295869) ∧
    -Real.log (250000 / 295869) ≤ (168455871 / 1000000000) := by
  have h := checkLog_sound (w := (45869 / 545869)) (n := 12)
    (lo := (16845587 / 100000000)) (hi := (168455871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295869 / 250000) = 1/(250000 / 295869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10567 : Bounds (16845587 / 100000000) (168455871 / 1000000000) (Real.log (295869 / 250000)) := by
  have h := reflection_log_10567_neg
  have he : Real.log (295869 / 250000) = -Real.log (250000 / 295869) := by
    rw [show ((295869 / 250000) : ℝ) = ((250000 / 295869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10568_neg : (202698973 / 1000000000) ≤ -Real.log (204131 / 250000) ∧
    -Real.log (204131 / 250000) ≤ (101349487 / 500000000) := by
  have h := checkLog_sound (w := (45869 / 454131)) (n := 12)
    (lo := (202698973 / 1000000000)) (hi := (101349487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204131) = 1/(204131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10568 : Bounds (-101349487 / 500000000) (-202698973 / 1000000000) (Real.log (204131 / 250000)) := by
  have h := reflection_log_10568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10569_neg : (17121551 / 500000000) ≤ -Real.log (60396034839 / 62500000000) ∧
    -Real.log (60396034839 / 62500000000) ≤ (34243103 / 1000000000) := by
  have h := checkLog_sound (w := (2103965161 / 122896034839)) (n := 12)
    (lo := (17121551 / 500000000)) (hi := (34243103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60396034839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60396034839) = 1/(60396034839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10569 : Bounds (-34243103 / 1000000000) (-17121551 / 500000000) (Real.log (60396034839 / 62500000000)) := by
  have h := reflection_log_10569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10570_neg : (1356301 / 40000000) ≤ -Real.log (9666608919 / 10000000000) ∧
    -Real.log (9666608919 / 10000000000) ≤ (16953763 / 500000000) := by
  have h := checkLog_sound (w := (333391081 / 19666608919)) (n := 12)
    (lo := (1356301 / 40000000)) (hi := (16953763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9666608919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9666608919) = 1/(9666608919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10570 : Bounds (-16953763 / 500000000) (-1356301 / 40000000) (Real.log (9666608919 / 10000000000)) := by
  have h := reflection_log_10570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10571_neg : (184660711 / 500000000) ≤ -Real.log (6250000000 / 9042203423) ∧
    -Real.log (6250000000 / 9042203423) ≤ (369321423 / 1000000000) := by
  have h := checkLog_sound (w := (2792203423 / 15292203423)) (n := 12)
    (lo := (184660711 / 500000000)) (hi := (369321423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9042203423 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9042203423 / 6250000000) = 1/(6250000000 / 9042203423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10571 : Bounds (184660711 / 500000000) (369321423 / 1000000000) (Real.log (9042203423 / 6250000000)) := by
  have h := reflection_log_10571_neg
  have he : Real.log (9042203423 / 6250000000) = -Real.log (6250000000 / 9042203423) := by
    rw [show ((9042203423 / 6250000000) : ℝ) = ((6250000000 / 9042203423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10572_neg : (92788711 / 250000000) ≤ -Real.log (100000000000 / 144940748833) ∧
    -Real.log (100000000000 / 144940748833) ≤ (74230969 / 200000000) := by
  have h := checkLog_sound (w := (44940748833 / 244940748833)) (n := 12)
    (lo := (92788711 / 250000000)) (hi := (74230969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144940748833 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144940748833 / 100000000000) = 1/(100000000000 / 144940748833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10572 : Bounds (92788711 / 250000000) (74230969 / 200000000) (Real.log (144940748833 / 100000000000)) := by
  have h := reflection_log_10572_neg
  have he : Real.log (144940748833 / 100000000000) = -Real.log (100000000000 / 144940748833) := by
    rw [show ((144940748833 / 100000000000) : ℝ) = ((100000000000 / 144940748833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10573_neg : (149377387 / 200000000) ≤ -Real.log (500000000000 / 1055209953343) ∧
    -Real.log (500000000000 / 1055209953343) ≤ (746886937 / 1000000000) := by
  have h := checkLog_sound (w := (55209953343 / 2055209953343)) (n := 12)
    (lo := (10747951 / 200000000)) (hi := (13434939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055209953343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055209953343 / 1000000000000) = 1/(500000000000 / 1055209953343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10573 : Bounds (149377387 / 200000000) (746886937 / 1000000000) (Real.log (1055209953343 / 500000000000)) := by
  have h := reflection_log_10573_neg
  have he : Real.log (1055209953343 / 500000000000) = -Real.log (500000000000 / 1055209953343) := by
    rw [show ((1055209953343 / 500000000000) : ℝ) = ((500000000000 / 1055209953343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10574_neg : (749180003 / 1000000000) ≤ -Real.log (250000000000 / 528816199377) ∧
    -Real.log (250000000000 / 528816199377) ≤ (149836001 / 200000000) := by
  have h := checkLog_sound (w := (28816199377 / 1028816199377)) (n := 12)
    (lo := (56032823 / 1000000000)) (hi := (7004103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528816199377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528816199377 / 500000000000) = 1/(250000000000 / 528816199377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10574 : Bounds (749180003 / 1000000000) (149836001 / 200000000) (Real.log (528816199377 / 250000000000)) := by
  have h := reflection_log_10574_neg
  have he : Real.log (528816199377 / 250000000000) = -Real.log (250000000000 / 528816199377) := by
    rw [show ((528816199377 / 250000000000) : ℝ) = ((250000000000 / 528816199377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10575_neg : (61349827 / 200000000) ≤ -Real.log (1000 / 1359) ∧
    -Real.log (1000 / 1359) ≤ (19171821 / 62500000) := by
  have h := checkLog_sound (w := (359 / 2359)) (n := 12)
    (lo := (61349827 / 200000000)) (hi := (19171821 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1000) = 1/(1000 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10575 : Bounds (61349827 / 200000000) (19171821 / 62500000) (Real.log (1359 / 1000)) := by
  have h := reflection_log_10575_neg
  have he : Real.log (1359 / 1000) = -Real.log (1000 / 1359) := by
    rw [show ((1359 / 1000) : ℝ) = ((1000 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10576_neg : (222362911 / 500000000) ≤ -Real.log (641 / 1000) ∧
    -Real.log (641 / 1000) ≤ (444725823 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 1641)) (n := 12)
    (lo := (222362911 / 500000000)) (hi := (444725823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 641) = 1/(641 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10576 : Bounds (-444725823 / 1000000000) (-222362911 / 500000000) (Real.log (641 / 1000)) := by
  have h := reflection_log_10576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10577_neg : (71787 / 200000000) ≤ -Real.log (1000000 / 1000359) ∧
    -Real.log (1000000 / 1000359) ≤ (44867 / 125000000) := by
  have h := checkLog_sound (w := (359 / 2000359)) (n := 12)
    (lo := (71787 / 200000000)) (hi := (44867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000359 / 1000000) = 1/(1000000 / 1000359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10577 : Bounds (71787 / 200000000) (44867 / 125000000) (Real.log (1000359 / 1000000)) := by
  have h := reflection_log_10577_neg
  have he : Real.log (1000359 / 1000000) = -Real.log (1000000 / 1000359) := by
    rw [show ((1000359 / 1000000) : ℝ) = ((1000000 / 1000359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10578_neg : (44883 / 125000000) ≤ -Real.log (999641 / 1000000) ∧
    -Real.log (999641 / 1000000) ≤ (71813 / 200000000) := by
  have h := checkLog_sound (w := (359 / 1999641)) (n := 12)
    (lo := (44883 / 125000000)) (hi := (71813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999641) = 1/(999641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10578 : Bounds (-71813 / 200000000) (-44883 / 125000000) (Real.log (999641 / 1000000)) := by
  have h := reflection_log_10578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10579_neg : (21020011 / 125000000) ≤ -Real.log (500000 / 591563) ∧
    -Real.log (500000 / 591563) ≤ (168160089 / 1000000000) := by
  have h := checkLog_sound (w := (91563 / 1091563)) (n := 12)
    (lo := (21020011 / 125000000)) (hi := (168160089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591563 / 500000) = 1/(500000 / 591563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10579 : Bounds (21020011 / 125000000) (168160089 / 1000000000) (Real.log (591563 / 500000)) := by
  have h := reflection_log_10579_neg
  have he : Real.log (591563 / 500000) = -Real.log (500000 / 591563) := by
    rw [show ((591563 / 500000) : ℝ) = ((500000 / 591563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10580_neg : (101135209 / 500000000) ≤ -Real.log (408437 / 500000) ∧
    -Real.log (408437 / 500000) ≤ (202270419 / 1000000000) := by
  have h := checkLog_sound (w := (91563 / 908437)) (n := 12)
    (lo := (101135209 / 500000000)) (hi := (202270419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408437) = 1/(408437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10580 : Bounds (-202270419 / 1000000000) (-101135209 / 500000000) (Real.log (408437 / 500000)) := by
  have h := reflection_log_10580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10581_neg : (4222759 / 25000000) ≤ -Real.log (500000 / 592007) ∧
    -Real.log (500000 / 592007) ≤ (168910361 / 1000000000) := by
  have h := checkLog_sound (w := (92007 / 1092007)) (n := 12)
    (lo := (4222759 / 25000000)) (hi := (168910361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592007 / 500000) = 1/(500000 / 592007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10581 : Bounds (4222759 / 25000000) (168910361 / 1000000000) (Real.log (592007 / 500000)) := by
  have h := reflection_log_10581_neg
  have he : Real.log (592007 / 500000) = -Real.log (500000 / 592007) := by
    rw [show ((592007 / 500000) : ℝ) = ((500000 / 592007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10582_neg : (203358081 / 1000000000) ≤ -Real.log (407993 / 500000) ∧
    -Real.log (407993 / 500000) ≤ (101679041 / 500000000) := by
  have h := checkLog_sound (w := (92007 / 907993)) (n := 12)
    (lo := (203358081 / 1000000000)) (hi := (101679041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407993) = 1/(407993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10582 : Bounds (-101679041 / 500000000) (-203358081 / 1000000000) (Real.log (407993 / 500000)) := by
  have h := reflection_log_10582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10583_neg : (861193 / 25000000) ≤ -Real.log (241534711951 / 250000000000) ∧
    -Real.log (241534711951 / 250000000000) ≤ (34447721 / 1000000000) := by
  have h := checkLog_sound (w := (8465288049 / 491534711951)) (n := 12)
    (lo := (861193 / 25000000)) (hi := (34447721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241534711951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241534711951) = 1/(241534711951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10583 : Bounds (-34447721 / 1000000000) (-861193 / 25000000) (Real.log (241534711951 / 250000000000)) := by
  have h := reflection_log_10583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10584_neg : (3411033 / 100000000) ≤ -Real.log (241616217031 / 250000000000) ∧
    -Real.log (241616217031 / 250000000000) ≤ (34110331 / 1000000000) := by
  have h := checkLog_sound (w := (8383782969 / 491616217031)) (n := 12)
    (lo := (3411033 / 100000000)) (hi := (34110331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241616217031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241616217031) = 1/(241616217031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10584 : Bounds (-34110331 / 1000000000) (-3411033 / 100000000) (Real.log (241616217031 / 250000000000)) := by
  have h := reflection_log_10584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10585_neg : (185215253 / 500000000) ≤ -Real.log (10000000000 / 14483580087) ∧
    -Real.log (10000000000 / 14483580087) ≤ (370430507 / 1000000000) := by
  have h := checkLog_sound (w := (4483580087 / 24483580087)) (n := 12)
    (lo := (185215253 / 500000000)) (hi := (370430507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14483580087 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14483580087 / 10000000000) = 1/(10000000000 / 14483580087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10585 : Bounds (185215253 / 500000000) (370430507 / 1000000000) (Real.log (14483580087 / 10000000000)) := by
  have h := reflection_log_10585_neg
  have he : Real.log (14483580087 / 10000000000) = -Real.log (10000000000 / 14483580087) := by
    rw [show ((14483580087 / 10000000000) : ℝ) = ((10000000000 / 14483580087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10586_neg : (372268441 / 1000000000) ≤ -Real.log (500000000000 / 725511222007) ∧
    -Real.log (500000000000 / 725511222007) ≤ (186134221 / 500000000) := by
  have h := checkLog_sound (w := (225511222007 / 1225511222007)) (n := 12)
    (lo := (372268441 / 1000000000)) (hi := (186134221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725511222007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725511222007 / 500000000000) = 1/(500000000000 / 725511222007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10586 : Bounds (372268441 / 1000000000) (186134221 / 500000000) (Real.log (725511222007 / 500000000000)) := by
  have h := reflection_log_10586_neg
  have he : Real.log (725511222007 / 500000000000) = -Real.log (500000000000 / 725511222007) := by
    rw [show ((725511222007 / 500000000000) : ℝ) = ((500000000000 / 725511222007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10587_neg : (749180003 / 1000000000) ≤ -Real.log (500000000000 / 1057632398753) ∧
    -Real.log (500000000000 / 1057632398753) ≤ (149836001 / 200000000) := by
  have h := checkLog_sound (w := (57632398753 / 2057632398753)) (n := 12)
    (lo := (56032823 / 1000000000)) (hi := (7004103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057632398753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057632398753 / 1000000000000) = 1/(500000000000 / 1057632398753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10587 : Bounds (749180003 / 1000000000) (149836001 / 200000000) (Real.log (1057632398753 / 500000000000)) := by
  have h := reflection_log_10587_neg
  have he : Real.log (1057632398753 / 500000000000) = -Real.log (500000000000 / 1057632398753) := by
    rw [show ((1057632398753 / 500000000000) : ℝ) = ((500000000000 / 1057632398753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10588_neg : (187868739 / 250000000) ≤ -Real.log (500000000000 / 1060062402497) ∧
    -Real.log (500000000000 / 1060062402497) ≤ (375737479 / 500000000) := by
  have h := checkLog_sound (w := (60062402497 / 2060062402497)) (n := 12)
    (lo := (1822743 / 31250000)) (hi := (58327777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060062402497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060062402497 / 1000000000000) = 1/(500000000000 / 1060062402497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10588 : Bounds (187868739 / 250000000) (375737479 / 500000000) (Real.log (1060062402497 / 500000000000)) := by
  have h := reflection_log_10588_neg
  have he : Real.log (1060062402497 / 500000000000) = -Real.log (500000000000 / 1060062402497) := by
    rw [show ((1060062402497 / 500000000000) : ℝ) = ((500000000000 / 1060062402497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10589_neg : (307484699 / 1000000000) ≤ -Real.log (25 / 34) ∧
    -Real.log (25 / 34) ≤ (3074847 / 10000000) := by
  have h := checkLog_sound (w := (9 / 59)) (n := 12)
    (lo := (307484699 / 1000000000)) (hi := (3074847 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34 / 25) = 1/(25 / 34) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10589 : Bounds (307484699 / 1000000000) (3074847 / 10000000) (Real.log (34 / 25)) := by
  have h := reflection_log_10589_neg
  have he : Real.log (34 / 25) = -Real.log (25 / 34) := by
    rw [show ((34 / 25) : ℝ) = ((25 / 34) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10590_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
    -Real.log (16 / 25) ≤ (446287103 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 16) = 1/(16 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10590 : Bounds (-446287103 / 1000000000) (-223143551 / 500000000) (Real.log (16 / 25)) := by
  have h := reflection_log_10590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10591_neg : (71987 / 200000000) ≤ -Real.log (25000 / 25009) ∧
    -Real.log (25000 / 25009) ≤ (703 / 1953125) := by
  have h := checkLog_sound (w := (9 / 50009)) (n := 12)
    (lo := (71987 / 200000000)) (hi := (703 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25009 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25009 / 25000) = 1/(25000 / 25009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10591 : Bounds (71987 / 200000000) (703 / 1953125) (Real.log (25009 / 25000)) := by
  have h := reflection_log_10591_neg
  have he : Real.log (25009 / 25000) = -Real.log (25000 / 25009) := by
    rw [show ((25009 / 25000) : ℝ) = ((25000 / 25009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10592_neg : (2813 / 7812500) ≤ -Real.log (24991 / 25000) ∧
    -Real.log (24991 / 25000) ≤ (72013 / 200000000) := by
  have h := checkLog_sound (w := (9 / 49991)) (n := 12)
    (lo := (2813 / 7812500)) (hi := (72013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24991) = 1/(24991 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10592 : Bounds (-72013 / 200000000) (-2813 / 7812500) (Real.log (24991 / 25000)) := by
  have h := reflection_log_10592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10593_neg : (168613867 / 1000000000) ≤ -Real.log (1000000 / 1183663) ∧
    -Real.log (1000000 / 1183663) ≤ (42153467 / 250000000) := by
  have h := checkLog_sound (w := (183663 / 2183663)) (n := 12)
    (lo := (168613867 / 1000000000)) (hi := (42153467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183663 / 1000000) = 1/(1000000 / 1183663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10593 : Bounds (168613867 / 1000000000) (42153467 / 250000000) (Real.log (1183663 / 1000000)) := by
  have h := reflection_log_10593_neg
  have he : Real.log (1183663 / 1000000) = -Real.log (1000000 / 1183663) := by
    rw [show ((1183663 / 1000000) : ℝ) = ((1000000 / 1183663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10594_neg : (202928019 / 1000000000) ≤ -Real.log (816337 / 1000000) ∧
    -Real.log (816337 / 1000000) ≤ (10146401 / 50000000) := by
  have h := checkLog_sound (w := (183663 / 1816337)) (n := 12)
    (lo := (202928019 / 1000000000)) (hi := (10146401 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816337) = 1/(816337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10594 : Bounds (-10146401 / 50000000) (-202928019 / 1000000000) (Real.log (816337 / 1000000)) := by
  have h := reflection_log_10594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10595_neg : (42341161 / 250000000) ≤ -Real.log (125000 / 148069) ∧
    -Real.log (125000 / 148069) ≤ (33872929 / 200000000) := by
  have h := checkLog_sound (w := (23069 / 273069)) (n := 12)
    (lo := (42341161 / 250000000)) (hi := (33872929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148069 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148069 / 125000) = 1/(125000 / 148069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10595 : Bounds (42341161 / 250000000) (33872929 / 200000000) (Real.log (148069 / 125000)) := by
  have h := reflection_log_10595_neg
  have he : Real.log (148069 / 125000) = -Real.log (125000 / 148069) := by
    rw [show ((148069 / 125000) : ℝ) = ((125000 / 148069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10596_neg : (204017623 / 1000000000) ≤ -Real.log (101931 / 125000) ∧
    -Real.log (101931 / 125000) ≤ (25502203 / 125000000) := by
  have h := checkLog_sound (w := (23069 / 226931)) (n := 12)
    (lo := (204017623 / 1000000000)) (hi := (25502203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101931) = 1/(101931 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10596 : Bounds (-25502203 / 125000000) (-204017623 / 1000000000) (Real.log (101931 / 125000)) := by
  have h := reflection_log_10596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10597_neg : (34652979 / 1000000000) ≤ -Real.log (15092821239 / 15625000000) ∧
    -Real.log (15092821239 / 15625000000) ≤ (1732649 / 50000000) := by
  have h := checkLog_sound (w := (532178761 / 30717821239)) (n := 12)
    (lo := (34652979 / 1000000000)) (hi := (1732649 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15092821239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15092821239) = 1/(15092821239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10597 : Bounds (-1732649 / 50000000) (-34652979 / 1000000000) (Real.log (15092821239 / 15625000000)) := by
  have h := reflection_log_10597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10598_neg : (34314151 / 1000000000) ≤ -Real.log (966267902431 / 1000000000000) ∧
    -Real.log (966267902431 / 1000000000000) ≤ (4289269 / 125000000) := by
  have h := checkLog_sound (w := (33732097569 / 1966267902431)) (n := 12)
    (lo := (34314151 / 1000000000)) (hi := (4289269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966267902431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966267902431) = 1/(966267902431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10598 : Bounds (-4289269 / 125000000) (-34314151 / 1000000000) (Real.log (966267902431 / 1000000000000)) := by
  have h := reflection_log_10598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10599_neg : (185770943 / 500000000) ≤ -Real.log (62500000000 / 90623036197) ∧
    -Real.log (62500000000 / 90623036197) ≤ (371541887 / 1000000000) := by
  have h := checkLog_sound (w := (28123036197 / 153123036197)) (n := 12)
    (lo := (185770943 / 500000000)) (hi := (371541887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90623036197 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90623036197 / 62500000000) = 1/(62500000000 / 90623036197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10599 : Bounds (185770943 / 500000000) (371541887 / 1000000000) (Real.log (90623036197 / 62500000000)) := by
  have h := reflection_log_10599_neg
  have he : Real.log (90623036197 / 62500000000) = -Real.log (62500000000 / 90623036197) := by
    rw [show ((90623036197 / 62500000000) : ℝ) = ((62500000000 / 90623036197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10600_neg : (373382267 / 1000000000) ≤ -Real.log (125000000000 / 181579941333) ∧
    -Real.log (125000000000 / 181579941333) ≤ (93345567 / 250000000) := by
  have h := checkLog_sound (w := (56579941333 / 306579941333)) (n := 12)
    (lo := (373382267 / 1000000000)) (hi := (93345567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181579941333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181579941333 / 125000000000) = 1/(125000000000 / 181579941333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10600 : Bounds (373382267 / 1000000000) (93345567 / 250000000) (Real.log (181579941333 / 125000000000)) := by
  have h := reflection_log_10600_neg
  have he : Real.log (181579941333 / 125000000000) = -Real.log (125000000000 / 181579941333) := by
    rw [show ((181579941333 / 125000000000) : ℝ) = ((125000000000 / 181579941333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10601_neg : (187868739 / 250000000) ≤ -Real.log (7812500000 / 16563475039) ∧
    -Real.log (7812500000 / 16563475039) ≤ (375737479 / 500000000) := by
  have h := checkLog_sound (w := (938475039 / 32188475039)) (n := 12)
    (lo := (1822743 / 31250000)) (hi := (58327777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16563475039 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16563475039 / 15625000000) = 1/(7812500000 / 16563475039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10601 : Bounds (187868739 / 250000000) (375737479 / 500000000) (Real.log (16563475039 / 7812500000)) := by
  have h := reflection_log_10601_neg
  have he : Real.log (16563475039 / 7812500000) = -Real.log (7812500000 / 16563475039) := by
    rw [show ((16563475039 / 7812500000) : ℝ) = ((7812500000 / 16563475039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10602_neg : (753771801 / 1000000000) ≤ -Real.log (8 / 17) ∧
    -Real.log (8 / 17) ≤ (753771803 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 33)) (n := 12)
    (lo := (60624621 / 1000000000)) (hi := (30312311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 16) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(17 / 16) = 1/(8 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10602 : Bounds (753771801 / 1000000000) (753771803 / 1000000000) (Real.log (17 / 8)) := by
  have h := reflection_log_10602_neg
  have he : Real.log (17 / 8) = -Real.log (8 / 17) := by
    rw [show ((17 / 8) : ℝ) = ((8 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10603_neg : (308219723 / 1000000000) ≤ -Real.log (1000 / 1361) ∧
    -Real.log (1000 / 1361) ≤ (77054931 / 250000000) := by
  have h := checkLog_sound (w := (361 / 2361)) (n := 12)
    (lo := (308219723 / 1000000000)) (hi := (77054931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1000) = 1/(1000 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10603 : Bounds (308219723 / 1000000000) (77054931 / 250000000) (Real.log (1361 / 1000)) := by
  have h := reflection_log_10603_neg
  have he : Real.log (1361 / 1000) = -Real.log (1000 / 1361) := by
    rw [show ((1361 / 1000) : ℝ) = ((1000 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10604_neg : (55981353 / 125000000) ≤ -Real.log (639 / 1000) ∧
    -Real.log (639 / 1000) ≤ (17914033 / 40000000) := by
  have h := checkLog_sound (w := (361 / 1639)) (n := 12)
    (lo := (55981353 / 125000000)) (hi := (17914033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 639) = 1/(639 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10604 : Bounds (-17914033 / 40000000) (-55981353 / 125000000) (Real.log (639 / 1000)) := by
  have h := reflection_log_10604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10605_neg : (180467 / 500000000) ≤ -Real.log (1000000 / 1000361) ∧
    -Real.log (1000000 / 1000361) ≤ (72187 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2000361)) (n := 12)
    (lo := (180467 / 500000000)) (hi := (72187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000361 / 1000000) = 1/(1000000 / 1000361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10605 : Bounds (180467 / 500000000) (72187 / 200000000) (Real.log (1000361 / 1000000)) := by
  have h := reflection_log_10605_neg
  have he : Real.log (1000361 / 1000000) = -Real.log (1000000 / 1000361) := by
    rw [show ((1000361 / 1000000) : ℝ) = ((1000000 / 1000361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10606_neg : (72213 / 200000000) ≤ -Real.log (999639 / 1000000) ∧
    -Real.log (999639 / 1000000) ≤ (180533 / 500000000) := by
  have h := checkLog_sound (w := (361 / 1999639)) (n := 12)
    (lo := (72213 / 200000000)) (hi := (180533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999639) = 1/(999639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10606 : Bounds (-180533 / 500000000) (-72213 / 200000000) (Real.log (999639 / 1000000)) := by
  have h := reflection_log_10606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10607_neg : (169818721 / 1000000000) ≤ -Real.log (100000 / 118509) ∧
    -Real.log (100000 / 118509) ≤ (84909361 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 218509)) (n := 12)
    (lo := (169818721 / 1000000000)) (hi := (84909361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118509 / 100000) = 1/(100000 / 118509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10607 : Bounds (169818721 / 1000000000) (84909361 / 500000000) (Real.log (118509 / 100000)) := by
  have h := reflection_log_10607_neg
  have he : Real.log (118509 / 100000) = -Real.log (100000 / 118509) := by
    rw [show ((118509 / 100000) : ℝ) = ((100000 / 118509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10608_neg : (204677601 / 1000000000) ≤ -Real.log (81491 / 100000) ∧
    -Real.log (81491 / 100000) ≤ (102338801 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 181491)) (n := 12)
    (lo := (204677601 / 1000000000)) (hi := (102338801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81491) = 1/(81491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10608 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) (Real.log (81491 / 100000)) := by
  have h := reflection_log_10608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10609_neg : (54467 / 1562500) ≤ -Real.log (9657416919 / 10000000000) ∧
    -Real.log (9657416919 / 10000000000) ≤ (34858881 / 1000000000) := by
  have h := checkLog_sound (w := (342583081 / 19657416919)) (n := 12)
    (lo := (54467 / 1562500)) (hi := (34858881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9657416919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9657416919) = 1/(9657416919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10609 : Bounds (-34858881 / 1000000000) (-54467 / 1562500) (Real.log (9657416919 / 10000000000)) := by
  have h := reflection_log_10609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10610_neg : (3451861 / 100000000) ≤ -Real.log (24151759 / 25000000) ∧
    -Real.log (24151759 / 25000000) ≤ (34518611 / 1000000000) := by
  have h := checkLog_sound (w := (848241 / 49151759)) (n := 12)
    (lo := (3451861 / 100000000)) (hi := (34518611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24151759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24151759) = 1/(24151759 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10610 : Bounds (-34518611 / 1000000000) (-3451861 / 100000000) (Real.log (24151759 / 25000000)) := by
  have h := reflection_log_10610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10611_neg : (187248161 / 500000000) ≤ -Real.log (500000000000 / 727129376251) ∧
    -Real.log (500000000000 / 727129376251) ≤ (374496323 / 1000000000) := by
  have h := checkLog_sound (w := (227129376251 / 1227129376251)) (n := 12)
    (lo := (187248161 / 500000000)) (hi := (374496323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727129376251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727129376251 / 500000000000) = 1/(500000000000 / 727129376251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10611 : Bounds (187248161 / 500000000) (374496323 / 1000000000) (Real.log (727129376251 / 500000000000)) := by
  have h := reflection_log_10611_neg
  have he : Real.log (727129376251 / 500000000000) = -Real.log (500000000000 / 727129376251) := by
    rw [show ((727129376251 / 500000000000) : ℝ) = ((500000000000 / 727129376251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10612_neg : (756070547 / 1000000000) ≤ -Real.log (250000000000 / 532472613459) ∧
    -Real.log (250000000000 / 532472613459) ≤ (756070549 / 1000000000) := by
  have h := checkLog_sound (w := (32472613459 / 1032472613459)) (n := 12)
    (lo := (62923367 / 1000000000)) (hi := (7865421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532472613459 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532472613459 / 500000000000) = 1/(250000000000 / 532472613459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10612 : Bounds (756070547 / 1000000000) (756070549 / 1000000000) (Real.log (532472613459 / 250000000000)) := by
  have h := reflection_log_10612_neg
  have he : Real.log (532472613459 / 250000000000) = -Real.log (250000000000 / 532472613459) := by
    rw [show ((532472613459 / 250000000000) : ℝ) = ((250000000000 / 532472613459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10613_neg : (308954207 / 1000000000) ≤ -Real.log (500 / 681) ∧
    -Real.log (500 / 681) ≤ (9654819 / 31250000) := by
  have h := checkLog_sound (w := (181 / 1181)) (n := 12)
    (lo := (308954207 / 1000000000)) (hi := (9654819 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 500) = 1/(500 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10613 : Bounds (308954207 / 1000000000) (9654819 / 31250000) (Real.log (681 / 500)) := by
  have h := reflection_log_10613_neg
  have he : Real.log (681 / 500) = -Real.log (500 / 681) := by
    rw [show ((681 / 500) : ℝ) = ((500 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10614_neg : (89883399 / 200000000) ≤ -Real.log (319 / 500) ∧
    -Real.log (319 / 500) ≤ (112354249 / 250000000) := by
  have h := checkLog_sound (w := (181 / 819)) (n := 12)
    (lo := (89883399 / 200000000)) (hi := (112354249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 319) = 1/(319 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10614 : Bounds (-112354249 / 250000000) (-89883399 / 200000000) (Real.log (319 / 500)) := by
  have h := reflection_log_10614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10615_neg : (180967 / 500000000) ≤ -Real.log (500000 / 500181) ∧
    -Real.log (500000 / 500181) ≤ (72387 / 200000000) := by
  have h := checkLog_sound (w := (181 / 1000181)) (n := 12)
    (lo := (180967 / 500000000)) (hi := (72387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500181 / 500000) = 1/(500000 / 500181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10615 : Bounds (180967 / 500000000) (72387 / 200000000) (Real.log (500181 / 500000)) := by
  have h := reflection_log_10615_neg
  have he : Real.log (500181 / 500000) = -Real.log (500000 / 500181) := by
    rw [show ((500181 / 500000) : ℝ) = ((500000 / 500181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10616_neg : (72413 / 200000000) ≤ -Real.log (499819 / 500000) ∧
    -Real.log (499819 / 500000) ≤ (181033 / 500000000) := by
  have h := checkLog_sound (w := (181 / 999819)) (n := 12)
    (lo := (72413 / 200000000)) (hi := (181033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499819) = 1/(499819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10616 : Bounds (-181033 / 500000000) (-72413 / 200000000) (Real.log (499819 / 500000)) := by
  have h := reflection_log_10616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10617_neg : (169520809 / 1000000000) ≤ -Real.log (1000000 / 1184737) ∧
    -Real.log (1000000 / 1184737) ≤ (16952081 / 100000000) := by
  have h := checkLog_sound (w := (184737 / 2184737)) (n := 12)
    (lo := (169520809 / 1000000000)) (hi := (16952081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184737 / 1000000) = 1/(1000000 / 1184737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10617 : Bounds (169520809 / 1000000000) (16952081 / 100000000) (Real.log (1184737 / 1000000)) := by
  have h := reflection_log_10617_neg
  have he : Real.log (1184737 / 1000000) = -Real.log (1000000 / 1184737) := by
    rw [show ((1184737 / 1000000) : ℝ) = ((1000000 / 1184737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10618_neg : (102122259 / 500000000) ≤ -Real.log (815263 / 1000000) ∧
    -Real.log (815263 / 1000000) ≤ (204244519 / 1000000000) := by
  have h := checkLog_sound (w := (184737 / 1815263)) (n := 12)
    (lo := (102122259 / 500000000)) (hi := (204244519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815263) = 1/(815263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10618 : Bounds (-204244519 / 1000000000) (-102122259 / 500000000) (Real.log (815263 / 1000000)) := by
  have h := reflection_log_10618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10619_neg : (10642037 / 62500000) ≤ -Real.log (250000 / 296407) ∧
    -Real.log (250000 / 296407) ≤ (170272593 / 1000000000) := by
  have h := checkLog_sound (w := (46407 / 546407)) (n := 12)
    (lo := (10642037 / 62500000)) (hi := (170272593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296407 / 250000) = 1/(250000 / 296407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10619 : Bounds (10642037 / 62500000) (170272593 / 1000000000) (Real.log (296407 / 250000)) := by
  have h := reflection_log_10619_neg
  have he : Real.log (296407 / 250000) = -Real.log (250000 / 296407) := by
    rw [show ((296407 / 250000) : ℝ) = ((250000 / 296407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10620_neg : (102669007 / 500000000) ≤ -Real.log (203593 / 250000) ∧
    -Real.log (203593 / 250000) ≤ (41067603 / 200000000) := by
  have h := checkLog_sound (w := (46407 / 453593)) (n := 12)
    (lo := (102669007 / 500000000)) (hi := (41067603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203593) = 1/(203593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10620 : Bounds (-41067603 / 200000000) (-102669007 / 500000000) (Real.log (203593 / 250000)) := by
  have h := reflection_log_10620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10621_neg : (17532711 / 500000000) ≤ -Real.log (60346390351 / 62500000000) ∧
    -Real.log (60346390351 / 62500000000) ≤ (35065423 / 1000000000) := by
  have h := checkLog_sound (w := (2153609649 / 122846390351)) (n := 12)
    (lo := (17532711 / 500000000)) (hi := (35065423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60346390351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60346390351) = 1/(60346390351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10621 : Bounds (-35065423 / 1000000000) (-17532711 / 500000000) (Real.log (60346390351 / 62500000000)) := by
  have h := reflection_log_10621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10622_neg : (34723709 / 1000000000) ≤ -Real.log (965872240831 / 1000000000000) ∧
    -Real.log (965872240831 / 1000000000000) ≤ (3472371 / 100000000) := by
  have h := checkLog_sound (w := (34127759169 / 1965872240831)) (n := 12)
    (lo := (34723709 / 1000000000)) (hi := (3472371 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965872240831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965872240831) = 1/(965872240831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10622 : Bounds (-3472371 / 100000000) (-34723709 / 1000000000) (Real.log (965872240831 / 1000000000000)) := by
  have h := reflection_log_10622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10623_neg : (373765327 / 1000000000) ≤ -Real.log (250000000000 / 363299021297) ∧
    -Real.log (250000000000 / 363299021297) ≤ (23360333 / 62500000) := by
  have h := checkLog_sound (w := (113299021297 / 613299021297)) (n := 12)
    (lo := (373765327 / 1000000000)) (hi := (23360333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363299021297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363299021297 / 250000000000) = 1/(250000000000 / 363299021297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10623 : Bounds (373765327 / 1000000000) (23360333 / 62500000) (Real.log (363299021297 / 250000000000)) := by
  have h := reflection_log_10623_neg
  have he : Real.log (363299021297 / 250000000000) = -Real.log (250000000000 / 363299021297) := by
    rw [show ((363299021297 / 250000000000) : ℝ) = ((250000000000 / 363299021297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
