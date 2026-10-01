import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11328_neg : (238820799 / 1000000000) ≤ -Real.log (196889 / 250000) ∧
    -Real.log (196889 / 250000) ≤ (149263 / 625000) := by
  have h := checkLog_sound (w := (53111 / 446889)) (n := 12)
    (lo := (238820799 / 1000000000)) (hi := (149263 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196889) = 1/(196889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11328 : Bounds (-149263 / 625000) (-238820799 / 1000000000) (Real.log (196889 / 250000)) := by
  have h := reflection_log_11328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11329_neg : (193421391 / 1000000000) ≤ -Real.log (500000 / 606697) ∧
    -Real.log (500000 / 606697) ≤ (12088837 / 62500000) := by
  have h := checkLog_sound (w := (106697 / 1106697)) (n := 12)
    (lo := (193421391 / 1000000000)) (hi := (12088837 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606697 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606697 / 500000) = 1/(500000 / 606697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11329 : Bounds (193421391 / 1000000000) (12088837 / 62500000) (Real.log (606697 / 500000)) := by
  have h := reflection_log_11329_neg
  have he : Real.log (606697 / 500000) = -Real.log (500000 / 606697) := by
    rw [show ((606697 / 500000) : ℝ) = ((500000 / 606697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11330_neg : (240027791 / 1000000000) ≤ -Real.log (393303 / 500000) ∧
    -Real.log (393303 / 500000) ≤ (15001737 / 62500000) := by
  have h := checkLog_sound (w := (106697 / 893303)) (n := 12)
    (lo := (240027791 / 1000000000)) (hi := (15001737 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393303) = 1/(393303 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11330 : Bounds (-15001737 / 62500000) (-240027791 / 1000000000) (Real.log (393303 / 500000)) := by
  have h := reflection_log_11330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11331_neg : (46606399 / 1000000000) ≤ -Real.log (238615750191 / 250000000000) ∧
    -Real.log (238615750191 / 250000000000) ≤ (29129 / 625000) := by
  have h := checkLog_sound (w := (11384249809 / 488615750191)) (n := 12)
    (lo := (46606399 / 1000000000)) (hi := (29129 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238615750191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238615750191) = 1/(238615750191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11331 : Bounds (-29129 / 625000) (-46606399 / 1000000000) (Real.log (238615750191 / 250000000000)) := by
  have h := reflection_log_11331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11332_neg : (23091321 / 500000000) ≤ -Real.log (59679221679 / 62500000000) ∧
    -Real.log (59679221679 / 62500000000) ≤ (46182643 / 1000000000) := by
  have h := checkLog_sound (w := (2820778321 / 122179221679)) (n := 12)
    (lo := (23091321 / 500000000)) (hi := (46182643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59679221679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59679221679) = 1/(59679221679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11332 : Bounds (-46182643 / 1000000000) (-23091321 / 500000000) (Real.log (59679221679 / 62500000000)) := by
  have h := reflection_log_11332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11333_neg : (107864739 / 250000000) ≤ -Real.log (250000000000 / 384875488219) ∧
    -Real.log (250000000000 / 384875488219) ≤ (431458957 / 1000000000) := by
  have h := checkLog_sound (w := (134875488219 / 634875488219)) (n := 12)
    (lo := (107864739 / 250000000)) (hi := (431458957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384875488219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384875488219 / 250000000000) = 1/(250000000000 / 384875488219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11333 : Bounds (107864739 / 250000000) (431458957 / 1000000000) (Real.log (384875488219 / 250000000000)) := by
  have h := reflection_log_11333_neg
  have he : Real.log (384875488219 / 250000000000) = -Real.log (250000000000 / 384875488219) := by
    rw [show ((384875488219 / 250000000000) : ℝ) = ((250000000000 / 384875488219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11334_neg : (216724591 / 500000000) ≤ -Real.log (250000000000 / 385642240207) ∧
    -Real.log (250000000000 / 385642240207) ≤ (433449183 / 1000000000) := by
  have h := checkLog_sound (w := (135642240207 / 635642240207)) (n := 12)
    (lo := (216724591 / 500000000)) (hi := (433449183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385642240207 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385642240207 / 250000000000) = 1/(250000000000 / 385642240207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11334 : Bounds (216724591 / 500000000) (433449183 / 1000000000) (Real.log (385642240207 / 250000000000)) := by
  have h := reflection_log_11334_neg
  have he : Real.log (385642240207 / 250000000000) = -Real.log (250000000000 / 385642240207) := by
    rw [show ((385642240207 / 250000000000) : ℝ) = ((250000000000 / 385642240207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11335_neg : (876035469 / 1000000000) ≤ -Real.log (125000000000 / 300170068027) ∧
    -Real.log (125000000000 / 300170068027) ≤ (876035471 / 1000000000) := by
  have h := checkLog_sound (w := (50170068027 / 550170068027)) (n := 12)
    (lo := (182888289 / 1000000000)) (hi := (18288829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300170068027 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(300170068027 / 250000000000) = 1/(125000000000 / 300170068027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11335 : Bounds (876035469 / 1000000000) (876035471 / 1000000000) (Real.log (300170068027 / 125000000000)) := by
  have h := reflection_log_11335_neg
  have he : Real.log (300170068027 / 125000000000) = -Real.log (125000000000 / 300170068027) := by
    rw [show ((300170068027 / 125000000000) : ℝ) = ((125000000000 / 300170068027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11336_neg : (439222781 / 500000000) ≤ -Real.log (500000000000 / 1203577512777) ∧
    -Real.log (500000000000 / 1203577512777) ≤ (219611391 / 250000000) := by
  have h := checkLog_sound (w := (203577512777 / 2203577512777)) (n := 12)
    (lo := (92649191 / 500000000)) (hi := (185298383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203577512777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1203577512777 / 1000000000000) = 1/(500000000000 / 1203577512777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11336 : Bounds (439222781 / 500000000) (219611391 / 250000000) (Real.log (1203577512777 / 500000000000)) := by
  have h := reflection_log_11336_neg
  have he : Real.log (1203577512777 / 500000000000) = -Real.log (500000000000 / 1203577512777) := by
    rw [show ((1203577512777 / 500000000000) : ℝ) = ((500000000000 / 1203577512777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11337_neg : (346422567 / 1000000000) ≤ -Real.log (500 / 707) ∧
    -Real.log (500 / 707) ≤ (43302821 / 125000000) := by
  have h := checkLog_sound (w := (207 / 1207)) (n := 12)
    (lo := (346422567 / 1000000000)) (hi := (43302821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707 / 500) = 1/(500 / 707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11337 : Bounds (346422567 / 1000000000) (43302821 / 125000000) (Real.log (707 / 500)) := by
  have h := reflection_log_11337_neg
  have he : Real.log (707 / 500) = -Real.log (500 / 707) := by
    rw [show ((707 / 500) : ℝ) = ((500 / 707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11338_neg : (534435489 / 1000000000) ≤ -Real.log (293 / 500) ∧
    -Real.log (293 / 500) ≤ (53443549 / 100000000) := by
  have h := checkLog_sound (w := (207 / 793)) (n := 12)
    (lo := (534435489 / 1000000000)) (hi := (53443549 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 293) = 1/(293 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11338 : Bounds (-53443549 / 100000000) (-534435489 / 1000000000) (Real.log (293 / 500)) := by
  have h := reflection_log_11338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11339_neg : (206957 / 500000000) ≤ -Real.log (500000 / 500207) ∧
    -Real.log (500000 / 500207) ≤ (82783 / 200000000) := by
  have h := checkLog_sound (w := (207 / 1000207)) (n := 12)
    (lo := (206957 / 500000000)) (hi := (82783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500207 / 500000) = 1/(500000 / 500207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11339 : Bounds (206957 / 500000000) (82783 / 200000000) (Real.log (500207 / 500000)) := by
  have h := reflection_log_11339_neg
  have he : Real.log (500207 / 500000) = -Real.log (500000 / 500207) := by
    rw [show ((500207 / 500000) : ℝ) = ((500000 / 500207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11340_neg : (82817 / 200000000) ≤ -Real.log (499793 / 500000) ∧
    -Real.log (499793 / 500000) ≤ (207043 / 500000000) := by
  have h := checkLog_sound (w := (207 / 999793)) (n := 12)
    (lo := (82817 / 200000000)) (hi := (207043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499793) = 1/(499793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11340 : Bounds (-207043 / 500000000) (-82817 / 200000000) (Real.log (499793 / 500000)) := by
  have h := reflection_log_11340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11341_neg : (193091683 / 1000000000) ≤ -Real.log (500000 / 606497) ∧
    -Real.log (500000 / 606497) ≤ (48272921 / 250000000) := by
  have h := checkLog_sound (w := (106497 / 1106497)) (n := 12)
    (lo := (193091683 / 1000000000)) (hi := (48272921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606497 / 500000) = 1/(500000 / 606497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11341 : Bounds (193091683 / 1000000000) (48272921 / 250000000) (Real.log (606497 / 500000)) := by
  have h := reflection_log_11341_neg
  have he : Real.log (606497 / 500000) = -Real.log (500000 / 606497) := by
    rw [show ((606497 / 500000) : ℝ) = ((500000 / 606497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11342_neg : (119759703 / 500000000) ≤ -Real.log (393503 / 500000) ∧
    -Real.log (393503 / 500000) ≤ (239519407 / 1000000000) := by
  have h := checkLog_sound (w := (106497 / 893503)) (n := 12)
    (lo := (119759703 / 500000000)) (hi := (239519407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393503) = 1/(393503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11342 : Bounds (-239519407 / 1000000000) (-119759703 / 500000000) (Real.log (393503 / 500000)) := by
  have h := reflection_log_11342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11343_neg : (96937693 / 500000000) ≤ -Real.log (200000 / 242789) ∧
    -Real.log (200000 / 242789) ≤ (193875387 / 1000000000) := by
  have h := checkLog_sound (w := (42789 / 442789)) (n := 12)
    (lo := (96937693 / 500000000)) (hi := (193875387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242789 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242789 / 200000) = 1/(200000 / 242789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11343 : Bounds (96937693 / 500000000) (193875387 / 1000000000) (Real.log (242789 / 200000)) := by
  have h := reflection_log_11343_neg
  have he : Real.log (242789 / 200000) = -Real.log (200000 / 242789) := by
    rw [show ((242789 / 200000) : ℝ) = ((200000 / 242789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11344_neg : (120364257 / 500000000) ≤ -Real.log (157211 / 200000) ∧
    -Real.log (157211 / 200000) ≤ (48145703 / 200000000) := by
  have h := checkLog_sound (w := (42789 / 357211)) (n := 12)
    (lo := (120364257 / 500000000)) (hi := (48145703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157211) = 1/(157211 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11344 : Bounds (-48145703 / 200000000) (-120364257 / 500000000) (Real.log (157211 / 200000)) := by
  have h := reflection_log_11344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11345_neg : (46853127 / 1000000000) ≤ -Real.log (38169101479 / 40000000000) ∧
    -Real.log (38169101479 / 40000000000) ≤ (5856641 / 125000000) := by
  have h := checkLog_sound (w := (1830898521 / 78169101479)) (n := 12)
    (lo := (46853127 / 1000000000)) (hi := (5856641 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38169101479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38169101479) = 1/(38169101479 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11345 : Bounds (-5856641 / 125000000) (-46853127 / 1000000000) (Real.log (38169101479 / 40000000000)) := by
  have h := reflection_log_11345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11346_neg : (46427723 / 1000000000) ≤ -Real.log (238658388991 / 250000000000) ∧
    -Real.log (238658388991 / 250000000000) ≤ (11606931 / 250000000) := by
  have h := checkLog_sound (w := (11341611009 / 488658388991)) (n := 12)
    (lo := (46427723 / 1000000000)) (hi := (11606931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238658388991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238658388991) = 1/(238658388991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11346 : Bounds (-11606931 / 250000000) (-46427723 / 1000000000) (Real.log (238658388991 / 250000000000)) := by
  have h := reflection_log_11346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11347_neg : (43261109 / 100000000) ≤ -Real.log (50000000000 / 77063834329) ∧
    -Real.log (50000000000 / 77063834329) ≤ (432611091 / 1000000000) := by
  have h := checkLog_sound (w := (27063834329 / 127063834329)) (n := 12)
    (lo := (43261109 / 100000000)) (hi := (432611091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77063834329 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77063834329 / 50000000000) = 1/(50000000000 / 77063834329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11347 : Bounds (43261109 / 100000000) (432611091 / 1000000000) (Real.log (77063834329 / 50000000000)) := by
  have h := reflection_log_11347_neg
  have he : Real.log (77063834329 / 50000000000) = -Real.log (50000000000 / 77063834329) := by
    rw [show ((77063834329 / 50000000000) : ℝ) = ((50000000000 / 77063834329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11348_neg : (434603901 / 1000000000) ≤ -Real.log (250000000000 / 386087805561) ∧
    -Real.log (250000000000 / 386087805561) ≤ (217301951 / 500000000) := by
  have h := checkLog_sound (w := (136087805561 / 636087805561)) (n := 12)
    (lo := (434603901 / 1000000000)) (hi := (217301951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386087805561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386087805561 / 250000000000) = 1/(250000000000 / 386087805561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11348 : Bounds (434603901 / 1000000000) (217301951 / 500000000) (Real.log (386087805561 / 250000000000)) := by
  have h := reflection_log_11348_neg
  have he : Real.log (386087805561 / 250000000000) = -Real.log (250000000000 / 386087805561) := by
    rw [show ((386087805561 / 250000000000) : ℝ) = ((250000000000 / 386087805561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11349_neg : (439222781 / 500000000) ≤ -Real.log (62500000000 / 150447189097) ∧
    -Real.log (62500000000 / 150447189097) ≤ (219611391 / 250000000) := by
  have h := checkLog_sound (w := (25447189097 / 275447189097)) (n := 12)
    (lo := (92649191 / 500000000)) (hi := (185298383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150447189097 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(150447189097 / 125000000000) = 1/(62500000000 / 150447189097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11349 : Bounds (439222781 / 500000000) (219611391 / 250000000) (Real.log (150447189097 / 62500000000)) := by
  have h := reflection_log_11349_neg
  have he : Real.log (150447189097 / 62500000000) = -Real.log (62500000000 / 150447189097) := by
    rw [show ((150447189097 / 62500000000) : ℝ) = ((62500000000 / 150447189097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11350_neg : (110107257 / 125000000) ≤ -Real.log (500000000000 / 1206484641639) ∧
    -Real.log (500000000000 / 1206484641639) ≤ (440429029 / 500000000) := by
  have h := checkLog_sound (w := (206484641639 / 2206484641639)) (n := 12)
    (lo := (46927719 / 250000000)) (hi := (187710877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206484641639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1206484641639 / 1000000000000) = 1/(500000000000 / 1206484641639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11350 : Bounds (110107257 / 125000000) (440429029 / 500000000) (Real.log (1206484641639 / 500000000000)) := by
  have h := reflection_log_11350_neg
  have he : Real.log (1206484641639 / 500000000000) = -Real.log (500000000000 / 1206484641639) := by
    rw [show ((1206484641639 / 500000000000) : ℝ) = ((500000000000 / 1206484641639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11351_neg : (347129531 / 1000000000) ≤ -Real.log (200 / 283) ∧
    -Real.log (200 / 283) ≤ (86782383 / 250000000) := by
  have h := checkLog_sound (w := (83 / 483)) (n := 12)
    (lo := (347129531 / 1000000000)) (hi := (86782383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283 / 200) = 1/(200 / 283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11351 : Bounds (347129531 / 1000000000) (86782383 / 250000000) (Real.log (283 / 200)) := by
  have h := reflection_log_11351_neg
  have he : Real.log (283 / 200) = -Real.log (200 / 283) := by
    rw [show ((283 / 200) : ℝ) = ((200 / 283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11352_neg : (536143431 / 1000000000) ≤ -Real.log (117 / 200) ∧
    -Real.log (117 / 200) ≤ (67017929 / 125000000) := by
  have h := checkLog_sound (w := (83 / 317)) (n := 12)
    (lo := (536143431 / 1000000000)) (hi := (67017929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 117) = 1/(117 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11352 : Bounds (-67017929 / 125000000) (-536143431 / 1000000000) (Real.log (117 / 200)) := by
  have h := reflection_log_11352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11353_neg : (414913 / 1000000000) ≤ -Real.log (200000 / 200083) ∧
    -Real.log (200000 / 200083) ≤ (207457 / 500000000) := by
  have h := checkLog_sound (w := (83 / 400083)) (n := 12)
    (lo := (414913 / 1000000000)) (hi := (207457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200083 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200083 / 200000) = 1/(200000 / 200083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11353 : Bounds (414913 / 1000000000) (207457 / 500000000) (Real.log (200083 / 200000)) := by
  have h := reflection_log_11353_neg
  have he : Real.log (200083 / 200000) = -Real.log (200000 / 200083) := by
    rw [show ((200083 / 200000) : ℝ) = ((200000 / 200083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11354_neg : (207543 / 500000000) ≤ -Real.log (199917 / 200000) ∧
    -Real.log (199917 / 200000) ≤ (415087 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 399917)) (n := 12)
    (lo := (207543 / 500000000)) (hi := (415087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199917) = 1/(199917 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11354 : Bounds (-415087 / 1000000000) (-207543 / 500000000) (Real.log (199917 / 200000)) := by
  have h := reflection_log_11354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11355_neg : (48386251 / 250000000) ≤ -Real.log (125000 / 151693) ∧
    -Real.log (125000 / 151693) ≤ (38709001 / 200000000) := by
  have h := checkLog_sound (w := (26693 / 276693)) (n := 12)
    (lo := (48386251 / 250000000)) (hi := (38709001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151693 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151693 / 125000) = 1/(125000 / 151693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11355 : Bounds (48386251 / 250000000) (38709001 / 200000000) (Real.log (151693 / 125000)) := by
  have h := reflection_log_11355_neg
  have he : Real.log (151693 / 125000) = -Real.log (125000 / 151693) := by
    rw [show ((151693 / 125000) : ℝ) = ((125000 / 151693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11356_neg : (120109251 / 500000000) ≤ -Real.log (98307 / 125000) ∧
    -Real.log (98307 / 125000) ≤ (240218503 / 1000000000) := by
  have h := checkLog_sound (w := (26693 / 223307)) (n := 12)
    (lo := (120109251 / 500000000)) (hi := (240218503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98307) = 1/(98307 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11356 : Bounds (-240218503 / 1000000000) (-120109251 / 500000000) (Real.log (98307 / 125000)) := by
  have h := reflection_log_11356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11357_neg : (7773167 / 40000000) ≤ -Real.log (31250 / 37953) ∧
    -Real.log (31250 / 37953) ≤ (24291147 / 125000000) := by
  have h := checkLog_sound (w := (6703 / 69203)) (n := 12)
    (lo := (7773167 / 40000000)) (hi := (24291147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37953 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37953 / 31250) = 1/(31250 / 37953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11357 : Bounds (7773167 / 40000000) (24291147 / 125000000) (Real.log (37953 / 31250)) := by
  have h := reflection_log_11357_neg
  have he : Real.log (37953 / 31250) = -Real.log (31250 / 37953) := by
    rw [show ((37953 / 31250) : ℝ) = ((31250 / 37953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11358_neg : (241429729 / 1000000000) ≤ -Real.log (24547 / 31250) ∧
    -Real.log (24547 / 31250) ≤ (24142973 / 100000000) := by
  have h := checkLog_sound (w := (6703 / 55797)) (n := 12)
    (lo := (241429729 / 1000000000)) (hi := (24142973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24547) = 1/(24547 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11358 : Bounds (-24142973 / 100000000) (-241429729 / 1000000000) (Real.log (24547 / 31250)) := by
  have h := reflection_log_11358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11359_neg : (47100553 / 1000000000) ≤ -Real.log (931632291 / 976562500) ∧
    -Real.log (931632291 / 976562500) ≤ (23550277 / 500000000) := by
  have h := checkLog_sound (w := (44930209 / 1908194791)) (n := 12)
    (lo := (47100553 / 1000000000)) (hi := (23550277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 931632291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 931632291) = 1/(931632291 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11359 : Bounds (-23550277 / 500000000) (-47100553 / 1000000000) (Real.log (931632291 / 976562500)) := by
  have h := reflection_log_11359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11360_neg : (46673497 / 1000000000) ≤ -Real.log (14912483751 / 15625000000) ∧
    -Real.log (14912483751 / 15625000000) ≤ (23336749 / 500000000) := by
  have h := checkLog_sound (w := (712516249 / 30537483751)) (n := 12)
    (lo := (46673497 / 1000000000)) (hi := (23336749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14912483751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14912483751) = 1/(14912483751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11360 : Bounds (-23336749 / 500000000) (-46673497 / 1000000000) (Real.log (14912483751 / 15625000000)) := by
  have h := reflection_log_11360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11361_neg : (216881753 / 500000000) ≤ -Real.log (100000000000 / 154305390257) ∧
    -Real.log (100000000000 / 154305390257) ≤ (433763507 / 1000000000) := by
  have h := checkLog_sound (w := (54305390257 / 254305390257)) (n := 12)
    (lo := (216881753 / 500000000)) (hi := (433763507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154305390257 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154305390257 / 100000000000) = 1/(100000000000 / 154305390257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11361 : Bounds (216881753 / 500000000) (433763507 / 1000000000) (Real.log (154305390257 / 100000000000)) := by
  have h := reflection_log_11361_neg
  have he : Real.log (154305390257 / 100000000000) = -Real.log (100000000000 / 154305390257) := by
    rw [show ((154305390257 / 100000000000) : ℝ) = ((100000000000 / 154305390257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11362_neg : (54469863 / 125000000) ≤ -Real.log (31250000000 / 48316749501) ∧
    -Real.log (31250000000 / 48316749501) ≤ (87151781 / 200000000) := by
  have h := checkLog_sound (w := (17066749501 / 79566749501)) (n := 12)
    (lo := (54469863 / 125000000)) (hi := (87151781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48316749501 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48316749501 / 31250000000) = 1/(31250000000 / 48316749501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11362 : Bounds (54469863 / 125000000) (87151781 / 200000000) (Real.log (48316749501 / 31250000000)) := by
  have h := reflection_log_11362_neg
  have he : Real.log (48316749501 / 31250000000) = -Real.log (31250000000 / 48316749501) := by
    rw [show ((48316749501 / 31250000000) : ℝ) = ((31250000000 / 48316749501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11363_neg : (110107257 / 125000000) ≤ -Real.log (250000000000 / 603242320819) ∧
    -Real.log (250000000000 / 603242320819) ≤ (440429029 / 500000000) := by
  have h := checkLog_sound (w := (103242320819 / 1103242320819)) (n := 12)
    (lo := (46927719 / 250000000)) (hi := (187710877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603242320819 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(603242320819 / 500000000000) = 1/(250000000000 / 603242320819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11363 : Bounds (110107257 / 125000000) (440429029 / 500000000) (Real.log (603242320819 / 250000000000)) := by
  have h := reflection_log_11363_neg
  have he : Real.log (603242320819 / 250000000000) = -Real.log (250000000000 / 603242320819) := by
    rw [show ((603242320819 / 250000000000) : ℝ) = ((250000000000 / 603242320819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11364_neg : (441636481 / 500000000) ≤ -Real.log (250000000000 / 604700854701) ∧
    -Real.log (250000000000 / 604700854701) ≤ (220818241 / 250000000) := by
  have h := checkLog_sound (w := (104700854701 / 1104700854701)) (n := 12)
    (lo := (95062891 / 500000000)) (hi := (190125783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604700854701 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(604700854701 / 500000000000) = 1/(250000000000 / 604700854701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11364 : Bounds (441636481 / 500000000) (220818241 / 250000000) (Real.log (604700854701 / 250000000000)) := by
  have h := reflection_log_11364_neg
  have he : Real.log (604700854701 / 250000000000) = -Real.log (250000000000 / 604700854701) := by
    rw [show ((604700854701 / 250000000000) : ℝ) = ((250000000000 / 604700854701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11365_neg : (69567199 / 200000000) ≤ -Real.log (125 / 177) ∧
    -Real.log (125 / 177) ≤ (86958999 / 250000000) := by
  have h := checkLog_sound (w := (26 / 151)) (n := 12)
    (lo := (69567199 / 200000000)) (hi := (86958999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 125) = 1/(125 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11365 : Bounds (69567199 / 200000000) (86958999 / 250000000) (Real.log (177 / 125)) := by
  have h := reflection_log_11365_neg
  have he : Real.log (177 / 125) = -Real.log (125 / 177) := by
    rw [show ((177 / 125) : ℝ) = ((125 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11366_neg : (67231787 / 125000000) ≤ -Real.log (73 / 125) ∧
    -Real.log (73 / 125) ≤ (537854297 / 1000000000) := by
  have h := checkLog_sound (w := (26 / 99)) (n := 12)
    (lo := (67231787 / 125000000)) (hi := (537854297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 73) = 1/(73 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11366 : Bounds (-537854297 / 1000000000) (-67231787 / 125000000) (Real.log (73 / 125)) := by
  have h := reflection_log_11366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11367_neg : (415913 / 1000000000) ≤ -Real.log (31250 / 31263) ∧
    -Real.log (31250 / 31263) ≤ (207957 / 500000000) := by
  have h := checkLog_sound (w := (13 / 62513)) (n := 12)
    (lo := (415913 / 1000000000)) (hi := (207957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31263 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31263 / 31250) = 1/(31250 / 31263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11367 : Bounds (415913 / 1000000000) (207957 / 500000000) (Real.log (31263 / 31250)) := by
  have h := reflection_log_11367_neg
  have he : Real.log (31263 / 31250) = -Real.log (31250 / 31263) := by
    rw [show ((31263 / 31250) : ℝ) = ((31250 / 31263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11368_neg : (208043 / 500000000) ≤ -Real.log (31237 / 31250) ∧
    -Real.log (31237 / 31250) ≤ (416087 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 62487)) (n := 12)
    (lo := (208043 / 500000000)) (hi := (416087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31237) = 1/(31237 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11368 : Bounds (-416087 / 1000000000) (-208043 / 500000000) (Real.log (31237 / 31250)) := by
  have h := reflection_log_11368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11369_neg : (193998119 / 1000000000) ≤ -Real.log (500000 / 607047) ∧
    -Real.log (500000 / 607047) ≤ (4849953 / 25000000) := by
  have h := checkLog_sound (w := (107047 / 1107047)) (n := 12)
    (lo := (193998119 / 1000000000)) (hi := (4849953 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607047 / 500000) = 1/(500000 / 607047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11369 : Bounds (193998119 / 1000000000) (4849953 / 25000000) (Real.log (607047 / 500000)) := by
  have h := reflection_log_11369_neg
  have he : Real.log (607047 / 500000) = -Real.log (500000 / 607047) := by
    rw [show ((607047 / 500000) : ℝ) = ((500000 / 607047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11370_neg : (120459043 / 500000000) ≤ -Real.log (392953 / 500000) ∧
    -Real.log (392953 / 500000) ≤ (240918087 / 1000000000) := by
  have h := checkLog_sound (w := (107047 / 892953)) (n := 12)
    (lo := (120459043 / 500000000)) (hi := (240918087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392953) = 1/(392953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11370 : Bounds (-240918087 / 1000000000) (-120459043 / 500000000) (Real.log (392953 / 500000)) := by
  have h := reflection_log_11370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11371_neg : (97391791 / 500000000) ≤ -Real.log (125000 / 151881) ∧
    -Real.log (125000 / 151881) ≤ (194783583 / 1000000000) := by
  have h := checkLog_sound (w := (26881 / 276881)) (n := 12)
    (lo := (97391791 / 500000000)) (hi := (194783583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151881 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151881 / 125000) = 1/(125000 / 151881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11371 : Bounds (97391791 / 500000000) (194783583 / 1000000000) (Real.log (151881 / 125000)) := by
  have h := reflection_log_11371_neg
  have he : Real.log (151881 / 125000) = -Real.log (125000 / 151881) := by
    rw [show ((151881 / 125000) : ℝ) = ((125000 / 151881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11372_neg : (242132709 / 1000000000) ≤ -Real.log (98119 / 125000) ∧
    -Real.log (98119 / 125000) ≤ (24213271 / 100000000) := by
  have h := checkLog_sound (w := (26881 / 223119)) (n := 12)
    (lo := (242132709 / 1000000000)) (hi := (24213271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98119) = 1/(98119 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11372 : Bounds (-24213271 / 100000000) (-242132709 / 1000000000) (Real.log (98119 / 125000)) := by
  have h := reflection_log_11372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11373_neg : (47349127 / 1000000000) ≤ -Real.log (14902411839 / 15625000000) ∧
    -Real.log (14902411839 / 15625000000) ≤ (5918641 / 125000000) := by
  have h := checkLog_sound (w := (722588161 / 30527411839)) (n := 12)
    (lo := (47349127 / 1000000000)) (hi := (5918641 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14902411839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14902411839) = 1/(14902411839 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11373 : Bounds (-5918641 / 125000000) (-47349127 / 1000000000) (Real.log (14902411839 / 15625000000)) := by
  have h := reflection_log_11373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11374_neg : (23459983 / 500000000) ≤ -Real.log (238540939791 / 250000000000) ∧
    -Real.log (238540939791 / 250000000000) ≤ (46919967 / 1000000000) := by
  have h := checkLog_sound (w := (11459060209 / 488540939791)) (n := 12)
    (lo := (23459983 / 500000000)) (hi := (46919967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238540939791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238540939791) = 1/(238540939791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11374 : Bounds (-46919967 / 1000000000) (-23459983 / 500000000) (Real.log (238540939791 / 250000000000)) := by
  have h := reflection_log_11374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11375_neg : (217458103 / 500000000) ≤ -Real.log (500000000000 / 772416803027) ∧
    -Real.log (500000000000 / 772416803027) ≤ (434916207 / 1000000000) := by
  have h := checkLog_sound (w := (272416803027 / 1272416803027)) (n := 12)
    (lo := (217458103 / 500000000)) (hi := (434916207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772416803027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772416803027 / 500000000000) = 1/(500000000000 / 772416803027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11375 : Bounds (217458103 / 500000000) (434916207 / 1000000000) (Real.log (772416803027 / 500000000000)) := by
  have h := reflection_log_11375_neg
  have he : Real.log (772416803027 / 500000000000) = -Real.log (500000000000 / 772416803027) := by
    rw [show ((772416803027 / 500000000000) : ℝ) = ((500000000000 / 772416803027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11376_neg : (436916291 / 1000000000) ≤ -Real.log (500000000000 / 773963248709) ∧
    -Real.log (500000000000 / 773963248709) ≤ (109229073 / 250000000) := by
  have h := checkLog_sound (w := (273963248709 / 1273963248709)) (n := 12)
    (lo := (436916291 / 1000000000)) (hi := (109229073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773963248709 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773963248709 / 500000000000) = 1/(500000000000 / 773963248709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11376 : Bounds (436916291 / 1000000000) (109229073 / 250000000) (Real.log (773963248709 / 500000000000)) := by
  have h := reflection_log_11376_neg
  have he : Real.log (773963248709 / 500000000000) = -Real.log (500000000000 / 773963248709) := by
    rw [show ((773963248709 / 500000000000) : ℝ) = ((500000000000 / 773963248709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11377_neg : (441636481 / 500000000) ≤ -Real.log (500000000000 / 1209401709401) ∧
    -Real.log (500000000000 / 1209401709401) ≤ (220818241 / 250000000) := by
  have h := checkLog_sound (w := (209401709401 / 2209401709401)) (n := 12)
    (lo := (95062891 / 500000000)) (hi := (190125783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209401709401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1209401709401 / 1000000000000) = 1/(500000000000 / 1209401709401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11377 : Bounds (441636481 / 500000000) (220818241 / 250000000) (Real.log (1209401709401 / 500000000000)) := by
  have h := reflection_log_11377_neg
  have he : Real.log (1209401709401 / 500000000000) = -Real.log (500000000000 / 1209401709401) := by
    rw [show ((1209401709401 / 500000000000) : ℝ) = ((500000000000 / 1209401709401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11378_neg : (88569029 / 100000000) ≤ -Real.log (125000000000 / 303082191781) ∧
    -Real.log (125000000000 / 303082191781) ≤ (221422573 / 250000000) := by
  have h := checkLog_sound (w := (53082191781 / 553082191781)) (n := 12)
    (lo := (19254311 / 100000000)) (hi := (192543111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303082191781 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(303082191781 / 250000000000) = 1/(125000000000 / 303082191781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11378 : Bounds (88569029 / 100000000) (221422573 / 250000000) (Real.log (303082191781 / 125000000000)) := by
  have h := reflection_log_11378_neg
  have he : Real.log (303082191781 / 125000000000) = -Real.log (125000000000 / 303082191781) := by
    rw [show ((303082191781 / 125000000000) : ℝ) = ((125000000000 / 303082191781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11379_neg : (8713549 / 25000000) ≤ -Real.log (1000 / 1417) ∧
    -Real.log (1000 / 1417) ≤ (348541961 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 2417)) (n := 12)
    (lo := (8713549 / 25000000)) (hi := (348541961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1417 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1417 / 1000) = 1/(1000 / 1417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11379 : Bounds (8713549 / 25000000) (348541961 / 1000000000) (Real.log (1417 / 1000)) := by
  have h := reflection_log_11379_neg
  have he : Real.log (1417 / 1000) = -Real.log (1000 / 1417) := by
    rw [show ((1417 / 1000) : ℝ) = ((1000 / 1417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11380_neg : (134892023 / 250000000) ≤ -Real.log (583 / 1000) ∧
    -Real.log (583 / 1000) ≤ (539568093 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 1583)) (n := 12)
    (lo := (134892023 / 250000000)) (hi := (539568093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 583) = 1/(583 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11380 : Bounds (-539568093 / 1000000000) (-134892023 / 250000000) (Real.log (583 / 1000)) := by
  have h := reflection_log_11380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11381_neg : (416913 / 1000000000) ≤ -Real.log (1000000 / 1000417) ∧
    -Real.log (1000000 / 1000417) ≤ (208457 / 500000000) := by
  have h := checkLog_sound (w := (417 / 2000417)) (n := 12)
    (lo := (416913 / 1000000000)) (hi := (208457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000417 / 1000000) = 1/(1000000 / 1000417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11381 : Bounds (416913 / 1000000000) (208457 / 500000000) (Real.log (1000417 / 1000000)) := by
  have h := reflection_log_11381_neg
  have he : Real.log (1000417 / 1000000) = -Real.log (1000000 / 1000417) := by
    rw [show ((1000417 / 1000000) : ℝ) = ((1000000 / 1000417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11382_neg : (208543 / 500000000) ≤ -Real.log (999583 / 1000000) ∧
    -Real.log (999583 / 1000000) ≤ (417087 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 1999583)) (n := 12)
    (lo := (208543 / 500000000)) (hi := (417087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999583) = 1/(999583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11382 : Bounds (-417087 / 1000000000) (-208543 / 500000000) (Real.log (999583 / 1000000)) := by
  have h := reflection_log_11382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11383_neg : (194451853 / 1000000000) ≤ -Real.log (200000 / 242929) ∧
    -Real.log (200000 / 242929) ≤ (97225927 / 500000000) := by
  have h := checkLog_sound (w := (42929 / 442929)) (n := 12)
    (lo := (194451853 / 1000000000)) (hi := (97225927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242929 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242929 / 200000) = 1/(200000 / 242929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11383 : Bounds (194451853 / 1000000000) (97225927 / 500000000) (Real.log (242929 / 200000)) := by
  have h := reflection_log_11383_neg
  have he : Real.log (242929 / 200000) = -Real.log (200000 / 242929) := by
    rw [show ((242929 / 200000) : ℝ) = ((200000 / 242929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11384_neg : (120809717 / 500000000) ≤ -Real.log (157071 / 200000) ∧
    -Real.log (157071 / 200000) ≤ (48323887 / 200000000) := by
  have h := checkLog_sound (w := (42929 / 357071)) (n := 12)
    (lo := (120809717 / 500000000)) (hi := (48323887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157071) = 1/(157071 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11384 : Bounds (-48323887 / 200000000) (-120809717 / 500000000) (Real.log (157071 / 200000)) := by
  have h := reflection_log_11384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11385_neg : (195236959 / 1000000000) ≤ -Real.log (1000000 / 1215599) ∧
    -Real.log (1000000 / 1215599) ≤ (1220231 / 6250000) := by
  have h := checkLog_sound (w := (215599 / 2215599)) (n := 12)
    (lo := (195236959 / 1000000000)) (hi := (1220231 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215599 / 1000000) = 1/(1000000 / 1215599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11385 : Bounds (195236959 / 1000000000) (1220231 / 6250000) (Real.log (1215599 / 1000000)) := by
  have h := reflection_log_11385_neg
  have he : Real.log (1215599 / 1000000) = -Real.log (1000000 / 1215599) := by
    rw [show ((1215599 / 1000000) : ℝ) = ((1000000 / 1215599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11386_neg : (242834909 / 1000000000) ≤ -Real.log (784401 / 1000000) ∧
    -Real.log (784401 / 1000000) ≤ (24283491 / 100000000) := by
  have h := checkLog_sound (w := (215599 / 1784401)) (n := 12)
    (lo := (242834909 / 1000000000)) (hi := (24283491 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784401) = 1/(784401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11386 : Bounds (-24283491 / 100000000) (-242834909 / 1000000000) (Real.log (784401 / 1000000)) := by
  have h := reflection_log_11386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11387_neg : (951959 / 20000000) ≤ -Real.log (953517071199 / 1000000000000) ∧
    -Real.log (953517071199 / 1000000000000) ≤ (47597951 / 1000000000) := by
  have h := checkLog_sound (w := (46482928801 / 1953517071199)) (n := 12)
    (lo := (951959 / 20000000)) (hi := (47597951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953517071199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953517071199) = 1/(953517071199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11387 : Bounds (-47597951 / 1000000000) (-951959 / 20000000) (Real.log (953517071199 / 1000000000000)) := by
  have h := reflection_log_11387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11388_neg : (47167581 / 1000000000) ≤ -Real.log (38157100959 / 40000000000) ∧
    -Real.log (38157100959 / 40000000000) ≤ (23583791 / 500000000) := by
  have h := checkLog_sound (w := (1842899041 / 78157100959)) (n := 12)
    (lo := (47167581 / 1000000000)) (hi := (23583791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38157100959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38157100959) = 1/(38157100959 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11388 : Bounds (-23583791 / 500000000) (-47167581 / 1000000000) (Real.log (38157100959 / 40000000000)) := by
  have h := reflection_log_11388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11389_neg : (436071287 / 1000000000) ≤ -Real.log (100000000000 / 154661904489) ∧
    -Real.log (100000000000 / 154661904489) ≤ (54508911 / 125000000) := by
  have h := checkLog_sound (w := (54661904489 / 254661904489)) (n := 12)
    (lo := (436071287 / 1000000000)) (hi := (54508911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154661904489 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154661904489 / 100000000000) = 1/(100000000000 / 154661904489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11389 : Bounds (436071287 / 1000000000) (54508911 / 125000000) (Real.log (154661904489 / 100000000000)) := by
  have h := reflection_log_11389_neg
  have he : Real.log (154661904489 / 100000000000) = -Real.log (100000000000 / 154661904489) := by
    rw [show ((154661904489 / 100000000000) : ℝ) = ((100000000000 / 154661904489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11390_neg : (438071869 / 1000000000) ≤ -Real.log (500000000000 / 774858140161) ∧
    -Real.log (500000000000 / 774858140161) ≤ (43807187 / 100000000) := by
  have h := checkLog_sound (w := (274858140161 / 1274858140161)) (n := 12)
    (lo := (438071869 / 1000000000)) (hi := (43807187 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774858140161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774858140161 / 500000000000) = 1/(500000000000 / 774858140161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11390 : Bounds (438071869 / 1000000000) (43807187 / 100000000) (Real.log (774858140161 / 500000000000)) := by
  have h := reflection_log_11390_neg
  have he : Real.log (774858140161 / 500000000000) = -Real.log (500000000000 / 774858140161) := by
    rw [show ((774858140161 / 500000000000) : ℝ) = ((500000000000 / 774858140161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11391_neg : (88569029 / 100000000) ≤ -Real.log (500000000000 / 1212328767123) ∧
    -Real.log (500000000000 / 1212328767123) ≤ (221422573 / 250000000) := by
  have h := checkLog_sound (w := (212328767123 / 2212328767123)) (n := 12)
    (lo := (19254311 / 100000000)) (hi := (192543111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212328767123 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212328767123 / 1000000000000) = 1/(500000000000 / 1212328767123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11391 : Bounds (88569029 / 100000000) (221422573 / 250000000) (Real.log (1212328767123 / 500000000000)) := by
  have h := reflection_log_11391_neg
  have he : Real.log (1212328767123 / 500000000000) = -Real.log (500000000000 / 1212328767123) := by
    rw [show ((1212328767123 / 500000000000) : ℝ) = ((500000000000 / 1212328767123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
