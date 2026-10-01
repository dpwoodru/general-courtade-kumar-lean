import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14336_neg : (1166680629 / 1000000000) ≤ -Real.log (500000000000 / 1605657691651) ∧
    -Real.log (500000000000 / 1605657691651) ≤ (1166680631 / 1000000000) := by
  have h := checkLog_sound (w := (605657691651 / 2605657691651)) (n := 12)
    (lo := (473533449 / 1000000000)) (hi := (9470669 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1605657691651 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1605657691651 / 1000000000000) = 1/(500000000000 / 1605657691651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14336 : Bounds (1166680629 / 1000000000) (1166680631 / 1000000000) (Real.log (1605657691651 / 500000000000)) := by
  have h := reflection_log_14336_neg
  have he : Real.log (1605657691651 / 500000000000) = -Real.log (500000000000 / 1605657691651) := by
    rw [show ((1605657691651 / 500000000000) : ℝ) = ((500000000000 / 1605657691651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14337_neg : (293987747 / 250000000) ≤ -Real.log (500000000000 / 1620611923777) ∧
    -Real.log (500000000000 / 1620611923777) ≤ (117595099 / 100000000) := by
  have h := checkLog_sound (w := (620611923777 / 2620611923777)) (n := 12)
    (lo := (15087619 / 31250000)) (hi := (482803809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1620611923777 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1620611923777 / 1000000000000) = 1/(500000000000 / 1620611923777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14337 : Bounds (293987747 / 250000000) (117595099 / 100000000) (Real.log (1620611923777 / 500000000000)) := by
  have h := reflection_log_14337_neg
  have he : Real.log (1620611923777 / 500000000000) = -Real.log (500000000000 / 1620611923777) := by
    rw [show ((1620611923777 / 500000000000) : ℝ) = ((500000000000 / 1620611923777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14338_neg : (1380217667 / 500000000) ≤ -Real.log (500000000000 / 7903361344537) ∧
    -Real.log (500000000000 / 7903361344537) ≤ (1380217669 / 500000000) := by
  have h := checkLog_sound (w := (3903361344537 / 11903361344537)) (n := 12)
    (lo := (340496897 / 500000000)) (hi := (136198759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7903361344537 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7903361344537 / 4000000000000) = 1/(500000000000 / 7903361344537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14338 : Bounds (1380217667 / 500000000) (1380217669 / 500000000) (Real.log (7903361344537 / 500000000000)) := by
  have h := reflection_log_14338_neg
  have he : Real.log (7903361344537 / 500000000000) = -Real.log (500000000000 / 7903361344537) := by
    rw [show ((7903361344537 / 500000000000) : ℝ) = ((500000000000 / 7903361344537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14339_neg : (2787562261 / 1000000000) ≤ -Real.log (500000000000 / 8120689655173) ∧
    -Real.log (500000000000 / 8120689655173) ≤ (1393781133 / 500000000) := by
  have h := checkLog_sound (w := (120689655173 / 16120689655173)) (n := 12)
    (lo := (14973541 / 1000000000)) (hi := (7486771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8120689655173 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8120689655173 / 8000000000000) = 1/(500000000000 / 8120689655173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14339 : Bounds (2787562261 / 1000000000) (1393781133 / 500000000) (Real.log (8120689655173 / 500000000000)) := by
  have h := reflection_log_14339_neg
  have he : Real.log (8120689655173 / 500000000000) = -Real.log (500000000000 / 8120689655173) := by
    rw [show ((8120689655173 / 500000000000) : ℝ) = ((500000000000 / 8120689655173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14340_neg : (317494133 / 500000000) ≤ -Real.log (1000 / 1887) ∧
    -Real.log (1000 / 1887) ≤ (634988267 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 2887)) (n := 12)
    (lo := (317494133 / 500000000)) (hi := (634988267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1000) = 1/(1000 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14340 : Bounds (317494133 / 500000000) (634988267 / 1000000000) (Real.log (1887 / 1000)) := by
  have h := reflection_log_14340_neg
  have he : Real.log (1887 / 1000) = -Real.log (1000 / 1887) := by
    rw [show ((1887 / 1000) : ℝ) = ((1000 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14341_neg : (1090183729 / 500000000) ≤ -Real.log (113 / 1000) ∧
    -Real.log (113 / 1000) ≤ (1090183731 / 500000000) := by
  have h := checkLog_sound (w := (6 / 119)) (n := 12)
    (lo := (50462959 / 500000000)) (hi := (100925919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 113) = 1/(113 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14341 : Bounds (-1090183731 / 500000000) (-1090183729 / 500000000) (Real.log (113 / 1000)) := by
  have h := reflection_log_14341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14342_neg : (443303 / 500000000) ≤ -Real.log (1000000 / 1000887) ∧
    -Real.log (1000000 / 1000887) ≤ (886607 / 1000000000) := by
  have h := checkLog_sound (w := (887 / 2000887)) (n := 12)
    (lo := (443303 / 500000000)) (hi := (886607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000887 / 1000000) = 1/(1000000 / 1000887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14342 : Bounds (443303 / 500000000) (886607 / 1000000000) (Real.log (1000887 / 1000000)) := by
  have h := reflection_log_14342_neg
  have he : Real.log (1000887 / 1000000) = -Real.log (1000000 / 1000887) := by
    rw [show ((1000887 / 1000000) : ℝ) = ((1000000 / 1000887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14343_neg : (887393 / 1000000000) ≤ -Real.log (999113 / 1000000) ∧
    -Real.log (999113 / 1000000) ≤ (443697 / 500000000) := by
  have h := checkLog_sound (w := (887 / 1999113)) (n := 12)
    (lo := (887393 / 1000000000)) (hi := (443697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999113) = 1/(999113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14343 : Bounds (-443697 / 500000000) (-887393 / 1000000000) (Real.log (999113 / 1000000)) := by
  have h := reflection_log_14343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14344_neg : (211902287 / 500000000) ≤ -Real.log (1000000 / 1527763) ∧
    -Real.log (1000000 / 1527763) ≤ (16952183 / 40000000) := by
  have h := checkLog_sound (w := (527763 / 2527763)) (n := 12)
    (lo := (211902287 / 500000000)) (hi := (16952183 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527763 / 1000000) = 1/(1000000 / 1527763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14344 : Bounds (211902287 / 500000000) (16952183 / 40000000) (Real.log (1527763 / 1000000)) := by
  have h := reflection_log_14344_neg
  have he : Real.log (1527763 / 1000000) = -Real.log (1000000 / 1527763) := by
    rw [show ((1527763 / 1000000) : ℝ) = ((1000000 / 1527763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14345_neg : (7502743 / 10000000) ≤ -Real.log (472237 / 1000000) ∧
    -Real.log (472237 / 1000000) ≤ (375137151 / 500000000) := by
  have h := checkLog_sound (w := (27763 / 972237)) (n := 12)
    (lo := (714089 / 12500000)) (hi := (57127121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 472237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 472237) = 1/(472237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14345 : Bounds (-375137151 / 500000000) (-7502743 / 10000000) (Real.log (472237 / 1000000)) := by
  have h := reflection_log_14345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14346_neg : (53250753 / 125000000) ≤ -Real.log (100000 / 153113) ∧
    -Real.log (100000 / 153113) ≤ (17040241 / 40000000) := by
  have h := checkLog_sound (w := (53113 / 253113)) (n := 12)
    (lo := (53250753 / 125000000)) (hi := (17040241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153113 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153113 / 100000) = 1/(100000 / 153113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14346 : Bounds (53250753 / 125000000) (17040241 / 40000000) (Real.log (153113 / 100000)) := by
  have h := reflection_log_14346_neg
  have he : Real.log (153113 / 100000) = -Real.log (100000 / 153113) := by
    rw [show ((153113 / 100000) : ℝ) = ((100000 / 153113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14347_neg : (757429733 / 1000000000) ≤ -Real.log (46887 / 100000) ∧
    -Real.log (46887 / 100000) ≤ (151485947 / 200000000) := by
  have h := checkLog_sound (w := (3113 / 96887)) (n := 12)
    (lo := (64282553 / 1000000000)) (hi := (32141277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46887) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 46887) = 1/(46887 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14347 : Bounds (-151485947 / 200000000) (-757429733 / 1000000000) (Real.log (46887 / 100000)) := by
  have h := reflection_log_14347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14348_neg : (331423709 / 1000000000) ≤ -Real.log (7179009231 / 10000000000) ∧
    -Real.log (7179009231 / 10000000000) ≤ (33142371 / 100000000) := by
  have h := checkLog_sound (w := (2820990769 / 17179009231)) (n := 12)
    (lo := (331423709 / 1000000000)) (hi := (33142371 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7179009231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7179009231) = 1/(7179009231 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14348 : Bounds (-33142371 / 100000000) (-331423709 / 1000000000) (Real.log (7179009231 / 10000000000)) := by
  have h := reflection_log_14348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14349_neg : (163234863 / 500000000) ≤ -Real.log (721466215831 / 1000000000000) ∧
    -Real.log (721466215831 / 1000000000000) ≤ (326469727 / 1000000000) := by
  have h := checkLog_sound (w := (278533784169 / 1721466215831)) (n := 12)
    (lo := (163234863 / 500000000)) (hi := (326469727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 721466215831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 721466215831) = 1/(721466215831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14349 : Bounds (-326469727 / 1000000000) (-163234863 / 500000000) (Real.log (721466215831 / 1000000000000)) := by
  have h := reflection_log_14349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14350_neg : (587039437 / 500000000) ≤ -Real.log (500000000000 / 1617580791001) ∧
    -Real.log (500000000000 / 1617580791001) ≤ (293519719 / 250000000) := by
  have h := checkLog_sound (w := (617580791001 / 2617580791001)) (n := 12)
    (lo := (240465847 / 500000000)) (hi := (96186339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617580791001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1617580791001 / 1000000000000) = 1/(500000000000 / 1617580791001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14350 : Bounds (587039437 / 500000000) (293519719 / 250000000) (Real.log (1617580791001 / 500000000000)) := by
  have h := reflection_log_14350_neg
  have he : Real.log (1617580791001 / 500000000000) = -Real.log (500000000000 / 1617580791001) := by
    rw [show ((1617580791001 / 500000000000) : ℝ) = ((500000000000 / 1617580791001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14351_neg : (591717879 / 500000000) ≤ -Real.log (20000000000 / 65311493591) ∧
    -Real.log (20000000000 / 65311493591) ≤ (14792947 / 12500000) := by
  have h := checkLog_sound (w := (25311493591 / 105311493591)) (n := 12)
    (lo := (245144289 / 500000000)) (hi := (490288579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65311493591 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65311493591 / 40000000000) = 1/(20000000000 / 65311493591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14351 : Bounds (591717879 / 500000000) (14792947 / 12500000) (Real.log (65311493591 / 20000000000)) := by
  have h := reflection_log_14351_neg
  have he : Real.log (65311493591 / 20000000000) = -Real.log (20000000000 / 65311493591) := by
    rw [show ((65311493591 / 20000000000) : ℝ) = ((20000000000 / 65311493591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14352_neg : (2787562261 / 1000000000) ≤ -Real.log (125000000000 / 2030172413793) ∧
    -Real.log (125000000000 / 2030172413793) ≤ (1393781133 / 500000000) := by
  have h := checkLog_sound (w := (30172413793 / 4030172413793)) (n := 12)
    (lo := (14973541 / 1000000000)) (hi := (7486771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2030172413793 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2030172413793 / 2000000000000) = 1/(125000000000 / 2030172413793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14352 : Bounds (2787562261 / 1000000000) (1393781133 / 500000000) (Real.log (2030172413793 / 125000000000)) := by
  have h := reflection_log_14352_neg
  have he : Real.log (2030172413793 / 125000000000) = -Real.log (125000000000 / 2030172413793) := by
    rw [show ((2030172413793 / 125000000000) : ℝ) = ((125000000000 / 2030172413793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14353_neg : (703838931 / 250000000) ≤ -Real.log (125000000000 / 2087389380531) ∧
    -Real.log (125000000000 / 2087389380531) ≤ (2815355729 / 1000000000) := by
  have h := checkLog_sound (w := (87389380531 / 4087389380531)) (n := 12)
    (lo := (10691751 / 250000000)) (hi := (8553401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2087389380531 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2087389380531 / 2000000000000) = 1/(125000000000 / 2087389380531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14353 : Bounds (703838931 / 250000000) (2815355729 / 1000000000) (Real.log (2087389380531 / 125000000000)) := by
  have h := reflection_log_14353_neg
  have he : Real.log (2087389380531 / 125000000000) = -Real.log (125000000000 / 2087389380531) := by
    rw [show ((2087389380531 / 125000000000) : ℝ) = ((125000000000 / 2087389380531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14354_neg : (636576829 / 1000000000) ≤ -Real.log (100 / 189) ∧
    -Real.log (100 / 189) ≤ (63657683 / 100000000) := by
  have h := checkLog_sound (w := (89 / 289)) (n := 12)
    (lo := (636576829 / 1000000000)) (hi := (63657683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 100) = 1/(100 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14354 : Bounds (636576829 / 1000000000) (63657683 / 100000000) (Real.log (189 / 100)) := by
  have h := reflection_log_14354_neg
  have he : Real.log (189 / 100) = -Real.log (100 / 189) := by
    rw [show ((189 / 100) : ℝ) = ((100 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14355_neg : (2207274911 / 1000000000) ≤ -Real.log (11 / 100) ∧
    -Real.log (11 / 100) ≤ (441454983 / 200000000) := by
  have h := checkLog_sound (w := (3 / 47)) (n := 12)
    (lo := (127833371 / 1000000000)) (hi := (31958343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 22) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 22) = 1/(11 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14355 : Bounds (-441454983 / 200000000) (-2207274911 / 1000000000) (Real.log (11 / 100)) := by
  have h := reflection_log_14355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14356_neg : (222401 / 250000000) ≤ -Real.log (100000 / 100089) ∧
    -Real.log (100000 / 100089) ≤ (177921 / 200000000) := by
  have h := checkLog_sound (w := (89 / 200089)) (n := 12)
    (lo := (222401 / 250000000)) (hi := (177921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100089 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100089 / 100000) = 1/(100000 / 100089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14356 : Bounds (222401 / 250000000) (177921 / 200000000) (Real.log (100089 / 100000)) := by
  have h := reflection_log_14356_neg
  have he : Real.log (100089 / 100000) = -Real.log (100000 / 100089) := by
    rw [show ((100089 / 100000) : ℝ) = ((100000 / 100089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14357_neg : (222599 / 250000000) ≤ -Real.log (99911 / 100000) ∧
    -Real.log (99911 / 100000) ≤ (890397 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 199911)) (n := 12)
    (lo := (222599 / 250000000)) (hi := (890397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99911) = 1/(99911 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14357 : Bounds (-890397 / 1000000000) (-222599 / 250000000) (Real.log (99911 / 100000)) := by
  have h := reflection_log_14357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14358_neg : (106391269 / 250000000) ≤ -Real.log (200000 / 306091) ∧
    -Real.log (200000 / 306091) ≤ (425565077 / 1000000000) := by
  have h := checkLog_sound (w := (106091 / 506091)) (n := 12)
    (lo := (106391269 / 250000000)) (hi := (425565077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306091 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306091 / 200000) = 1/(200000 / 306091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14358 : Bounds (106391269 / 250000000) (425565077 / 1000000000) (Real.log (306091 / 200000)) := by
  have h := reflection_log_14358_neg
  have he : Real.log (306091 / 200000) = -Real.log (200000 / 306091) := by
    rw [show ((306091 / 200000) : ℝ) = ((200000 / 306091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14359_neg : (755991137 / 1000000000) ≤ -Real.log (93909 / 200000) ∧
    -Real.log (93909 / 200000) ≤ (755991139 / 1000000000) := by
  have h := checkLog_sound (w := (6091 / 193909)) (n := 12)
    (lo := (62843957 / 1000000000)) (hi := (31421979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 93909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 93909) = 1/(93909 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14359 : Bounds (-755991139 / 1000000000) (-755991137 / 1000000000) (Real.log (93909 / 200000)) := by
  have h := reflection_log_14359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14360_neg : (85554879 / 200000000) ≤ -Real.log (12500 / 19173) ∧
    -Real.log (12500 / 19173) ≤ (106943599 / 250000000) := by
  have h := checkLog_sound (w := (6673 / 31673)) (n := 12)
    (lo := (85554879 / 200000000)) (hi := (106943599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19173 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19173 / 12500) = 1/(12500 / 19173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14360 : Bounds (85554879 / 200000000) (106943599 / 250000000) (Real.log (19173 / 12500)) := by
  have h := reflection_log_14360_neg
  have he : Real.log (19173 / 12500) = -Real.log (12500 / 19173) := by
    rw [show ((19173 / 12500) : ℝ) = ((12500 / 19173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14361_neg : (152645271 / 200000000) ≤ -Real.log (5827 / 12500) ∧
    -Real.log (5827 / 12500) ≤ (763226357 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 12077)) (n := 12)
    (lo := (2803167 / 40000000)) (hi := (8759897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5827) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 5827) = 1/(5827 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14361 : Bounds (-763226357 / 1000000000) (-152645271 / 200000000) (Real.log (5827 / 12500)) := by
  have h := reflection_log_14361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14362_neg : (335451961 / 1000000000) ≤ -Real.log (111721071 / 156250000) ∧
    -Real.log (111721071 / 156250000) ≤ (167725981 / 500000000) := by
  have h := checkLog_sound (w := (44528929 / 267971071)) (n := 12)
    (lo := (335451961 / 1000000000)) (hi := (167725981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 111721071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 111721071) = 1/(111721071 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14362 : Bounds (-167725981 / 500000000) (-335451961 / 1000000000) (Real.log (111721071 / 156250000)) := by
  have h := reflection_log_14362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14363_neg : (330426061 / 1000000000) ≤ -Real.log (28744699719 / 40000000000) ∧
    -Real.log (28744699719 / 40000000000) ≤ (165213031 / 500000000) := by
  have h := checkLog_sound (w := (11255300281 / 68744699719)) (n := 12)
    (lo := (330426061 / 1000000000)) (hi := (165213031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 28744699719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 28744699719) = 1/(28744699719 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14363 : Bounds (-165213031 / 500000000) (-330426061 / 1000000000) (Real.log (28744699719 / 40000000000)) := by
  have h := reflection_log_14363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14364_neg : (590778107 / 500000000) ≤ -Real.log (125000000000 / 407430331491) ∧
    -Real.log (125000000000 / 407430331491) ≤ (147694527 / 125000000) := by
  have h := checkLog_sound (w := (157430331491 / 657430331491)) (n := 12)
    (lo := (244204517 / 500000000)) (hi := (97681807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407430331491 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(407430331491 / 250000000000) = 1/(125000000000 / 407430331491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14364 : Bounds (590778107 / 500000000) (147694527 / 125000000) (Real.log (407430331491 / 125000000000)) := by
  have h := reflection_log_14364_neg
  have he : Real.log (407430331491 / 125000000000) = -Real.log (125000000000 / 407430331491) := by
    rw [show ((407430331491 / 125000000000) : ℝ) = ((125000000000 / 407430331491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14365_neg : (4764003 / 4000000) ≤ -Real.log (500000000000 / 1645186202163) ∧
    -Real.log (500000000000 / 1645186202163) ≤ (74437547 / 62500000) := by
  have h := checkLog_sound (w := (645186202163 / 2645186202163)) (n := 12)
    (lo := (49785357 / 100000000)) (hi := (497853571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1645186202163 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1645186202163 / 1000000000000) = 1/(500000000000 / 1645186202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14365 : Bounds (4764003 / 4000000) (74437547 / 62500000) (Real.log (1645186202163 / 500000000000)) := by
  have h := reflection_log_14365_neg
  have he : Real.log (1645186202163 / 500000000000) = -Real.log (500000000000 / 1645186202163) := by
    rw [show ((1645186202163 / 500000000000) : ℝ) = ((500000000000 / 1645186202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14366_neg : (703838931 / 250000000) ≤ -Real.log (500000000000 / 8349557522123) ∧
    -Real.log (500000000000 / 8349557522123) ≤ (2815355729 / 1000000000) := by
  have h := checkLog_sound (w := (349557522123 / 16349557522123)) (n := 12)
    (lo := (10691751 / 250000000)) (hi := (8553401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8349557522123 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8349557522123 / 8000000000000) = 1/(500000000000 / 8349557522123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14366 : Bounds (703838931 / 250000000) (2815355729 / 1000000000) (Real.log (8349557522123 / 500000000000)) := by
  have h := reflection_log_14366_neg
  have he : Real.log (8349557522123 / 500000000000) = -Real.log (500000000000 / 8349557522123) := by
    rw [show ((8349557522123 / 500000000000) : ℝ) = ((500000000000 / 8349557522123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14367_neg : (142192587 / 50000000) ≤ -Real.log (50000000000 / 859090909091) ∧
    -Real.log (50000000000 / 859090909091) ≤ (568770349 / 200000000) := by
  have h := checkLog_sound (w := (59090909091 / 1659090909091)) (n := 12)
    (lo := (3563151 / 50000000)) (hi := (71263021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859090909091 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(859090909091 / 800000000000) = 1/(50000000000 / 859090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14367 : Bounds (142192587 / 50000000) (568770349 / 200000000) (Real.log (859090909091 / 50000000000)) := by
  have h := reflection_log_14367_neg
  have he : Real.log (859090909091 / 50000000000) = -Real.log (50000000000 / 859090909091) := by
    rw [show ((859090909091 / 50000000000) : ℝ) = ((50000000000 / 859090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14368_neg : (79770359 / 125000000) ≤ -Real.log (1000 / 1893) ∧
    -Real.log (1000 / 1893) ≤ (638162873 / 1000000000) := by
  have h := checkLog_sound (w := (893 / 2893)) (n := 12)
    (lo := (79770359 / 125000000)) (hi := (638162873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1893 / 1000) = 1/(1000 / 1893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14368 : Bounds (79770359 / 125000000) (638162873 / 1000000000) (Real.log (1893 / 1000)) := by
  have h := reflection_log_14368_neg
  have he : Real.log (1893 / 1000) = -Real.log (1000 / 1893) := by
    rw [show ((1893 / 1000) : ℝ) = ((1000 / 1893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14369_neg : (1117463221 / 500000000) ≤ -Real.log (107 / 1000) ∧
    -Real.log (107 / 1000) ≤ (1117463223 / 500000000) := by
  have h := checkLog_sound (w := (9 / 116)) (n := 12)
    (lo := (77742451 / 500000000)) (hi := (155484903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 107) = 1/(107 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14369 : Bounds (-1117463223 / 500000000) (-1117463221 / 500000000) (Real.log (107 / 1000)) := by
  have h := reflection_log_14369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14370_neg : (892601 / 1000000000) ≤ -Real.log (1000000 / 1000893) ∧
    -Real.log (1000000 / 1000893) ≤ (446301 / 500000000) := by
  have h := checkLog_sound (w := (893 / 2000893)) (n := 12)
    (lo := (892601 / 1000000000)) (hi := (446301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000893 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000893 / 1000000) = 1/(1000000 / 1000893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14370 : Bounds (892601 / 1000000000) (446301 / 500000000) (Real.log (1000893 / 1000000)) := by
  have h := reflection_log_14370_neg
  have he : Real.log (1000893 / 1000000) = -Real.log (1000000 / 1000893) := by
    rw [show ((1000893 / 1000000) : ℝ) = ((1000000 / 1000893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14371_neg : (446699 / 500000000) ≤ -Real.log (999107 / 1000000) ∧
    -Real.log (999107 / 1000000) ≤ (893399 / 1000000000) := by
  have h := checkLog_sound (w := (893 / 1999107)) (n := 12)
    (lo := (446699 / 500000000)) (hi := (893399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999107) = 1/(999107 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14371 : Bounds (-893399 / 1000000000) (-446699 / 500000000) (Real.log (999107 / 1000000)) := by
  have h := reflection_log_14371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14372_neg : (213667439 / 500000000) ≤ -Real.log (500000 / 766583) ∧
    -Real.log (500000 / 766583) ≤ (427334879 / 1000000000) := by
  have h := checkLog_sound (w := (266583 / 1266583)) (n := 12)
    (lo := (213667439 / 500000000)) (hi := (427334879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766583 / 500000) = 1/(500000 / 766583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14372 : Bounds (213667439 / 500000000) (427334879 / 1000000000) (Real.log (766583 / 500000)) := by
  have h := reflection_log_14372_neg
  have he : Real.log (766583 / 500000) = -Real.log (500000 / 766583) := by
    rw [show ((766583 / 500000) : ℝ) = ((500000 / 766583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14373_neg : (95222693 / 125000000) ≤ -Real.log (233417 / 500000) ∧
    -Real.log (233417 / 500000) ≤ (380890773 / 500000000) := by
  have h := checkLog_sound (w := (16583 / 483417)) (n := 12)
    (lo := (17158591 / 250000000)) (hi := (13726873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 233417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 233417) = 1/(233417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14373 : Bounds (-380890773 / 500000000) (-95222693 / 125000000) (Real.log (233417 / 500000)) := by
  have h := reflection_log_14373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14374_neg : (429552659 / 1000000000) ≤ -Real.log (100000 / 153657) ∧
    -Real.log (100000 / 153657) ≤ (21477633 / 50000000) := by
  have h := checkLog_sound (w := (53657 / 253657)) (n := 12)
    (lo := (429552659 / 1000000000)) (hi := (21477633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153657 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153657 / 100000) = 1/(100000 / 153657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14374 : Bounds (429552659 / 1000000000) (21477633 / 50000000) (Real.log (153657 / 100000)) := by
  have h := reflection_log_14374_neg
  have he : Real.log (153657 / 100000) = -Real.log (100000 / 153657) := by
    rw [show ((153657 / 100000) : ℝ) = ((100000 / 153657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14375_neg : (769099929 / 1000000000) ≤ -Real.log (46343 / 100000) ∧
    -Real.log (46343 / 100000) ≤ (769099931 / 1000000000) := by
  have h := checkLog_sound (w := (3657 / 96343)) (n := 12)
    (lo := (75952749 / 1000000000)) (hi := (303811 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46343) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 46343) = 1/(46343 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14375 : Bounds (-769099931 / 1000000000) (-769099929 / 1000000000) (Real.log (46343 / 100000)) := by
  have h := reflection_log_14375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14376_neg : (33954727 / 100000000) ≤ -Real.log (7120926351 / 10000000000) ∧
    -Real.log (7120926351 / 10000000000) ≤ (339547271 / 1000000000) := by
  have h := checkLog_sound (w := (2879073649 / 17120926351)) (n := 12)
    (lo := (33954727 / 100000000)) (hi := (339547271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 7120926351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 7120926351) = 1/(7120926351 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14376 : Bounds (-339547271 / 1000000000) (-33954727 / 100000000) (Real.log (7120926351 / 10000000000)) := by
  have h := reflection_log_14376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14377_neg : (167223333 / 500000000) ≤ -Real.log (178933504111 / 250000000000) ∧
    -Real.log (178933504111 / 250000000000) ≤ (334446667 / 1000000000) := by
  have h := checkLog_sound (w := (71066495889 / 428933504111)) (n := 12)
    (lo := (167223333 / 500000000)) (hi := (334446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 178933504111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 178933504111) = 1/(178933504111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14377 : Bounds (-334446667 / 1000000000) (-167223333 / 500000000) (Real.log (178933504111 / 250000000000)) := by
  have h := reflection_log_14377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14378_neg : (594558211 / 500000000) ≤ -Real.log (250000000000 / 821044525463) ∧
    -Real.log (250000000000 / 821044525463) ≤ (148639553 / 125000000) := by
  have h := checkLog_sound (w := (321044525463 / 1321044525463)) (n := 12)
    (lo := (247984621 / 500000000)) (hi := (495969243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821044525463 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(821044525463 / 500000000000) = 1/(250000000000 / 821044525463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14378 : Bounds (594558211 / 500000000) (148639553 / 125000000) (Real.log (821044525463 / 250000000000)) := by
  have h := reflection_log_14378_neg
  have he : Real.log (821044525463 / 250000000000) = -Real.log (250000000000 / 821044525463) := by
    rw [show ((821044525463 / 250000000000) : ℝ) = ((250000000000 / 821044525463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14379_neg : (1198652589 / 1000000000) ≤ -Real.log (488281250 / 1618967957) ∧
    -Real.log (488281250 / 1618967957) ≤ (1198652591 / 1000000000) := by
  have h := checkLog_sound (w := (642405457 / 2595530457)) (n := 12)
    (lo := (505505409 / 1000000000)) (hi := (50550541 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1618967957 / 976562500) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1618967957 / 976562500) = 1/(488281250 / 1618967957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14379 : Bounds (1198652589 / 1000000000) (1198652591 / 1000000000) (Real.log (1618967957 / 488281250)) := by
  have h := reflection_log_14379_neg
  have he : Real.log (1618967957 / 488281250) = -Real.log (488281250 / 1618967957) := by
    rw [show ((1618967957 / 488281250) : ℝ) = ((488281250 / 1618967957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14380_neg : (142192587 / 50000000) ≤ -Real.log (500000000000 / 8590909090909) ∧
    -Real.log (500000000000 / 8590909090909) ≤ (568770349 / 200000000) := by
  have h := checkLog_sound (w := (590909090909 / 16590909090909)) (n := 12)
    (lo := (3563151 / 50000000)) (hi := (71263021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8590909090909 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8590909090909 / 8000000000000) = 1/(500000000000 / 8590909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14380 : Bounds (142192587 / 50000000) (568770349 / 200000000) (Real.log (8590909090909 / 500000000000)) := by
  have h := reflection_log_14380_neg
  have he : Real.log (8590909090909 / 500000000000) = -Real.log (500000000000 / 8590909090909) := by
    rw [show ((8590909090909 / 500000000000) : ℝ) = ((500000000000 / 8590909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14381_neg : (1436544657 / 500000000) ≤ -Real.log (125000000000 / 2211448598131) ∧
    -Real.log (125000000000 / 2211448598131) ≤ (2873089319 / 1000000000) := by
  have h := checkLog_sound (w := (211448598131 / 4211448598131)) (n := 12)
    (lo := (50250297 / 500000000)) (hi := (20100119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2211448598131 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2211448598131 / 2000000000000) = 1/(125000000000 / 2211448598131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14381 : Bounds (1436544657 / 500000000) (2873089319 / 1000000000) (Real.log (2211448598131 / 125000000000)) := by
  have h := reflection_log_14381_neg
  have he : Real.log (2211448598131 / 125000000000) = -Real.log (125000000000 / 2211448598131) := by
    rw [show ((2211448598131 / 125000000000) : ℝ) = ((125000000000 / 2211448598131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14382_neg : (639746403 / 1000000000) ≤ -Real.log (125 / 237) ∧
    -Real.log (125 / 237) ≤ (159936601 / 250000000) := by
  have h := checkLog_sound (w := (56 / 181)) (n := 12)
    (lo := (639746403 / 1000000000)) (hi := (159936601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 125) = 1/(125 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14382 : Bounds (639746403 / 1000000000) (159936601 / 250000000) (Real.log (237 / 125)) := by
  have h := reflection_log_14382_neg
  have he : Real.log (237 / 125) = -Real.log (125 / 237) := by
    rw [show ((237 / 125) : ℝ) = ((125 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14383_neg : (1131682189 / 500000000) ≤ -Real.log (13 / 125) ∧
    -Real.log (13 / 125) ≤ (1131682191 / 500000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 104) = 1/(13 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14383 : Bounds (-1131682191 / 500000000) (-1131682189 / 500000000) (Real.log (13 / 125)) := by
  have h := reflection_log_14383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14384_neg : (447799 / 500000000) ≤ -Real.log (15625 / 15639) ∧
    -Real.log (15625 / 15639) ≤ (895599 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 15632)) (n := 12)
    (lo := (447799 / 500000000)) (hi := (895599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15639 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15639 / 15625) = 1/(15625 / 15639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14384 : Bounds (447799 / 500000000) (895599 / 1000000000) (Real.log (15639 / 15625)) := by
  have h := reflection_log_14384_neg
  have he : Real.log (15639 / 15625) = -Real.log (15625 / 15639) := by
    rw [show ((15639 / 15625) : ℝ) = ((15625 / 15639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14385_neg : (896401 / 1000000000) ≤ -Real.log (15611 / 15625) ∧
    -Real.log (15611 / 15625) ≤ (448201 / 500000000) := by
  have h := checkLog_sound (w := (7 / 15618)) (n := 12)
    (lo := (896401 / 1000000000)) (hi := (448201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15611) = 1/(15611 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14385 : Bounds (-448201 / 500000000) (-896401 / 1000000000) (Real.log (15611 / 15625)) := by
  have h := reflection_log_14385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14386_neg : (107278481 / 250000000) ≤ -Real.log (125000 / 191987) ∧
    -Real.log (125000 / 191987) ≤ (17164557 / 40000000) := by
  have h := checkLog_sound (w := (66987 / 316987)) (n := 12)
    (lo := (107278481 / 250000000)) (hi := (17164557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191987 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191987 / 125000) = 1/(125000 / 191987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14386 : Bounds (107278481 / 250000000) (17164557 / 40000000) (Real.log (191987 / 125000)) := by
  have h := reflection_log_14386_neg
  have he : Real.log (191987 / 125000) = -Real.log (125000 / 191987) := by
    rw [show ((191987 / 125000) : ℝ) = ((125000 / 191987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14387_neg : (767646613 / 1000000000) ≤ -Real.log (58013 / 125000) ∧
    -Real.log (58013 / 125000) ≤ (153529323 / 200000000) := by
  have h := checkLog_sound (w := (4487 / 120513)) (n := 12)
    (lo := (74499433 / 1000000000)) (hi := (37249717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 58013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 58013) = 1/(58013 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14387 : Bounds (-153529323 / 200000000) (-767646613 / 1000000000) (Real.log (58013 / 125000)) := by
  have h := reflection_log_14387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14388_neg : (43134011 / 100000000) ≤ -Real.log (1000000 / 1539319) ∧
    -Real.log (1000000 / 1539319) ≤ (431340111 / 1000000000) := by
  have h := checkLog_sound (w := (539319 / 2539319)) (n := 12)
    (lo := (43134011 / 100000000)) (hi := (431340111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539319 / 1000000) = 1/(1000000 / 1539319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14388 : Bounds (43134011 / 100000000) (431340111 / 1000000000) (Real.log (1539319 / 1000000)) := by
  have h := reflection_log_14388_neg
  have he : Real.log (1539319 / 1000000) = -Real.log (1000000 / 1539319) := by
    rw [show ((1539319 / 1000000) : ℝ) = ((1000000 / 1539319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14389_neg : (96881181 / 125000000) ≤ -Real.log (460681 / 1000000) ∧
    -Real.log (460681 / 1000000) ≤ (15500989 / 20000000) := by
  have h := checkLog_sound (w := (39319 / 960681)) (n := 12)
    (lo := (20475567 / 250000000)) (hi := (81902269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460681) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 460681) = 1/(460681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14389 : Bounds (-15500989 / 20000000) (-96881181 / 125000000) (Real.log (460681 / 1000000)) := by
  have h := reflection_log_14389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14390_neg : (171854669 / 500000000) ≤ -Real.log (709135016239 / 1000000000000) ∧
    -Real.log (709135016239 / 1000000000000) ≤ (343709339 / 1000000000) := by
  have h := checkLog_sound (w := (290864983761 / 1709135016239)) (n := 12)
    (lo := (171854669 / 500000000)) (hi := (343709339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 709135016239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 709135016239) = 1/(709135016239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14390 : Bounds (-343709339 / 1000000000) (-171854669 / 500000000) (Real.log (709135016239 / 1000000000000)) := by
  have h := reflection_log_14390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14391_neg : (338532689 / 1000000000) ≤ -Real.log (11137741831 / 15625000000) ∧
    -Real.log (11137741831 / 15625000000) ≤ (33853269 / 100000000) := by
  have h := checkLog_sound (w := (4487258169 / 26762741831)) (n := 12)
    (lo := (338532689 / 1000000000)) (hi := (33853269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 11137741831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 11137741831) = 1/(11137741831 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14391 : Bounds (-33853269 / 100000000) (-338532689 / 1000000000) (Real.log (11137741831 / 15625000000)) := by
  have h := reflection_log_14391_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14392_neg : (1196760537 / 1000000000) ≤ -Real.log (250000000000 / 827344733077) ∧
    -Real.log (250000000000 / 827344733077) ≤ (1196760539 / 1000000000) := by
  have h := checkLog_sound (w := (327344733077 / 1327344733077)) (n := 12)
    (lo := (503613357 / 1000000000)) (hi := (251806679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827344733077 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(827344733077 / 500000000000) = 1/(250000000000 / 827344733077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14392 : Bounds (1196760537 / 1000000000) (1196760539 / 1000000000) (Real.log (827344733077 / 250000000000)) := by
  have h := reflection_log_14392_neg
  have he : Real.log (827344733077 / 250000000000) = -Real.log (250000000000 / 827344733077) := by
    rw [show ((827344733077 / 250000000000) : ℝ) = ((250000000000 / 827344733077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14393_neg : (1206389559 / 1000000000) ≤ -Real.log (500000000000 / 1670699464489) ∧
    -Real.log (500000000000 / 1670699464489) ≤ (1206389561 / 1000000000) := by
  have h := checkLog_sound (w := (670699464489 / 2670699464489)) (n := 12)
    (lo := (513242379 / 1000000000)) (hi := (25662119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1670699464489 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1670699464489 / 1000000000000) = 1/(500000000000 / 1670699464489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14393 : Bounds (1206389559 / 1000000000) (1206389561 / 1000000000) (Real.log (1670699464489 / 500000000000)) := by
  have h := reflection_log_14393_neg
  have he : Real.log (1670699464489 / 500000000000) = -Real.log (500000000000 / 1670699464489) := by
    rw [show ((1670699464489 / 500000000000) : ℝ) = ((500000000000 / 1670699464489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14394_neg : (1436544657 / 500000000) ≤ -Real.log (500000000000 / 8845794392523) ∧
    -Real.log (500000000000 / 8845794392523) ≤ (2873089319 / 1000000000) := by
  have h := checkLog_sound (w := (845794392523 / 16845794392523)) (n := 12)
    (lo := (50250297 / 500000000)) (hi := (20100119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8845794392523 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8845794392523 / 8000000000000) = 1/(500000000000 / 8845794392523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14394 : Bounds (1436544657 / 500000000) (2873089319 / 1000000000) (Real.log (8845794392523 / 500000000000)) := by
  have h := reflection_log_14394_neg
  have he : Real.log (8845794392523 / 500000000000) = -Real.log (500000000000 / 8845794392523) := by
    rw [show ((8845794392523 / 500000000000) : ℝ) = ((500000000000 / 8845794392523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14395_neg : (2903110781 / 1000000000) ≤ -Real.log (100000000000 / 1823076923077) ∧
    -Real.log (100000000000 / 1823076923077) ≤ (1451555393 / 500000000) := by
  have h := checkLog_sound (w := (223076923077 / 3423076923077)) (n := 12)
    (lo := (130522061 / 1000000000)) (hi := (65261031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1823076923077 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1823076923077 / 1600000000000) = 1/(100000000000 / 1823076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14395 : Bounds (2903110781 / 1000000000) (1451555393 / 500000000) (Real.log (1823076923077 / 100000000000)) := by
  have h := reflection_log_14395_neg
  have he : Real.log (1823076923077 / 100000000000) = -Real.log (100000000000 / 1823076923077) := by
    rw [show ((1823076923077 / 100000000000) : ℝ) = ((100000000000 / 1823076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14396_neg : (641327431 / 1000000000) ≤ -Real.log (1000 / 1899) ∧
    -Real.log (1000 / 1899) ≤ (80165929 / 125000000) := by
  have h := checkLog_sound (w := (899 / 2899)) (n := 12)
    (lo := (641327431 / 1000000000)) (hi := (80165929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1000) = 1/(1000 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14396 : Bounds (641327431 / 1000000000) (80165929 / 125000000) (Real.log (1899 / 1000)) := by
  have h := reflection_log_14396_neg
  have he : Real.log (1899 / 1000) = -Real.log (1000 / 1899) := by
    rw [show ((1899 / 1000) : ℝ) = ((1000 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14397_neg : (57315869 / 25000000) ≤ -Real.log (101 / 1000) ∧
    -Real.log (101 / 1000) ≤ (573158691 / 250000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 101) = 1/(101 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14397 : Bounds (-573158691 / 250000000) (-57315869 / 25000000) (Real.log (101 / 1000)) := by
  have h := reflection_log_14397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14398_neg : (224649 / 250000000) ≤ -Real.log (1000000 / 1000899) ∧
    -Real.log (1000000 / 1000899) ≤ (898597 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 2000899)) (n := 12)
    (lo := (224649 / 250000000)) (hi := (898597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000899 / 1000000) = 1/(1000000 / 1000899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14398 : Bounds (224649 / 250000000) (898597 / 1000000000) (Real.log (1000899 / 1000000)) := by
  have h := reflection_log_14398_neg
  have he : Real.log (1000899 / 1000000) = -Real.log (1000000 / 1000899) := by
    rw [show ((1000899 / 1000000) : ℝ) = ((1000000 / 1000899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14399_neg : (224851 / 250000000) ≤ -Real.log (999101 / 1000000) ∧
    -Real.log (999101 / 1000000) ≤ (179881 / 200000000) := by
  have h := checkLog_sound (w := (899 / 1999101)) (n := 12)
    (lo := (224851 / 250000000)) (hi := (179881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999101) = 1/(999101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14399 : Bounds (-179881 / 200000000) (-224851 / 250000000) (Real.log (999101 / 1000000)) := by
  have h := reflection_log_14399_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
