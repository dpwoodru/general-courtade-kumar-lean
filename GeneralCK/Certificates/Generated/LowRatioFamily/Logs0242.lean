import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15488_neg : (154281451 / 100000000) ≤ -Real.log (500000000000 / 2338868654063) ∧
    -Real.log (500000000000 / 2338868654063) ≤ (1542814513 / 1000000000) := by
  have h := checkLog_sound (w := (338868654063 / 4338868654063)) (n := 12)
    (lo := (3130403 / 20000000)) (hi := (156520151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2338868654063 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2338868654063 / 2000000000000) = 1/(500000000000 / 2338868654063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15488 : Bounds (154281451 / 100000000) (1542814513 / 1000000000) (Real.log (2338868654063 / 500000000000)) := by
  have h := reflection_log_15488_neg
  have he : Real.log (2338868654063 / 500000000000) = -Real.log (500000000000 / 2338868654063) := by
    rw [show ((2338868654063 / 500000000000) : ℝ) = ((500000000000 / 2338868654063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15489_neg : (773033643 / 500000000) ≤ -Real.log (500000000000 / 2346488855997) ∧
    -Real.log (500000000000 / 2346488855997) ≤ (1546067289 / 1000000000) := by
  have h := checkLog_sound (w := (346488855997 / 4346488855997)) (n := 12)
    (lo := (79886463 / 500000000)) (hi := (159772927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2346488855997 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2346488855997 / 2000000000000) = 1/(500000000000 / 2346488855997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15489 : Bounds (773033643 / 500000000) (1546067289 / 1000000000) (Real.log (2346488855997 / 500000000000)) := by
  have h := reflection_log_15489_neg
  have he : Real.log (2346488855997 / 500000000000) = -Real.log (500000000000 / 2346488855997) := by
    rw [show ((2346488855997 / 500000000000) : ℝ) = ((500000000000 / 2346488855997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15490_neg : (1451534619 / 250000000) ≤ -Real.log (250000000000 / 83083333333333) ∧
    -Real.log (250000000000 / 83083333333333) ≤ (1161227697 / 200000000) := by
  have h := checkLog_sound (w := (19083333333333 / 147083333333333)) (n := 12)
    (lo := (65240259 / 250000000)) (hi := (260961037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83083333333333 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(83083333333333 / 64000000000000) = 1/(250000000000 / 83083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15490 : Bounds (1451534619 / 250000000) (1161227697 / 200000000) (Real.log (83083333333333 / 250000000000)) := by
  have h := reflection_log_15490_neg
  have he : Real.log (83083333333333 / 250000000000) = -Real.log (250000000000 / 83083333333333) := by
    rw [show ((83083333333333 / 250000000000) : ℝ) = ((250000000000 / 83083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15491_neg : (1460035081 / 250000000) ≤ -Real.log (500000000000 / 171913793103449) ∧
    -Real.log (500000000000 / 171913793103449) ≤ (5840140333 / 1000000000) := by
  have h := checkLog_sound (w := (43913793103449 / 299913793103449)) (n := 12)
    (lo := (73740721 / 250000000)) (hi := (58992577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171913793103449 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(171913793103449 / 128000000000000) = 1/(500000000000 / 171913793103449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15491 : Bounds (1460035081 / 250000000) (5840140333 / 1000000000) (Real.log (171913793103449 / 500000000000)) := by
  have h := reflection_log_15491_neg
  have he : Real.log (171913793103449 / 500000000000) = -Real.log (500000000000 / 171913793103449) := by
    rw [show ((171913793103449 / 500000000000) : ℝ) = ((500000000000 / 171913793103449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15492_neg : (690343253 / 1000000000) ≤ -Real.log (1250 / 2493) ∧
    -Real.log (1250 / 2493) ≤ (345171627 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 3743)) (n := 12)
    (lo := (690343253 / 1000000000)) (hi := (345171627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 1250) = 1/(1250 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15492 : Bounds (690343253 / 1000000000) (345171627 / 500000000) (Real.log (2493 / 1250)) := by
  have h := reflection_log_15492_neg
  have he : Real.log (2493 / 1250) = -Real.log (1250 / 2493) := by
    rw [show ((2493 / 1250) : ℝ) = ((1250 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15493_neg : (5184988677 / 1000000000) ≤ -Real.log (7 / 1250) ∧
    -Real.log (7 / 1250) ≤ (1036997737 / 200000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 448) = 1/(7 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15493 : Bounds (-1036997737 / 200000000) (-5184988677 / 1000000000) (Real.log (7 / 1250)) := by
  have h := reflection_log_15493_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15494_neg : (198781 / 200000000) ≤ -Real.log (1250000 / 1251243) ∧
    -Real.log (1250000 / 1251243) ≤ (496953 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 2501243)) (n := 12)
    (lo := (198781 / 200000000)) (hi := (496953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251243 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251243 / 1250000) = 1/(1250000 / 1251243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15494 : Bounds (198781 / 200000000) (496953 / 500000000) (Real.log (1251243 / 1250000)) := by
  have h := reflection_log_15494_neg
  have he : Real.log (1251243 / 1250000) = -Real.log (1250000 / 1251243) := by
    rw [show ((1251243 / 1250000) : ℝ) = ((1250000 / 1251243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15495_neg : (497447 / 500000000) ≤ -Real.log (1248757 / 1250000) ∧
    -Real.log (1248757 / 1250000) ≤ (198979 / 200000000) := by
  have h := checkLog_sound (w := (1243 / 2498757)) (n := 12)
    (lo := (497447 / 500000000)) (hi := (198979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248757) = 1/(1248757 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15495 : Bounds (-198979 / 200000000) (-497447 / 500000000) (Real.log (1248757 / 1250000)) := by
  have h := reflection_log_15495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15496_neg : (31225117 / 62500000) ≤ -Real.log (200000 / 329613) ∧
    -Real.log (200000 / 329613) ≤ (499601873 / 1000000000) := by
  have h := checkLog_sound (w := (129613 / 529613)) (n := 12)
    (lo := (31225117 / 62500000)) (hi := (499601873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329613 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329613 / 200000) = 1/(200000 / 329613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15496 : Bounds (31225117 / 62500000) (499601873 / 1000000000) (Real.log (329613 / 200000)) := by
  have h := reflection_log_15496_neg
  have he : Real.log (329613 / 200000) = -Real.log (200000 / 329613) := by
    rw [show ((329613 / 200000) : ℝ) = ((200000 / 329613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15497_neg : (522154389 / 500000000) ≤ -Real.log (70387 / 200000) ∧
    -Real.log (70387 / 200000) ≤ (52215439 / 50000000) := by
  have h := checkLog_sound (w := (29613 / 170387)) (n := 12)
    (lo := (175580799 / 500000000)) (hi := (351161599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70387) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70387) = 1/(70387 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15497 : Bounds (-52215439 / 50000000) (-522154389 / 500000000) (Real.log (70387 / 200000)) := by
  have h := reflection_log_15497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15498_neg : (500174501 / 1000000000) ≤ -Real.log (1000000 / 1649009) ∧
    -Real.log (1000000 / 1649009) ≤ (250087251 / 500000000) := by
  have h := checkLog_sound (w := (649009 / 2649009)) (n := 12)
    (lo := (500174501 / 1000000000)) (hi := (250087251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649009 / 1000000) = 1/(1000000 / 1649009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15498 : Bounds (500174501 / 1000000000) (250087251 / 500000000) (Real.log (1649009 / 1000000)) := by
  have h := reflection_log_15498_neg
  have he : Real.log (1649009 / 1000000) = -Real.log (1000000 / 1649009) := by
    rw [show ((1649009 / 1000000) : ℝ) = ((1000000 / 1649009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15499_neg : (130874337 / 125000000) ≤ -Real.log (350991 / 1000000) ∧
    -Real.log (350991 / 1000000) ≤ (523497349 / 500000000) := by
  have h := checkLog_sound (w := (149009 / 850991)) (n := 12)
    (lo := (88461879 / 250000000)) (hi := (353847517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350991) = 1/(350991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15499 : Bounds (-523497349 / 500000000) (-130874337 / 125000000) (Real.log (350991 / 1000000)) := by
  have h := reflection_log_15499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15500_neg : (109364039 / 200000000) ≤ -Real.log (578787317919 / 1000000000000) ∧
    -Real.log (578787317919 / 1000000000000) ≤ (136705049 / 250000000) := by
  have h := checkLog_sound (w := (421212682081 / 1578787317919)) (n := 12)
    (lo := (109364039 / 200000000)) (hi := (136705049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 578787317919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 578787317919) = 1/(578787317919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15500 : Bounds (-136705049 / 250000000) (-109364039 / 200000000) (Real.log (578787317919 / 1000000000000)) := by
  have h := reflection_log_15500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15501_neg : (544706907 / 1000000000) ≤ -Real.log (23200470231 / 40000000000) ∧
    -Real.log (23200470231 / 40000000000) ≤ (136176727 / 250000000) := by
  have h := checkLog_sound (w := (16799529769 / 63200470231)) (n := 12)
    (lo := (544706907 / 1000000000)) (hi := (136176727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23200470231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23200470231) = 1/(23200470231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15501 : Bounds (-136176727 / 250000000) (-544706907 / 1000000000) (Real.log (23200470231 / 40000000000)) := by
  have h := reflection_log_15501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15502_neg : (30878213 / 20000000) ≤ -Real.log (500000000000 / 2341433787489) ∧
    -Real.log (500000000000 / 2341433787489) ≤ (1543910653 / 1000000000) := by
  have h := checkLog_sound (w := (341433787489 / 4341433787489)) (n := 12)
    (lo := (15761629 / 100000000)) (hi := (157616291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341433787489 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2341433787489 / 2000000000000) = 1/(500000000000 / 2341433787489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15502 : Bounds (30878213 / 20000000) (1543910653 / 1000000000) (Real.log (2341433787489 / 500000000000)) := by
  have h := reflection_log_15502_neg
  have he : Real.log (2341433787489 / 500000000000) = -Real.log (500000000000 / 2341433787489) := by
    rw [show ((2341433787489 / 500000000000) : ℝ) = ((500000000000 / 2341433787489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15503_neg : (1547169197 / 1000000000) ≤ -Real.log (62500000000 / 293634487779) ∧
    -Real.log (62500000000 / 293634487779) ≤ (3867923 / 2500000) := by
  have h := checkLog_sound (w := (43634487779 / 543634487779)) (n := 12)
    (lo := (160874837 / 1000000000)) (hi := (80437419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293634487779 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(293634487779 / 250000000000) = 1/(62500000000 / 293634487779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15503 : Bounds (1547169197 / 1000000000) (3867923 / 2500000) (Real.log (293634487779 / 62500000000)) := by
  have h := reflection_log_15503_neg
  have he : Real.log (293634487779 / 62500000000) = -Real.log (62500000000 / 293634487779) := by
    rw [show ((293634487779 / 62500000000) : ℝ) = ((62500000000 / 293634487779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15504_neg : (1460035081 / 250000000) ≤ -Real.log (62500000000 / 21489224137931) ∧
    -Real.log (62500000000 / 21489224137931) ≤ (5840140333 / 1000000000) := by
  have h := checkLog_sound (w := (5489224137931 / 37489224137931)) (n := 12)
    (lo := (73740721 / 250000000)) (hi := (58992577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21489224137931 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(21489224137931 / 16000000000000) = 1/(62500000000 / 21489224137931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15504 : Bounds (1460035081 / 250000000) (5840140333 / 1000000000) (Real.log (21489224137931 / 62500000000)) := by
  have h := reflection_log_15504_neg
  have he : Real.log (21489224137931 / 62500000000) = -Real.log (62500000000 / 21489224137931) := by
    rw [show ((21489224137931 / 62500000000) : ℝ) = ((62500000000 / 21489224137931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15505_neg : (5875331929 / 1000000000) ≤ -Real.log (500000000000 / 178071428571429) ∧
    -Real.log (500000000000 / 178071428571429) ≤ (2937665969 / 500000000) := by
  have h := checkLog_sound (w := (50071428571429 / 306071428571429)) (n := 12)
    (lo := (330154489 / 1000000000)) (hi := (33015449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178071428571429 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(178071428571429 / 128000000000000) = 1/(500000000000 / 178071428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15505 : Bounds (5875331929 / 1000000000) (2937665969 / 500000000) (Real.log (178071428571429 / 500000000000)) := by
  have h := reflection_log_15505_neg
  have he : Real.log (178071428571429 / 500000000000) = -Real.log (500000000000 / 178071428571429) := by
    rw [show ((178071428571429 / 500000000000) : ℝ) = ((500000000000 / 178071428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15506_neg : (86305441 / 125000000) ≤ -Real.log (5000 / 9973) ∧
    -Real.log (5000 / 9973) ≤ (690443529 / 1000000000) := by
  have h := checkLog_sound (w := (4973 / 14973)) (n := 12)
    (lo := (86305441 / 125000000)) (hi := (690443529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9973 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9973 / 5000) = 1/(5000 / 9973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15506 : Bounds (86305441 / 125000000) (690443529 / 1000000000) (Real.log (9973 / 5000)) := by
  have h := reflection_log_15506_neg
  have he : Real.log (9973 / 5000) = -Real.log (5000 / 9973) := by
    rw [show ((9973 / 5000) : ℝ) = ((5000 / 9973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15507_neg : (5221356321 / 1000000000) ≤ -Real.log (27 / 5000) ∧
    -Real.log (27 / 5000) ≤ (5221356329 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1057)) (n := 12)
    (lo := (369326061 / 1000000000)) (hi := (184663031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 432) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 432) = 1/(27 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15507 : Bounds (-5221356329 / 1000000000) (-5221356321 / 1000000000) (Real.log (27 / 5000)) := by
  have h := reflection_log_15507_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15508_neg : (198821 / 200000000) ≤ -Real.log (5000000 / 5004973) ∧
    -Real.log (5000000 / 5004973) ≤ (497053 / 500000000) := by
  have h := checkLog_sound (w := (4973 / 10004973)) (n := 12)
    (lo := (198821 / 200000000)) (hi := (497053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004973 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004973 / 5000000) = 1/(5000000 / 5004973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15508 : Bounds (198821 / 200000000) (497053 / 500000000) (Real.log (5004973 / 5000000)) := by
  have h := reflection_log_15508_neg
  have he : Real.log (5004973 / 5000000) = -Real.log (5000000 / 5004973) := by
    rw [show ((5004973 / 5000000) : ℝ) = ((5000000 / 5004973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15509_neg : (497547 / 500000000) ≤ -Real.log (4995027 / 5000000) ∧
    -Real.log (4995027 / 5000000) ≤ (199019 / 200000000) := by
  have h := checkLog_sound (w := (4973 / 9995027)) (n := 12)
    (lo := (497547 / 500000000)) (hi := (199019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995027) = 1/(4995027 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15509 : Bounds (-199019 / 200000000) (-497547 / 500000000) (Real.log (4995027 / 5000000)) := by
  have h := reflection_log_15509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15510_neg : (249897707 / 500000000) ≤ -Real.log (15625 / 25756) ∧
    -Real.log (15625 / 25756) ≤ (99959083 / 200000000) := by
  have h := checkLog_sound (w := (10131 / 41381)) (n := 12)
    (lo := (249897707 / 500000000)) (hi := (99959083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25756 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25756 / 15625) = 1/(15625 / 25756) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15510 : Bounds (249897707 / 500000000) (99959083 / 200000000) (Real.log (25756 / 15625)) := by
  have h := reflection_log_15510_neg
  have he : Real.log (25756 / 15625) = -Real.log (15625 / 25756) := by
    rw [show ((25756 / 15625) : ℝ) = ((15625 / 25756) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15511_neg : (1045215607 / 1000000000) ≤ -Real.log (5494 / 15625) ∧
    -Real.log (5494 / 15625) ≤ (1045215609 / 1000000000) := by
  have h := checkLog_sound (w := (4637 / 26613)) (n := 12)
    (lo := (352068427 / 1000000000)) (hi := (88017107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10988) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 10988) = 1/(5494 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15511 : Bounds (-1045215609 / 1000000000) (-1045215607 / 1000000000) (Real.log (5494 / 15625)) := by
  have h := reflection_log_15511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15512_neg : (62546143 / 125000000) ≤ -Real.log (100000 / 164933) ∧
    -Real.log (100000 / 164933) ≤ (100073829 / 200000000) := by
  have h := checkLog_sound (w := (64933 / 264933)) (n := 12)
    (lo := (62546143 / 125000000)) (hi := (100073829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164933 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164933 / 100000) = 1/(100000 / 164933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15512 : Bounds (62546143 / 125000000) (100073829 / 200000000) (Real.log (164933 / 100000)) := by
  have h := reflection_log_15512_neg
  have he : Real.log (164933 / 100000) = -Real.log (100000 / 164933) := by
    rw [show ((164933 / 100000) : ℝ) = ((100000 / 164933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15513_neg : (261977417 / 250000000) ≤ -Real.log (35067 / 100000) ∧
    -Real.log (35067 / 100000) ≤ (104790967 / 100000000) := by
  have h := checkLog_sound (w := (14933 / 85067)) (n := 12)
    (lo := (44345311 / 125000000)) (hi := (354762489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35067) = 1/(35067 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15513 : Bounds (-104790967 / 100000000) (-261977417 / 250000000) (Real.log (35067 / 100000)) := by
  have h := reflection_log_15513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15514_neg : (547540523 / 1000000000) ≤ -Real.log (5783705511 / 10000000000) ∧
    -Real.log (5783705511 / 10000000000) ≤ (136885131 / 250000000) := by
  have h := checkLog_sound (w := (4216294489 / 15783705511)) (n := 12)
    (lo := (547540523 / 1000000000)) (hi := (136885131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5783705511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5783705511) = 1/(5783705511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15514 : Bounds (-136885131 / 250000000) (-547540523 / 1000000000) (Real.log (5783705511 / 10000000000)) := by
  have h := reflection_log_15514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15515_neg : (545420193 / 1000000000) ≤ -Real.log (141503464 / 244140625) ∧
    -Real.log (141503464 / 244140625) ≤ (272710097 / 500000000) := by
  have h := checkLog_sound (w := (102637161 / 385644089)) (n := 12)
    (lo := (545420193 / 1000000000)) (hi := (272710097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 141503464) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 141503464) = 1/(141503464 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15515 : Bounds (-272710097 / 500000000) (-545420193 / 1000000000) (Real.log (141503464 / 244140625)) := by
  have h := reflection_log_15515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15516_neg : (77250551 / 50000000) ≤ -Real.log (500000000000 / 2344011649071) ∧
    -Real.log (500000000000 / 2344011649071) ≤ (1545011023 / 1000000000) := by
  have h := checkLog_sound (w := (344011649071 / 4344011649071)) (n := 12)
    (lo := (7935833 / 50000000)) (hi := (158716661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2344011649071 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2344011649071 / 2000000000000) = 1/(500000000000 / 2344011649071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15516 : Bounds (77250551 / 50000000) (1545011023 / 1000000000) (Real.log (2344011649071 / 500000000000)) := by
  have h := reflection_log_15516_neg
  have he : Real.log (2344011649071 / 500000000000) = -Real.log (500000000000 / 2344011649071) := by
    rw [show ((2344011649071 / 500000000000) : ℝ) = ((500000000000 / 2344011649071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15517_neg : (387069703 / 250000000) ≤ -Real.log (100000000000 / 470336783871) ∧
    -Real.log (100000000000 / 470336783871) ≤ (309655763 / 200000000) := by
  have h := checkLog_sound (w := (70336783871 / 870336783871)) (n := 12)
    (lo := (40496113 / 250000000)) (hi := (161984453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470336783871 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(470336783871 / 400000000000) = 1/(100000000000 / 470336783871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15517 : Bounds (387069703 / 250000000) (309655763 / 200000000) (Real.log (470336783871 / 100000000000)) := by
  have h := reflection_log_15517_neg
  have he : Real.log (470336783871 / 100000000000) = -Real.log (100000000000 / 470336783871) := by
    rw [show ((470336783871 / 100000000000) : ℝ) = ((100000000000 / 470336783871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15518_neg : (5875331929 / 1000000000) ≤ -Real.log (125000000000 / 44517857142857) ∧
    -Real.log (125000000000 / 44517857142857) ≤ (2937665969 / 500000000) := by
  have h := checkLog_sound (w := (12517857142857 / 76517857142857)) (n := 12)
    (lo := (330154489 / 1000000000)) (hi := (33015449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44517857142857 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(44517857142857 / 32000000000000) = 1/(125000000000 / 44517857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15518 : Bounds (5875331929 / 1000000000) (2937665969 / 500000000) (Real.log (44517857142857 / 125000000000)) := by
  have h := reflection_log_15518_neg
  have he : Real.log (44517857142857 / 125000000000) = -Real.log (125000000000 / 44517857142857) := by
    rw [show ((44517857142857 / 125000000000) : ℝ) = ((125000000000 / 44517857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15519_neg : (5911799849 / 1000000000) ≤ -Real.log (250000000000 / 92342592592593) ∧
    -Real.log (250000000000 / 92342592592593) ≤ (2955899929 / 500000000) := by
  have h := checkLog_sound (w := (28342592592593 / 156342592592593)) (n := 12)
    (lo := (366622409 / 1000000000)) (hi := (36662241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92342592592593 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(92342592592593 / 64000000000000) = 1/(250000000000 / 92342592592593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15519 : Bounds (5911799849 / 1000000000) (2955899929 / 500000000) (Real.log (92342592592593 / 250000000000)) := by
  have h := reflection_log_15519_neg
  have he : Real.log (92342592592593 / 250000000000) = -Real.log (250000000000 / 92342592592593) := by
    rw [show ((92342592592593 / 250000000000) : ℝ) = ((250000000000 / 92342592592593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15520_neg : (345271897 / 500000000) ≤ -Real.log (2500 / 4987) ∧
    -Real.log (2500 / 4987) ≤ (138108759 / 200000000) := by
  have h := checkLog_sound (w := (2487 / 7487)) (n := 12)
    (lo := (345271897 / 500000000)) (hi := (138108759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4987 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4987 / 2500) = 1/(2500 / 4987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15520 : Bounds (345271897 / 500000000) (138108759 / 200000000) (Real.log (4987 / 2500)) := by
  have h := reflection_log_15520_neg
  have he : Real.log (4987 / 2500) = -Real.log (2500 / 4987) := by
    rw [show ((4987 / 2500) : ℝ) = ((2500 / 4987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15521_neg : (5259096649 / 1000000000) ≤ -Real.log (13 / 2500) ∧
    -Real.log (13 / 2500) ≤ (5259096657 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1041)) (n := 12)
    (lo := (407066389 / 1000000000)) (hi := (40706639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 416) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 416) = 1/(13 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15521 : Bounds (-5259096657 / 1000000000) (-5259096649 / 1000000000) (Real.log (13 / 2500)) := by
  have h := reflection_log_15521_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15522_neg : (198861 / 200000000) ≤ -Real.log (2500000 / 2502487) ∧
    -Real.log (2500000 / 2502487) ≤ (497153 / 500000000) := by
  have h := checkLog_sound (w := (2487 / 5002487)) (n := 12)
    (lo := (198861 / 200000000)) (hi := (497153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502487 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502487 / 2500000) = 1/(2500000 / 2502487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15522 : Bounds (198861 / 200000000) (497153 / 500000000) (Real.log (2502487 / 2500000)) := by
  have h := reflection_log_15522_neg
  have he : Real.log (2502487 / 2500000) = -Real.log (2500000 / 2502487) := by
    rw [show ((2502487 / 2500000) : ℝ) = ((2500000 / 2502487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15523_neg : (199059 / 200000000) ≤ -Real.log (2497513 / 2500000) ∧
    -Real.log (2497513 / 2500000) ≤ (31103 / 31250000) := by
  have h := checkLog_sound (w := (2487 / 4997513)) (n := 12)
    (lo := (199059 / 200000000)) (hi := (31103 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497513) = 1/(2497513 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15523 : Bounds (-31103 / 31250000) (-199059 / 200000000) (Real.log (2497513 / 2500000)) := by
  have h := reflection_log_15523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15524_neg : (499990131 / 1000000000) ≤ -Real.log (200000 / 329741) ∧
    -Real.log (200000 / 329741) ≤ (124997533 / 250000000) := by
  have h := checkLog_sound (w := (129741 / 529741)) (n := 12)
    (lo := (499990131 / 1000000000)) (hi := (124997533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329741 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329741 / 200000) = 1/(200000 / 329741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15524 : Bounds (499990131 / 1000000000) (124997533 / 250000000) (Real.log (329741 / 200000)) := by
  have h := reflection_log_15524_neg
  have he : Real.log (329741 / 200000) = -Real.log (200000 / 329741) := by
    rw [show ((329741 / 200000) : ℝ) = ((200000 / 329741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15525_neg : (130766119 / 125000000) ≤ -Real.log (70259 / 200000) ∧
    -Real.log (70259 / 200000) ≤ (523064477 / 500000000) := by
  have h := checkLog_sound (w := (29741 / 170259)) (n := 12)
    (lo := (88245443 / 250000000)) (hi := (352981773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 70259) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 70259) = 1/(70259 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15525 : Bounds (-523064477 / 500000000) (-130766119 / 125000000) (Real.log (70259 / 200000)) := by
  have h := reflection_log_15525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15526_neg : (250282481 / 500000000) ≤ -Real.log (1000000 / 1649653) ∧
    -Real.log (1000000 / 1649653) ≤ (500564963 / 1000000000) := by
  have h := checkLog_sound (w := (649653 / 2649653)) (n := 12)
    (lo := (250282481 / 500000000)) (hi := (500564963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649653 / 1000000) = 1/(1000000 / 1649653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15526 : Bounds (250282481 / 500000000) (500564963 / 1000000000) (Real.log (1649653 / 1000000)) := by
  have h := reflection_log_15526_neg
  have he : Real.log (1649653 / 1000000) = -Real.log (1000000 / 1649653) := by
    rw [show ((1649653 / 1000000) : ℝ) = ((1000000 / 1649653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15527_neg : (524415593 / 500000000) ≤ -Real.log (350347 / 1000000) ∧
    -Real.log (350347 / 1000000) ≤ (262207797 / 250000000) := by
  have h := checkLog_sound (w := (149653 / 850347)) (n := 12)
    (lo := (177842003 / 500000000)) (hi := (355684007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350347) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350347) = 1/(350347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15527 : Bounds (-262207797 / 250000000) (-524415593 / 500000000) (Real.log (350347 / 1000000)) := by
  have h := reflection_log_15527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15528_neg : (34266639 / 62500000) ≤ -Real.log (577950979591 / 1000000000000) ∧
    -Real.log (577950979591 / 1000000000000) ≤ (21930649 / 40000000) := by
  have h := checkLog_sound (w := (422049020409 / 1577950979591)) (n := 12)
    (lo := (34266639 / 62500000)) (hi := (21930649 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577950979591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577950979591) = 1/(577950979591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15528 : Bounds (-21930649 / 40000000) (-34266639 / 62500000) (Real.log (577950979591 / 1000000000000)) := by
  have h := reflection_log_15528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15529_neg : (546138821 / 1000000000) ≤ -Real.log (23167272919 / 40000000000) ∧
    -Real.log (23167272919 / 40000000000) ≤ (273069411 / 500000000) := by
  have h := checkLog_sound (w := (16832727081 / 63167272919)) (n := 12)
    (lo := (546138821 / 1000000000)) (hi := (273069411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23167272919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23167272919) = 1/(23167272919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15529 : Bounds (-273069411 / 500000000) (-546138821 / 1000000000) (Real.log (23167272919 / 40000000000)) := by
  have h := reflection_log_15529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15530_neg : (773059541 / 500000000) ≤ -Real.log (500000000000 / 2346610398667) ∧
    -Real.log (500000000000 / 2346610398667) ≤ (309223817 / 200000000) := by
  have h := checkLog_sound (w := (346610398667 / 4346610398667)) (n := 12)
    (lo := (79912361 / 500000000)) (hi := (159824723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2346610398667 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2346610398667 / 2000000000000) = 1/(500000000000 / 2346610398667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15530 : Bounds (773059541 / 500000000) (309223817 / 200000000) (Real.log (2346610398667 / 500000000000)) := by
  have h := reflection_log_15530_neg
  have he : Real.log (2346610398667 / 500000000000) = -Real.log (500000000000 / 2346610398667) := by
    rw [show ((2346610398667 / 500000000000) : ℝ) = ((500000000000 / 2346610398667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15531_neg : (387349037 / 250000000) ≤ -Real.log (250000000000 / 1177156504837) ∧
    -Real.log (250000000000 / 1177156504837) ≤ (1549396151 / 1000000000) := by
  have h := checkLog_sound (w := (177156504837 / 2177156504837)) (n := 12)
    (lo := (40775447 / 250000000)) (hi := (163101789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177156504837 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1177156504837 / 1000000000000) = 1/(250000000000 / 1177156504837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15531 : Bounds (387349037 / 250000000) (1549396151 / 1000000000) (Real.log (1177156504837 / 250000000000)) := by
  have h := reflection_log_15531_neg
  have he : Real.log (1177156504837 / 250000000000) = -Real.log (250000000000 / 1177156504837) := by
    rw [show ((1177156504837 / 250000000000) : ℝ) = ((250000000000 / 1177156504837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15532_neg : (5911799849 / 1000000000) ≤ -Real.log (100000000000 / 36937037037037) ∧
    -Real.log (100000000000 / 36937037037037) ≤ (2955899929 / 500000000) := by
  have h := checkLog_sound (w := (11337037037037 / 62537037037037)) (n := 12)
    (lo := (366622409 / 1000000000)) (hi := (36662241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36937037037037 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(36937037037037 / 25600000000000) = 1/(100000000000 / 36937037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15532 : Bounds (5911799849 / 1000000000) (2955899929 / 500000000) (Real.log (36937037037037 / 100000000000)) := by
  have h := reflection_log_15532_neg
  have he : Real.log (36937037037037 / 100000000000) = -Real.log (100000000000 / 36937037037037) := by
    rw [show ((36937037037037 / 100000000000) : ℝ) = ((100000000000 / 36937037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15533_neg : (5949640443 / 1000000000) ≤ -Real.log (500000000000 / 191807692307693) ∧
    -Real.log (500000000000 / 191807692307693) ≤ (1487410113 / 250000000) := by
  have h := checkLog_sound (w := (63807692307693 / 319807692307693)) (n := 12)
    (lo := (404463003 / 1000000000)) (hi := (101115751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191807692307693 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(191807692307693 / 128000000000000) = 1/(500000000000 / 191807692307693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15533 : Bounds (5949640443 / 1000000000) (1487410113 / 250000000) (Real.log (191807692307693 / 500000000000)) := by
  have h := reflection_log_15533_neg
  have he : Real.log (191807692307693 / 500000000000) = -Real.log (500000000000 / 191807692307693) := by
    rw [show ((191807692307693 / 500000000000) : ℝ) = ((500000000000 / 191807692307693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15534_neg : (13812881 / 20000000) ≤ -Real.log (200 / 399) ∧
    -Real.log (200 / 399) ≤ (690644051 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 599)) (n := 12)
    (lo := (13812881 / 20000000)) (hi := (690644051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 200) = 1/(200 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15534 : Bounds (13812881 / 20000000) (690644051 / 1000000000) (Real.log (399 / 200)) := by
  have h := reflection_log_15534_neg
  have he : Real.log (399 / 200) = -Real.log (200 / 399) := by
    rw [show ((399 / 200) : ℝ) = ((200 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15535_neg : (2649158681 / 500000000) ≤ -Real.log (1 / 200) ∧
    -Real.log (1 / 200) ≤ (529831737 / 100000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(25 / 16) = 1/(1 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15535 : Bounds (-529831737 / 100000000) (-2649158681 / 500000000) (Real.log (1 / 200)) := by
  have h := reflection_log_15535_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15536_neg : (198901 / 200000000) ≤ -Real.log (200000 / 200199) ∧
    -Real.log (200000 / 200199) ≤ (497253 / 500000000) := by
  have h := checkLog_sound (w := (199 / 400199)) (n := 12)
    (lo := (198901 / 200000000)) (hi := (497253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200199 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200199 / 200000) = 1/(200000 / 200199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15536 : Bounds (198901 / 200000000) (497253 / 500000000) (Real.log (200199 / 200000)) := by
  have h := reflection_log_15536_neg
  have he : Real.log (200199 / 200000) = -Real.log (200000 / 200199) := by
    rw [show ((200199 / 200000) : ℝ) = ((200000 / 200199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15537_neg : (199099 / 200000000) ≤ -Real.log (199801 / 200000) ∧
    -Real.log (199801 / 200000) ≤ (124437 / 125000000) := by
  have h := checkLog_sound (w := (199 / 399801)) (n := 12)
    (lo := (199099 / 200000000)) (hi := (124437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199801) = 1/(199801 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15537 : Bounds (-124437 / 125000000) (-199099 / 200000000) (Real.log (199801 / 200000)) := by
  have h := reflection_log_15537_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15538_neg : (500186023 / 1000000000) ≤ -Real.log (250000 / 412257) ∧
    -Real.log (250000 / 412257) ≤ (62523253 / 125000000) := by
  have h := checkLog_sound (w := (162257 / 662257)) (n := 12)
    (lo := (500186023 / 1000000000)) (hi := (62523253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412257 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412257 / 250000) = 1/(250000 / 412257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15538 : Bounds (500186023 / 1000000000) (62523253 / 125000000) (Real.log (412257 / 250000)) := by
  have h := reflection_log_15538_neg
  have he : Real.log (412257 / 250000) = -Real.log (250000 / 412257) := by
    rw [show ((412257 / 250000) : ℝ) = ((250000 / 412257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15539_neg : (104704883 / 100000000) ≤ -Real.log (87743 / 250000) ∧
    -Real.log (87743 / 250000) ≤ (8180069 / 7812500) := by
  have h := checkLog_sound (w := (37257 / 212743)) (n := 12)
    (lo := (7078033 / 20000000)) (hi := (353901651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 87743) = 1/(87743 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15539 : Bounds (-8180069 / 7812500) (-104704883 / 100000000) (Real.log (87743 / 250000)) := by
  have h := reflection_log_15539_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15540_neg : (125190337 / 250000000) ≤ -Real.log (1000000 / 1649977) ∧
    -Real.log (1000000 / 1649977) ≤ (500761349 / 1000000000) := by
  have h := checkLog_sound (w := (649977 / 2649977)) (n := 12)
    (lo := (125190337 / 250000000)) (hi := (500761349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1649977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1649977 / 1000000) = 1/(1000000 / 1649977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15540 : Bounds (125190337 / 250000000) (500761349 / 1000000000) (Real.log (1649977 / 1000000)) := by
  have h := reflection_log_15540_neg
  have he : Real.log (1649977 / 1000000) = -Real.log (1000000 / 1649977) := by
    rw [show ((1649977 / 1000000) : ℝ) = ((1000000 / 1649977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15541_neg : (1049756411 / 1000000000) ≤ -Real.log (350023 / 1000000) ∧
    -Real.log (350023 / 1000000) ≤ (1049756413 / 1000000000) := by
  have h := checkLog_sound (w := (149977 / 850023)) (n := 12)
    (lo := (356609231 / 1000000000)) (hi := (22288077 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 350023) = 1/(350023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15541 : Bounds (-1049756413 / 1000000000) (-1049756411 / 1000000000) (Real.log (350023 / 1000000)) := by
  have h := reflection_log_15541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15542_neg : (548995063 / 1000000000) ≤ -Real.log (577529899471 / 1000000000000) ∧
    -Real.log (577529899471 / 1000000000000) ≤ (68624383 / 125000000) := by
  have h := checkLog_sound (w := (422470100529 / 1577529899471)) (n := 12)
    (lo := (548995063 / 1000000000)) (hi := (68624383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 577529899471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 577529899471) = 1/(577529899471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15542 : Bounds (-68624383 / 125000000) (-548995063 / 1000000000) (Real.log (577529899471 / 1000000000000)) := by
  have h := reflection_log_15542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15543_neg : (546862807 / 1000000000) ≤ -Real.log (36172665951 / 62500000000) ∧
    -Real.log (36172665951 / 62500000000) ≤ (68357851 / 125000000) := by
  have h := checkLog_sound (w := (26327334049 / 98672665951)) (n := 12)
    (lo := (546862807 / 1000000000)) (hi := (68357851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36172665951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36172665951) = 1/(36172665951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15543 : Bounds (-68357851 / 125000000) (-546862807 / 1000000000) (Real.log (36172665951 / 62500000000)) := by
  have h := reflection_log_15543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15544_neg : (1547234853 / 1000000000) ≤ -Real.log (15625000000 / 73413441813) ∧
    -Real.log (15625000000 / 73413441813) ≤ (193404357 / 125000000) := by
  have h := checkLog_sound (w := (10913441813 / 135913441813)) (n := 12)
    (lo := (160940493 / 1000000000)) (hi := (80470247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73413441813 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(73413441813 / 62500000000) = 1/(15625000000 / 73413441813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15544 : Bounds (1547234853 / 1000000000) (193404357 / 125000000) (Real.log (73413441813 / 15625000000)) := by
  have h := reflection_log_15544_neg
  have he : Real.log (73413441813 / 15625000000) = -Real.log (15625000000 / 73413441813) := by
    rw [show ((73413441813 / 15625000000) : ℝ) = ((15625000000 / 73413441813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15545_neg : (1550517759 / 1000000000) ≤ -Real.log (500000000000 / 2356955114379) ∧
    -Real.log (500000000000 / 2356955114379) ≤ (775258881 / 500000000) := by
  have h := checkLog_sound (w := (356955114379 / 4356955114379)) (n := 12)
    (lo := (164223399 / 1000000000)) (hi := (821117 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2356955114379 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2356955114379 / 2000000000000) = 1/(500000000000 / 2356955114379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15545 : Bounds (1550517759 / 1000000000) (775258881 / 500000000) (Real.log (2356955114379 / 500000000000)) := by
  have h := reflection_log_15545_neg
  have he : Real.log (2356955114379 / 500000000000) = -Real.log (500000000000 / 2356955114379) := by
    rw [show ((2356955114379 / 500000000000) : ℝ) = ((500000000000 / 2356955114379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15546_neg : (5949640443 / 1000000000) ≤ -Real.log (125000000000 / 47951923076923) ∧
    -Real.log (125000000000 / 47951923076923) ≤ (1487410113 / 250000000) := by
  have h := checkLog_sound (w := (15951923076923 / 79951923076923)) (n := 12)
    (lo := (404463003 / 1000000000)) (hi := (101115751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47951923076923 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(47951923076923 / 32000000000000) = 1/(125000000000 / 47951923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15546 : Bounds (5949640443 / 1000000000) (1487410113 / 250000000) (Real.log (47951923076923 / 125000000000)) := by
  have h := reflection_log_15546_neg
  have he : Real.log (47951923076923 / 125000000000) = -Real.log (125000000000 / 47951923076923) := by
    rw [show ((47951923076923 / 125000000000) : ℝ) = ((125000000000 / 47951923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15547_neg : (1497240353 / 250000000) ≤ -Real.log (1 / 399) ∧
    -Real.log (1 / 399) ≤ (5988961421 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 655)) (n := 12)
    (lo := (110945993 / 250000000)) (hi := (443783973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 256) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(399 / 256) = 1/(1 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15547 : Bounds (1497240353 / 250000000) (5988961421 / 1000000000) (Real.log (399 / 1)) := by
  have h := reflection_log_15547_neg
  have he : Real.log (399 / 1) = -Real.log (1 / 399) := by
    rw [show ((399 / 1) : ℝ) = ((1 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15548_neg : (138148859 / 200000000) ≤ -Real.log (625 / 1247) ∧
    -Real.log (625 / 1247) ≤ (86343037 / 125000000) := by
  have h := checkLog_sound (w := (311 / 936)) (n := 12)
    (lo := (138148859 / 200000000)) (hi := (86343037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 625) = 1/(625 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15548 : Bounds (138148859 / 200000000) (86343037 / 125000000) (Real.log (1247 / 625)) := by
  have h := reflection_log_15548_neg
  have he : Real.log (1247 / 625) = -Real.log (625 / 1247) := by
    rw [show ((1247 / 625) : ℝ) = ((625 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15549_neg : (5339139357 / 1000000000) ≤ -Real.log (3 / 625) ∧
    -Real.log (3 / 625) ≤ (1067827873 / 200000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 384) = 1/(3 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15549 : Bounds (-1067827873 / 200000000) (-5339139357 / 1000000000) (Real.log (3 / 625)) := by
  have h := reflection_log_15549_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15550_neg : (198941 / 200000000) ≤ -Real.log (312500 / 312811) ∧
    -Real.log (312500 / 312811) ≤ (497353 / 500000000) := by
  have h := checkLog_sound (w := (311 / 625311)) (n := 12)
    (lo := (198941 / 200000000)) (hi := (497353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312811 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312811 / 312500) = 1/(312500 / 312811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15550 : Bounds (198941 / 200000000) (497353 / 500000000) (Real.log (312811 / 312500)) := by
  have h := reflection_log_15550_neg
  have he : Real.log (312811 / 312500) = -Real.log (312500 / 312811) := by
    rw [show ((312811 / 312500) : ℝ) = ((312500 / 312811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15551_neg : (199139 / 200000000) ≤ -Real.log (312189 / 312500) ∧
    -Real.log (312189 / 312500) ≤ (62231 / 62500000) := by
  have h := checkLog_sound (w := (311 / 624689)) (n := 12)
    (lo := (199139 / 200000000)) (hi := (62231 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312189) = 1/(312189 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15551 : Bounds (-62231 / 62500000) (-199139 / 200000000) (Real.log (312189 / 312500)) := by
  have h := reflection_log_15551_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
