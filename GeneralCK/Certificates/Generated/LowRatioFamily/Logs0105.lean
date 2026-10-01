import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6720_neg : (4957 / 25000000) ≤ -Real.log (10000000 / 10001983) ∧
    -Real.log (10000000 / 10001983) ≤ (198281 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 20001983)) (n := 12)
    (lo := (4957 / 25000000)) (hi := (198281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001983 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001983 / 10000000) = 1/(10000000 / 10001983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6720 : Bounds (4957 / 25000000) (198281 / 1000000000) (Real.log (10001983 / 10000000)) := by
  have h := reflection_log_6720_neg
  have he : Real.log (10001983 / 10000000) = -Real.log (10000000 / 10001983) := by
    rw [show ((10001983 / 10000000) : ℝ) = ((10000000 / 10001983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6721_neg : (198319 / 1000000000) ≤ -Real.log (9998017 / 10000000) ∧
    -Real.log (9998017 / 10000000) ≤ (2479 / 12500000) := by
  have h := checkLog_sound (w := (1983 / 19998017)) (n := 12)
    (lo := (198319 / 1000000000)) (hi := (2479 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998017) = 1/(9998017 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6721 : Bounds (-2479 / 12500000) (-198319 / 1000000000) (Real.log (9998017 / 10000000)) := by
  have h := reflection_log_6721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6722_neg : (47523709 / 500000000) ≤ -Real.log (1000000 / 1099711) ∧
    -Real.log (1000000 / 1099711) ≤ (95047419 / 1000000000) := by
  have h := checkLog_sound (w := (99711 / 2099711)) (n := 12)
    (lo := (47523709 / 500000000)) (hi := (95047419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099711 / 1000000) = 1/(1000000 / 1099711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6722 : Bounds (47523709 / 500000000) (95047419 / 1000000000) (Real.log (1099711 / 1000000)) := by
  have h := reflection_log_6722_neg
  have he : Real.log (1099711 / 1000000) = -Real.log (1000000 / 1099711) := by
    rw [show ((1099711 / 1000000) : ℝ) = ((1000000 / 1099711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6723_neg : (3282483 / 31250000) ≤ -Real.log (900289 / 1000000) ∧
    -Real.log (900289 / 1000000) ≤ (105039457 / 1000000000) := by
  have h := checkLog_sound (w := (99711 / 1900289)) (n := 12)
    (lo := (3282483 / 31250000)) (hi := (105039457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900289) = 1/(900289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6723 : Bounds (-105039457 / 1000000000) (-3282483 / 31250000) (Real.log (900289 / 1000000)) := by
  have h := reflection_log_6723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6724_neg : (19054763 / 200000000) ≤ -Real.log (25000 / 27499) ∧
    -Real.log (25000 / 27499) ≤ (11909227 / 125000000) := by
  have h := checkLog_sound (w := (2499 / 52499)) (n := 12)
    (lo := (19054763 / 200000000)) (hi := (11909227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27499 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27499 / 25000) = 1/(25000 / 27499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6724 : Bounds (19054763 / 200000000) (11909227 / 125000000) (Real.log (27499 / 25000)) := by
  have h := reflection_log_6724_neg
  have he : Real.log (27499 / 25000) = -Real.log (25000 / 27499) := by
    rw [show ((27499 / 25000) : ℝ) = ((25000 / 27499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6725_neg : (13164509 / 125000000) ≤ -Real.log (22501 / 25000) ∧
    -Real.log (22501 / 25000) ≤ (105316073 / 1000000000) := by
  have h := checkLog_sound (w := (2499 / 47501)) (n := 12)
    (lo := (13164509 / 125000000)) (hi := (105316073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22501) = 1/(22501 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6725 : Bounds (-105316073 / 1000000000) (-13164509 / 125000000) (Real.log (22501 / 25000)) := by
  have h := reflection_log_6725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6726_neg : (627641 / 62500000) ≤ -Real.log (618754999 / 625000000) ∧
    -Real.log (618754999 / 625000000) ≤ (10042257 / 1000000000) := by
  have h := checkLog_sound (w := (6245001 / 1243754999)) (n := 12)
    (lo := (627641 / 62500000)) (hi := (10042257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618754999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618754999) = 1/(618754999 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6726 : Bounds (-10042257 / 1000000000) (-627641 / 62500000) (Real.log (618754999 / 625000000)) := by
  have h := reflection_log_6726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6727_neg : (4996019 / 500000000) ≤ -Real.log (990057716479 / 1000000000000) ∧
    -Real.log (990057716479 / 1000000000000) ≤ (9992039 / 1000000000) := by
  have h := checkLog_sound (w := (9942283521 / 1990057716479)) (n := 12)
    (lo := (4996019 / 500000000)) (hi := (9992039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990057716479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990057716479) = 1/(990057716479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6727 : Bounds (-9992039 / 1000000000) (-4996019 / 500000000) (Real.log (990057716479 / 1000000000000)) := by
  have h := reflection_log_6727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6728_neg : (100043437 / 500000000) ≤ -Real.log (1562500000 / 1908607611) ∧
    -Real.log (1562500000 / 1908607611) ≤ (320139 / 1600000) := by
  have h := checkLog_sound (w := (346107611 / 3471107611)) (n := 12)
    (lo := (100043437 / 500000000)) (hi := (320139 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1908607611 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1908607611 / 1562500000) = 1/(1562500000 / 1908607611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6728 : Bounds (100043437 / 500000000) (320139 / 1600000) (Real.log (1908607611 / 1562500000)) := by
  have h := reflection_log_6728_neg
  have he : Real.log (1908607611 / 1562500000) = -Real.log (1562500000 / 1908607611) := by
    rw [show ((1908607611 / 1562500000) : ℝ) = ((1562500000 / 1908607611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6729_neg : (200589887 / 1000000000) ≤ -Real.log (50000000000 / 61106173059) ∧
    -Real.log (50000000000 / 61106173059) ≤ (3134217 / 15625000) := by
  have h := checkLog_sound (w := (11106173059 / 111106173059)) (n := 12)
    (lo := (200589887 / 1000000000)) (hi := (3134217 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61106173059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61106173059 / 50000000000) = 1/(50000000000 / 61106173059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6729 : Bounds (200589887 / 1000000000) (3134217 / 15625000) (Real.log (61106173059 / 50000000000)) := by
  have h := reflection_log_6729_neg
  have he : Real.log (61106173059 / 50000000000) = -Real.log (50000000000 / 61106173059) := by
    rw [show ((61106173059 / 50000000000) : ℝ) = ((50000000000 / 61106173059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6730_neg : (401716509 / 1000000000) ≤ -Real.log (250000000000 / 373596906959) ∧
    -Real.log (250000000000 / 373596906959) ≤ (40171651 / 100000000) := by
  have h := checkLog_sound (w := (123596906959 / 623596906959)) (n := 12)
    (lo := (401716509 / 1000000000)) (hi := (40171651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373596906959 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373596906959 / 250000000000) = 1/(250000000000 / 373596906959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6730 : Bounds (401716509 / 1000000000) (40171651 / 100000000) (Real.log (373596906959 / 250000000000)) := by
  have h := reflection_log_6730_neg
  have he : Real.log (373596906959 / 250000000000) = -Real.log (250000000000 / 373596906959) := by
    rw [show ((373596906959 / 250000000000) : ℝ) = ((250000000000 / 373596906959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6731_neg : (401924691 / 1000000000) ≤ -Real.log (500000000000 / 747349382563) ∧
    -Real.log (500000000000 / 747349382563) ≤ (100481173 / 250000000) := by
  have h := checkLog_sound (w := (247349382563 / 1247349382563)) (n := 12)
    (lo := (401924691 / 1000000000)) (hi := (100481173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747349382563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747349382563 / 500000000000) = 1/(500000000000 / 747349382563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6731 : Bounds (401924691 / 1000000000) (100481173 / 250000000) (Real.log (747349382563 / 500000000000)) := by
  have h := reflection_log_6731_neg
  have he : Real.log (747349382563 / 500000000000) = -Real.log (500000000000 / 747349382563) := by
    rw [show ((747349382563 / 500000000000) : ℝ) = ((500000000000 / 747349382563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6732_neg : (180987333 / 1000000000) ≤ -Real.log (625 / 749) ∧
    -Real.log (625 / 749) ≤ (90493667 / 500000000) := by
  have h := checkLog_sound (w := (62 / 687)) (n := 12)
    (lo := (180987333 / 1000000000)) (hi := (90493667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749 / 625) = 1/(625 / 749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6732 : Bounds (180987333 / 1000000000) (90493667 / 500000000) (Real.log (749 / 625)) := by
  have h := reflection_log_6732_neg
  have he : Real.log (749 / 625) = -Real.log (625 / 749) := by
    rw [show ((749 / 625) : ℝ) = ((625 / 749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6733_neg : (55286387 / 250000000) ≤ -Real.log (501 / 625) ∧
    -Real.log (501 / 625) ≤ (221145549 / 1000000000) := by
  have h := checkLog_sound (w := (62 / 563)) (n := 12)
    (lo := (55286387 / 250000000)) (hi := (221145549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 501) = 1/(501 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6733 : Bounds (-221145549 / 1000000000) (-55286387 / 250000000) (Real.log (501 / 625)) := by
  have h := reflection_log_6733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6734_neg : (9919 / 50000000) ≤ -Real.log (156250 / 156281) ∧
    -Real.log (156250 / 156281) ≤ (198381 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 312531)) (n := 12)
    (lo := (9919 / 50000000)) (hi := (198381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156281 / 156250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156281 / 156250) = 1/(156250 / 156281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6734 : Bounds (9919 / 50000000) (198381 / 1000000000) (Real.log (156281 / 156250)) := by
  have h := reflection_log_6734_neg
  have he : Real.log (156281 / 156250) = -Real.log (156250 / 156281) := by
    rw [show ((156281 / 156250) : ℝ) = ((156250 / 156281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6735_neg : (198419 / 1000000000) ≤ -Real.log (156219 / 156250) ∧
    -Real.log (156219 / 156250) ≤ (9921 / 50000000) := by
  have h := checkLog_sound (w := (31 / 312469)) (n := 12)
    (lo := (198419 / 1000000000)) (hi := (9921 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250 / 156219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250 / 156219) = 1/(156219 / 156250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6735 : Bounds (-9921 / 50000000) (-198419 / 1000000000) (Real.log (156219 / 156250)) := by
  have h := reflection_log_6735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6736_neg : (2971681 / 31250000) ≤ -Real.log (500000 / 549881) ∧
    -Real.log (500000 / 549881) ≤ (95093793 / 1000000000) := by
  have h := checkLog_sound (w := (49881 / 1049881)) (n := 12)
    (lo := (2971681 / 31250000)) (hi := (95093793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549881 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549881 / 500000) = 1/(500000 / 549881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6736 : Bounds (2971681 / 31250000) (95093793 / 1000000000) (Real.log (549881 / 500000)) := by
  have h := reflection_log_6736_neg
  have he : Real.log (549881 / 500000) = -Real.log (500000 / 549881) := by
    rw [show ((549881 / 500000) : ℝ) = ((500000 / 549881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6737_neg : (52548053 / 500000000) ≤ -Real.log (450119 / 500000) ∧
    -Real.log (450119 / 500000) ≤ (105096107 / 1000000000) := by
  have h := checkLog_sound (w := (49881 / 950119)) (n := 12)
    (lo := (52548053 / 500000000)) (hi := (105096107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450119) = 1/(450119 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6737 : Bounds (-105096107 / 1000000000) (-52548053 / 500000000) (Real.log (450119 / 500000)) := by
  have h := reflection_log_6737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6738_neg : (95320179 / 1000000000) ≤ -Real.log (1000000 / 1100011) ∧
    -Real.log (1000000 / 1100011) ≤ (4766009 / 50000000) := by
  have h := checkLog_sound (w := (100011 / 2100011)) (n := 12)
    (lo := (95320179 / 1000000000)) (hi := (4766009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100011 / 1000000) = 1/(1000000 / 1100011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6738 : Bounds (95320179 / 1000000000) (4766009 / 50000000) (Real.log (1100011 / 1000000)) := by
  have h := reflection_log_6738_neg
  have he : Real.log (1100011 / 1000000) = -Real.log (1000000 / 1100011) := by
    rw [show ((1100011 / 1000000) : ℝ) = ((1000000 / 1100011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6739_neg : (105372737 / 1000000000) ≤ -Real.log (899989 / 1000000) ∧
    -Real.log (899989 / 1000000) ≤ (52686369 / 500000000) := by
  have h := checkLog_sound (w := (100011 / 1899989)) (n := 12)
    (lo := (105372737 / 1000000000)) (hi := (52686369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899989) = 1/(899989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6739 : Bounds (-52686369 / 500000000) (-105372737 / 1000000000) (Real.log (899989 / 1000000)) := by
  have h := reflection_log_6739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6740_neg : (5026279 / 500000000) ≤ -Real.log (989997799879 / 1000000000000) ∧
    -Real.log (989997799879 / 1000000000000) ≤ (10052559 / 1000000000) := by
  have h := checkLog_sound (w := (10002200121 / 1989997799879)) (n := 12)
    (lo := (5026279 / 500000000)) (hi := (10052559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989997799879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989997799879) = 1/(989997799879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6740 : Bounds (-10052559 / 1000000000) (-5026279 / 500000000) (Real.log (989997799879 / 1000000000000)) := by
  have h := reflection_log_6740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6741_neg : (10002313 / 1000000000) ≤ -Real.log (247511885839 / 250000000000) ∧
    -Real.log (247511885839 / 250000000000) ≤ (5001157 / 500000000) := by
  have h := checkLog_sound (w := (2488114161 / 497511885839)) (n := 12)
    (lo := (10002313 / 1000000000)) (hi := (5001157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247511885839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247511885839) = 1/(247511885839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6741 : Bounds (-5001157 / 500000000) (-10002313 / 1000000000) (Real.log (247511885839 / 250000000000)) := by
  have h := reflection_log_6741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6742_neg : (100094949 / 500000000) ≤ -Real.log (500000000000 / 610817361631) ∧
    -Real.log (500000000000 / 610817361631) ≤ (200189899 / 1000000000) := by
  have h := checkLog_sound (w := (110817361631 / 1110817361631)) (n := 12)
    (lo := (100094949 / 500000000)) (hi := (200189899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610817361631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610817361631 / 500000000000) = 1/(500000000000 / 610817361631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6742 : Bounds (100094949 / 500000000) (200189899 / 1000000000) (Real.log (610817361631 / 500000000000)) := by
  have h := reflection_log_6742_neg
  have he : Real.log (610817361631 / 500000000000) = -Real.log (500000000000 / 610817361631) := by
    rw [show ((610817361631 / 500000000000) : ℝ) = ((500000000000 / 610817361631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6743_neg : (200692917 / 1000000000) ≤ -Real.log (20000000000 / 24444987661) ∧
    -Real.log (20000000000 / 24444987661) ≤ (100346459 / 500000000) := by
  have h := checkLog_sound (w := (4444987661 / 44444987661)) (n := 12)
    (lo := (200692917 / 1000000000)) (hi := (100346459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24444987661 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24444987661 / 20000000000) = 1/(20000000000 / 24444987661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6743 : Bounds (200692917 / 1000000000) (100346459 / 500000000) (Real.log (24444987661 / 20000000000)) := by
  have h := reflection_log_6743_neg
  have he : Real.log (24444987661 / 20000000000) = -Real.log (20000000000 / 24444987661) := by
    rw [show ((24444987661 / 20000000000) : ℝ) = ((20000000000 / 24444987661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6744_neg : (401924691 / 1000000000) ≤ -Real.log (250000000000 / 373674691281) ∧
    -Real.log (250000000000 / 373674691281) ≤ (100481173 / 250000000) := by
  have h := checkLog_sound (w := (123674691281 / 623674691281)) (n := 12)
    (lo := (401924691 / 1000000000)) (hi := (100481173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373674691281 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373674691281 / 250000000000) = 1/(250000000000 / 373674691281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6744 : Bounds (401924691 / 1000000000) (100481173 / 250000000) (Real.log (373674691281 / 250000000000)) := by
  have h := reflection_log_6744_neg
  have he : Real.log (373674691281 / 250000000000) = -Real.log (250000000000 / 373674691281) := by
    rw [show ((373674691281 / 250000000000) : ℝ) = ((250000000000 / 373674691281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6745_neg : (201066441 / 500000000) ≤ -Real.log (25000000000 / 37375249501) ∧
    -Real.log (25000000000 / 37375249501) ≤ (402132883 / 1000000000) := by
  have h := checkLog_sound (w := (12375249501 / 62375249501)) (n := 12)
    (lo := (201066441 / 500000000)) (hi := (402132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37375249501 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37375249501 / 25000000000) = 1/(25000000000 / 37375249501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6745 : Bounds (201066441 / 500000000) (402132883 / 1000000000) (Real.log (37375249501 / 25000000000)) := by
  have h := reflection_log_6745_neg
  have he : Real.log (37375249501 / 25000000000) = -Real.log (25000000000 / 37375249501) := by
    rw [show ((37375249501 / 25000000000) : ℝ) = ((25000000000 / 37375249501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6746_neg : (90535387 / 500000000) ≤ -Real.log (2000 / 2397) ∧
    -Real.log (2000 / 2397) ≤ (7242831 / 40000000) := by
  have h := checkLog_sound (w := (397 / 4397)) (n := 12)
    (lo := (90535387 / 500000000)) (hi := (7242831 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2397 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2397 / 2000) = 1/(2000 / 2397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6746 : Bounds (90535387 / 500000000) (7242831 / 40000000) (Real.log (2397 / 2000)) := by
  have h := reflection_log_6746_neg
  have he : Real.log (2397 / 2000) = -Real.log (2000 / 2397) := by
    rw [show ((2397 / 2000) : ℝ) = ((2000 / 2397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6747_neg : (110635153 / 500000000) ≤ -Real.log (1603 / 2000) ∧
    -Real.log (1603 / 2000) ≤ (221270307 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 3603)) (n := 12)
    (lo := (110635153 / 500000000)) (hi := (221270307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1603) = 1/(1603 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6747 : Bounds (-221270307 / 1000000000) (-110635153 / 500000000) (Real.log (1603 / 2000)) := by
  have h := reflection_log_6747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6748_neg : (2481 / 12500000) ≤ -Real.log (2000000 / 2000397) ∧
    -Real.log (2000000 / 2000397) ≤ (198481 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 4000397)) (n := 12)
    (lo := (2481 / 12500000)) (hi := (198481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000397 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000397 / 2000000) = 1/(2000000 / 2000397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6748 : Bounds (2481 / 12500000) (198481 / 1000000000) (Real.log (2000397 / 2000000)) := by
  have h := reflection_log_6748_neg
  have he : Real.log (2000397 / 2000000) = -Real.log (2000000 / 2000397) := by
    rw [show ((2000397 / 2000000) : ℝ) = ((2000000 / 2000397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6749_neg : (198519 / 1000000000) ≤ -Real.log (1999603 / 2000000) ∧
    -Real.log (1999603 / 2000000) ≤ (4963 / 25000000) := by
  have h := checkLog_sound (w := (397 / 3999603)) (n := 12)
    (lo := (198519 / 1000000000)) (hi := (4963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999603) = 1/(1999603 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6749 : Bounds (-4963 / 25000000) (-198519 / 1000000000) (Real.log (1999603 / 2000000)) := by
  have h := reflection_log_6749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6750_neg : (19028033 / 200000000) ≤ -Real.log (1000000 / 1099813) ∧
    -Real.log (1000000 / 1099813) ≤ (47570083 / 500000000) := by
  have h := checkLog_sound (w := (99813 / 2099813)) (n := 12)
    (lo := (19028033 / 200000000)) (hi := (47570083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099813 / 1000000) = 1/(1000000 / 1099813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6750 : Bounds (19028033 / 200000000) (47570083 / 500000000) (Real.log (1099813 / 1000000)) := by
  have h := reflection_log_6750_neg
  have he : Real.log (1099813 / 1000000) = -Real.log (1000000 / 1099813) := by
    rw [show ((1099813 / 1000000) : ℝ) = ((1000000 / 1099813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6751_neg : (105152759 / 1000000000) ≤ -Real.log (900187 / 1000000) ∧
    -Real.log (900187 / 1000000) ≤ (2628819 / 25000000) := by
  have h := checkLog_sound (w := (99813 / 1900187)) (n := 12)
    (lo := (105152759 / 1000000000)) (hi := (2628819 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900187) = 1/(900187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6751 : Bounds (-2628819 / 25000000) (-105152759 / 1000000000) (Real.log (900187 / 1000000)) := by
  have h := reflection_log_6751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6752_neg : (1907349 / 20000000) ≤ -Real.log (1000000 / 1100063) ∧
    -Real.log (1000000 / 1100063) ≤ (95367451 / 1000000000) := by
  have h := checkLog_sound (w := (100063 / 2100063)) (n := 12)
    (lo := (1907349 / 20000000)) (hi := (95367451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100063 / 1000000) = 1/(1000000 / 1100063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6752 : Bounds (1907349 / 20000000) (95367451 / 1000000000) (Real.log (1100063 / 1000000)) := by
  have h := reflection_log_6752_neg
  have he : Real.log (1100063 / 1000000) = -Real.log (1000000 / 1100063) := by
    rw [show ((1100063 / 1000000) : ℝ) = ((1000000 / 1100063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6753_neg : (52715259 / 500000000) ≤ -Real.log (899937 / 1000000) ∧
    -Real.log (899937 / 1000000) ≤ (105430519 / 1000000000) := by
  have h := checkLog_sound (w := (100063 / 1899937)) (n := 12)
    (lo := (52715259 / 500000000)) (hi := (105430519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899937) = 1/(899937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6753 : Bounds (-105430519 / 1000000000) (-52715259 / 500000000) (Real.log (899937 / 1000000)) := by
  have h := reflection_log_6753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6754_neg : (10063067 / 1000000000) ≤ -Real.log (989987396031 / 1000000000000) ∧
    -Real.log (989987396031 / 1000000000000) ≤ (2515767 / 250000000) := by
  have h := checkLog_sound (w := (10012603969 / 1989987396031)) (n := 12)
    (lo := (10063067 / 1000000000)) (hi := (2515767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989987396031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989987396031) = 1/(989987396031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6754 : Bounds (-2515767 / 250000000) (-10063067 / 1000000000) (Real.log (989987396031 / 1000000000000)) := by
  have h := reflection_log_6754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6755_neg : (5006297 / 500000000) ≤ -Real.log (990037365031 / 1000000000000) ∧
    -Real.log (990037365031 / 1000000000000) ≤ (2002519 / 200000000) := by
  have h := checkLog_sound (w := (9962634969 / 1990037365031)) (n := 12)
    (lo := (5006297 / 500000000)) (hi := (2002519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990037365031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990037365031) = 1/(990037365031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6755 : Bounds (-2002519 / 200000000) (-5006297 / 500000000) (Real.log (990037365031 / 1000000000000)) := by
  have h := reflection_log_6755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6756_neg : (50073231 / 250000000) ≤ -Real.log (62500000000 / 76360036859) ∧
    -Real.log (62500000000 / 76360036859) ≤ (8011717 / 40000000) := by
  have h := checkLog_sound (w := (13860036859 / 138860036859)) (n := 12)
    (lo := (50073231 / 250000000)) (hi := (8011717 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76360036859 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76360036859 / 62500000000) = 1/(62500000000 / 76360036859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6756 : Bounds (50073231 / 250000000) (8011717 / 40000000) (Real.log (76360036859 / 62500000000)) := by
  have h := reflection_log_6756_neg
  have he : Real.log (76360036859 / 62500000000) = -Real.log (62500000000 / 76360036859) := by
    rw [show ((76360036859 / 62500000000) : ℝ) = ((62500000000 / 76360036859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6757_neg : (12549873 / 62500000) ≤ -Real.log (250000000000 / 305594447167) ∧
    -Real.log (250000000000 / 305594447167) ≤ (200797969 / 1000000000) := by
  have h := checkLog_sound (w := (55594447167 / 555594447167)) (n := 12)
    (lo := (12549873 / 62500000)) (hi := (200797969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305594447167 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305594447167 / 250000000000) = 1/(250000000000 / 305594447167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6757 : Bounds (12549873 / 62500000) (200797969 / 1000000000) (Real.log (305594447167 / 250000000000)) := by
  have h := reflection_log_6757_neg
  have he : Real.log (305594447167 / 250000000000) = -Real.log (250000000000 / 305594447167) := by
    rw [show ((305594447167 / 250000000000) : ℝ) = ((250000000000 / 305594447167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6758_neg : (201066441 / 500000000) ≤ -Real.log (500000000000 / 747504990019) ∧
    -Real.log (500000000000 / 747504990019) ≤ (402132883 / 1000000000) := by
  have h := checkLog_sound (w := (247504990019 / 1247504990019)) (n := 12)
    (lo := (201066441 / 500000000)) (hi := (402132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747504990019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747504990019 / 500000000000) = 1/(500000000000 / 747504990019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6758 : Bounds (201066441 / 500000000) (402132883 / 1000000000) (Real.log (747504990019 / 500000000000)) := by
  have h := reflection_log_6758_neg
  have he : Real.log (747504990019 / 500000000000) = -Real.log (500000000000 / 747504990019) := by
    rw [show ((747504990019 / 500000000000) : ℝ) = ((500000000000 / 747504990019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6759_neg : (402341081 / 1000000000) ≤ -Real.log (500000000000 / 747660636307) ∧
    -Real.log (500000000000 / 747660636307) ≤ (201170541 / 500000000) := by
  have h := checkLog_sound (w := (247660636307 / 1247660636307)) (n := 12)
    (lo := (402341081 / 1000000000)) (hi := (201170541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747660636307 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747660636307 / 500000000000) = 1/(500000000000 / 747660636307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6759 : Bounds (402341081 / 1000000000) (201170541 / 500000000) (Real.log (747660636307 / 500000000000)) := by
  have h := reflection_log_6759_neg
  have he : Real.log (747660636307 / 500000000000) = -Real.log (500000000000 / 747660636307) := by
    rw [show ((747660636307 / 500000000000) : ℝ) = ((500000000000 / 747660636307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6760_neg : (181154209 / 1000000000) ≤ -Real.log (5000 / 5993) ∧
    -Real.log (5000 / 5993) ≤ (18115421 / 100000000) := by
  have h := checkLog_sound (w := (993 / 10993)) (n := 12)
    (lo := (181154209 / 1000000000)) (hi := (18115421 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5993 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5993 / 5000) = 1/(5000 / 5993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6760 : Bounds (181154209 / 1000000000) (18115421 / 100000000) (Real.log (5993 / 5000)) := by
  have h := reflection_log_6760_neg
  have he : Real.log (5993 / 5000) = -Real.log (5000 / 5993) := by
    rw [show ((5993 / 5000) : ℝ) = ((5000 / 5993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6761_neg : (5534877 / 25000000) ≤ -Real.log (4007 / 5000) ∧
    -Real.log (4007 / 5000) ≤ (221395081 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 9007)) (n := 12)
    (lo := (5534877 / 25000000)) (hi := (221395081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4007) = 1/(4007 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6761 : Bounds (-221395081 / 1000000000) (-5534877 / 25000000) (Real.log (4007 / 5000)) := by
  have h := reflection_log_6761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6762_neg : (9929 / 50000000) ≤ -Real.log (5000000 / 5000993) ∧
    -Real.log (5000000 / 5000993) ≤ (198581 / 1000000000) := by
  have h := checkLog_sound (w := (993 / 10000993)) (n := 12)
    (lo := (9929 / 50000000)) (hi := (198581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000993 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000993 / 5000000) = 1/(5000000 / 5000993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6762 : Bounds (9929 / 50000000) (198581 / 1000000000) (Real.log (5000993 / 5000000)) := by
  have h := reflection_log_6762_neg
  have he : Real.log (5000993 / 5000000) = -Real.log (5000000 / 5000993) := by
    rw [show ((5000993 / 5000000) : ℝ) = ((5000000 / 5000993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6763_neg : (198619 / 1000000000) ≤ -Real.log (4999007 / 5000000) ∧
    -Real.log (4999007 / 5000000) ≤ (9931 / 50000000) := by
  have h := checkLog_sound (w := (993 / 9999007)) (n := 12)
    (lo := (198619 / 1000000000)) (hi := (9931 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999007) = 1/(4999007 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6763 : Bounds (-9931 / 50000000) (-198619 / 1000000000) (Real.log (4999007 / 5000000)) := by
  have h := reflection_log_6763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6764_neg : (19037307 / 200000000) ≤ -Real.log (125000 / 137483) ∧
    -Real.log (125000 / 137483) ≤ (11898317 / 125000000) := by
  have h := checkLog_sound (w := (12483 / 262483)) (n := 12)
    (lo := (19037307 / 200000000)) (hi := (11898317 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137483 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137483 / 125000) = 1/(125000 / 137483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6764 : Bounds (19037307 / 200000000) (11898317 / 125000000) (Real.log (137483 / 125000)) := by
  have h := reflection_log_6764_neg
  have he : Real.log (137483 / 125000) = -Real.log (125000 / 137483) := by
    rw [show ((137483 / 125000) : ℝ) = ((125000 / 137483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6765_neg : (21041883 / 200000000) ≤ -Real.log (112517 / 125000) ∧
    -Real.log (112517 / 125000) ≤ (13151177 / 125000000) := by
  have h := checkLog_sound (w := (12483 / 237517)) (n := 12)
    (lo := (21041883 / 200000000)) (hi := (13151177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112517) = 1/(112517 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6765 : Bounds (-13151177 / 125000000) (-21041883 / 200000000) (Real.log (112517 / 125000)) := by
  have h := reflection_log_6765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6766_neg : (9541381 / 100000000) ≤ -Real.log (500000 / 550057) ∧
    -Real.log (500000 / 550057) ≤ (95413811 / 1000000000) := by
  have h := checkLog_sound (w := (50057 / 1050057)) (n := 12)
    (lo := (9541381 / 100000000)) (hi := (95413811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550057 / 500000) = 1/(500000 / 550057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6766 : Bounds (9541381 / 100000000) (95413811 / 1000000000) (Real.log (550057 / 500000)) := by
  have h := reflection_log_6766_neg
  have he : Real.log (550057 / 500000) = -Real.log (500000 / 550057) := by
    rw [show ((550057 / 500000) : ℝ) = ((500000 / 550057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6767_neg : (10548719 / 100000000) ≤ -Real.log (449943 / 500000) ∧
    -Real.log (449943 / 500000) ≤ (105487191 / 1000000000) := by
  have h := checkLog_sound (w := (50057 / 949943)) (n := 12)
    (lo := (10548719 / 100000000)) (hi := (105487191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449943) = 1/(449943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6767 : Bounds (-105487191 / 1000000000) (-10548719 / 100000000) (Real.log (449943 / 500000)) := by
  have h := reflection_log_6767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6768_neg : (10073379 / 1000000000) ≤ -Real.log (247494296751 / 250000000000) ∧
    -Real.log (247494296751 / 250000000000) ≤ (503669 / 50000000) := by
  have h := checkLog_sound (w := (2505703249 / 497494296751)) (n := 12)
    (lo := (10073379 / 1000000000)) (hi := (503669 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247494296751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247494296751) = 1/(247494296751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6768 : Bounds (-503669 / 50000000) (-10073379 / 1000000000) (Real.log (247494296751 / 250000000000)) := by
  have h := reflection_log_6768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6769_neg : (62643 / 6250000) ≤ -Real.log (15469174711 / 15625000000) ∧
    -Real.log (15469174711 / 15625000000) ≤ (10022881 / 1000000000) := by
  have h := checkLog_sound (w := (155825289 / 31094174711)) (n := 12)
    (lo := (62643 / 6250000)) (hi := (10022881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15469174711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15469174711) = 1/(15469174711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6769 : Bounds (-10022881 / 1000000000) (-62643 / 6250000) (Real.log (15469174711 / 15625000000)) := by
  have h := reflection_log_6769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6770_neg : (200395951 / 1000000000) ≤ -Real.log (125000000000 / 152735808811) ∧
    -Real.log (125000000000 / 152735808811) ≤ (12524747 / 62500000) := by
  have h := checkLog_sound (w := (27735808811 / 277735808811)) (n := 12)
    (lo := (200395951 / 1000000000)) (hi := (12524747 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152735808811 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152735808811 / 125000000000) = 1/(125000000000 / 152735808811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6770 : Bounds (200395951 / 1000000000) (12524747 / 62500000) (Real.log (152735808811 / 125000000000)) := by
  have h := reflection_log_6770_neg
  have he : Real.log (152735808811 / 125000000000) = -Real.log (125000000000 / 152735808811) := by
    rw [show ((152735808811 / 125000000000) : ℝ) = ((125000000000 / 152735808811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6771_neg : (200901001 / 1000000000) ≤ -Real.log (250000000000 / 305625934841) ∧
    -Real.log (250000000000 / 305625934841) ≤ (100450501 / 500000000) := by
  have h := checkLog_sound (w := (55625934841 / 555625934841)) (n := 12)
    (lo := (200901001 / 1000000000)) (hi := (100450501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305625934841 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305625934841 / 250000000000) = 1/(250000000000 / 305625934841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6771 : Bounds (200901001 / 1000000000) (100450501 / 500000000) (Real.log (305625934841 / 250000000000)) := by
  have h := reflection_log_6771_neg
  have he : Real.log (305625934841 / 250000000000) = -Real.log (250000000000 / 305625934841) := by
    rw [show ((305625934841 / 250000000000) : ℝ) = ((250000000000 / 305625934841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6772_neg : (402341081 / 1000000000) ≤ -Real.log (250000000000 / 373830318153) ∧
    -Real.log (250000000000 / 373830318153) ≤ (201170541 / 500000000) := by
  have h := checkLog_sound (w := (123830318153 / 623830318153)) (n := 12)
    (lo := (402341081 / 1000000000)) (hi := (201170541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373830318153 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373830318153 / 250000000000) = 1/(250000000000 / 373830318153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6772 : Bounds (402341081 / 1000000000) (201170541 / 500000000) (Real.log (373830318153 / 250000000000)) := by
  have h := reflection_log_6772_neg
  have he : Real.log (373830318153 / 250000000000) = -Real.log (250000000000 / 373830318153) := by
    rw [show ((373830318153 / 250000000000) : ℝ) = ((250000000000 / 373830318153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6773_neg : (402549289 / 1000000000) ≤ -Real.log (250000000000 / 373908160719) ∧
    -Real.log (250000000000 / 373908160719) ≤ (40254929 / 100000000) := by
  have h := checkLog_sound (w := (123908160719 / 623908160719)) (n := 12)
    (lo := (402549289 / 1000000000)) (hi := (40254929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373908160719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373908160719 / 250000000000) = 1/(250000000000 / 373908160719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6773 : Bounds (402549289 / 1000000000) (40254929 / 100000000) (Real.log (373908160719 / 250000000000)) := by
  have h := reflection_log_6773_neg
  have he : Real.log (373908160719 / 250000000000) = -Real.log (250000000000 / 373908160719) := by
    rw [show ((373908160719 / 250000000000) : ℝ) = ((250000000000 / 373908160719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6774_neg : (45309409 / 250000000) ≤ -Real.log (10000 / 11987) ∧
    -Real.log (10000 / 11987) ≤ (181237637 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 21987)) (n := 12)
    (lo := (45309409 / 250000000)) (hi := (181237637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11987 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11987 / 10000) = 1/(10000 / 11987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6774 : Bounds (45309409 / 250000000) (181237637 / 1000000000) (Real.log (11987 / 10000)) := by
  have h := reflection_log_6774_neg
  have he : Real.log (11987 / 10000) = -Real.log (10000 / 11987) := by
    rw [show ((11987 / 10000) : ℝ) = ((10000 / 11987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6775_neg : (22151987 / 100000000) ≤ -Real.log (8013 / 10000) ∧
    -Real.log (8013 / 10000) ≤ (221519871 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 18013)) (n := 12)
    (lo := (22151987 / 100000000)) (hi := (221519871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8013) = 1/(8013 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6775 : Bounds (-221519871 / 1000000000) (-22151987 / 100000000) (Real.log (8013 / 10000)) := by
  have h := reflection_log_6775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6776_neg : (4967 / 25000000) ≤ -Real.log (10000000 / 10001987) ∧
    -Real.log (10000000 / 10001987) ≤ (198681 / 1000000000) := by
  have h := checkLog_sound (w := (1987 / 20001987)) (n := 12)
    (lo := (4967 / 25000000)) (hi := (198681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001987 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001987 / 10000000) = 1/(10000000 / 10001987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6776 : Bounds (4967 / 25000000) (198681 / 1000000000) (Real.log (10001987 / 10000000)) := by
  have h := reflection_log_6776_neg
  have he : Real.log (10001987 / 10000000) = -Real.log (10000000 / 10001987) := by
    rw [show ((10001987 / 10000000) : ℝ) = ((10000000 / 10001987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6777_neg : (198719 / 1000000000) ≤ -Real.log (9998013 / 10000000) ∧
    -Real.log (9998013 / 10000000) ≤ (621 / 3125000) := by
  have h := checkLog_sound (w := (1987 / 19998013)) (n := 12)
    (lo := (198719 / 1000000000)) (hi := (621 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998013) = 1/(9998013 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6777 : Bounds (-621 / 3125000) (-198719 / 1000000000) (Real.log (9998013 / 10000000)) := by
  have h := reflection_log_6777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6778_neg : (11904113 / 125000000) ≤ -Real.log (200000 / 219983) ∧
    -Real.log (200000 / 219983) ≤ (19046581 / 200000000) := by
  have h := checkLog_sound (w := (19983 / 419983)) (n := 12)
    (lo := (11904113 / 125000000)) (hi := (19046581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219983 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219983 / 200000) = 1/(200000 / 219983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6778 : Bounds (11904113 / 125000000) (19046581 / 200000000) (Real.log (219983 / 200000)) := by
  have h := reflection_log_6778_neg
  have he : Real.log (219983 / 200000) = -Real.log (200000 / 219983) := by
    rw [show ((219983 / 200000) : ℝ) = ((200000 / 219983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6779_neg : (4210643 / 40000000) ≤ -Real.log (180017 / 200000) ∧
    -Real.log (180017 / 200000) ≤ (26316519 / 250000000) := by
  have h := checkLog_sound (w := (19983 / 380017)) (n := 12)
    (lo := (4210643 / 40000000)) (hi := (26316519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180017) = 1/(180017 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6779 : Bounds (-26316519 / 250000000) (-4210643 / 40000000) (Real.log (180017 / 200000)) := by
  have h := reflection_log_6779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6780_neg : (11932521 / 125000000) ≤ -Real.log (200000 / 220033) ∧
    -Real.log (200000 / 220033) ≤ (95460169 / 1000000000) := by
  have h := checkLog_sound (w := (20033 / 420033)) (n := 12)
    (lo := (11932521 / 125000000)) (hi := (95460169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220033 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220033 / 200000) = 1/(200000 / 220033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6780 : Bounds (11932521 / 125000000) (95460169 / 1000000000) (Real.log (220033 / 200000)) := by
  have h := reflection_log_6780_neg
  have he : Real.log (220033 / 200000) = -Real.log (200000 / 220033) := by
    rw [show ((220033 / 200000) : ℝ) = ((200000 / 220033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6781_neg : (21108773 / 200000000) ≤ -Real.log (179967 / 200000) ∧
    -Real.log (179967 / 200000) ≤ (52771933 / 500000000) := by
  have h := checkLog_sound (w := (20033 / 379967)) (n := 12)
    (lo := (21108773 / 200000000)) (hi := (52771933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179967) = 1/(179967 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6781 : Bounds (-52771933 / 500000000) (-21108773 / 200000000) (Real.log (179967 / 200000)) := by
  have h := reflection_log_6781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6782_neg : (10083697 / 1000000000) ≤ -Real.log (39598678911 / 40000000000) ∧
    -Real.log (39598678911 / 40000000000) ≤ (5041849 / 500000000) := by
  have h := checkLog_sound (w := (401321089 / 79598678911)) (n := 12)
    (lo := (10083697 / 1000000000)) (hi := (5041849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39598678911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39598678911) = 1/(39598678911 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6782 : Bounds (-5041849 / 500000000) (-10083697 / 1000000000) (Real.log (39598678911 / 40000000000)) := by
  have h := reflection_log_6782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6783_neg : (10033171 / 1000000000) ≤ -Real.log (39600679711 / 40000000000) ∧
    -Real.log (39600679711 / 40000000000) ≤ (2508293 / 250000000) := by
  have h := checkLog_sound (w := (399320289 / 79600679711)) (n := 12)
    (lo := (10033171 / 1000000000)) (hi := (2508293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39600679711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39600679711) = 1/(39600679711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6783 : Bounds (-2508293 / 250000000) (-10033171 / 1000000000) (Real.log (39600679711 / 40000000000)) := by
  have h := reflection_log_6783_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
