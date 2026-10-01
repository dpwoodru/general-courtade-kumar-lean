import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5696_neg : (17479329 / 100000000) ≤ -Real.log (1000 / 1191) ∧
    -Real.log (1000 / 1191) ≤ (174793291 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 2191)) (n := 12)
    (lo := (17479329 / 100000000)) (hi := (174793291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191 / 1000) = 1/(1000 / 1191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5696 : Bounds (17479329 / 100000000) (174793291 / 1000000000) (Real.log (1191 / 1000)) := by
  have h := reflection_log_5696_neg
  have he : Real.log (1191 / 1000) = -Real.log (1000 / 1191) := by
    rw [show ((1191 / 1000) : ℝ) = ((1000 / 1191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5697_neg : (211956361 / 1000000000) ≤ -Real.log (809 / 1000) ∧
    -Real.log (809 / 1000) ≤ (105978181 / 500000000) := by
  have h := checkLog_sound (w := (191 / 1809)) (n := 12)
    (lo := (211956361 / 1000000000)) (hi := (105978181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 809) = 1/(809 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5697 : Bounds (-105978181 / 500000000) (-211956361 / 1000000000) (Real.log (809 / 1000)) := by
  have h := reflection_log_5697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5698_neg : (190981 / 1000000000) ≤ -Real.log (1000000 / 1000191) ∧
    -Real.log (1000000 / 1000191) ≤ (95491 / 500000000) := by
  have h := checkLog_sound (w := (191 / 2000191)) (n := 12)
    (lo := (190981 / 1000000000)) (hi := (95491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000191 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000191 / 1000000) = 1/(1000000 / 1000191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5698 : Bounds (190981 / 1000000000) (95491 / 500000000) (Real.log (1000191 / 1000000)) := by
  have h := reflection_log_5698_neg
  have he : Real.log (1000191 / 1000000) = -Real.log (1000000 / 1000191) := by
    rw [show ((1000191 / 1000000) : ℝ) = ((1000000 / 1000191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5699_neg : (95509 / 500000000) ≤ -Real.log (999809 / 1000000) ∧
    -Real.log (999809 / 1000000) ≤ (191019 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1999809)) (n := 12)
    (lo := (95509 / 500000000)) (hi := (191019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999809) = 1/(999809 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5699 : Bounds (-191019 / 1000000000) (-95509 / 500000000) (Real.log (999809 / 1000000)) := by
  have h := reflection_log_5699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5700_neg : (91657151 / 1000000000) ≤ -Real.log (1000000 / 1095989) ∧
    -Real.log (1000000 / 1095989) ≤ (1432143 / 15625000) := by
  have h := checkLog_sound (w := (95989 / 2095989)) (n := 12)
    (lo := (91657151 / 1000000000)) (hi := (1432143 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095989 / 1000000) = 1/(1000000 / 1095989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5700 : Bounds (91657151 / 1000000000) (1432143 / 15625000) (Real.log (1095989 / 1000000)) := by
  have h := reflection_log_5700_neg
  have he : Real.log (1095989 / 1000000) = -Real.log (1000000 / 1095989) := by
    rw [show ((1095989 / 1000000) : ℝ) = ((1000000 / 1095989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5701_neg : (80731 / 800000) ≤ -Real.log (904011 / 1000000) ∧
    -Real.log (904011 / 1000000) ≤ (100913751 / 1000000000) := by
  have h := checkLog_sound (w := (95989 / 1904011)) (n := 12)
    (lo := (80731 / 800000)) (hi := (100913751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904011) = 1/(904011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5701 : Bounds (-100913751 / 1000000000) (-80731 / 800000) (Real.log (904011 / 1000000)) := by
  have h := reflection_log_5701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5702_neg : (4593851 / 50000000) ≤ -Real.log (100000 / 109623) ∧
    -Real.log (100000 / 109623) ≤ (91877021 / 1000000000) := by
  have h := checkLog_sound (w := (9623 / 209623)) (n := 12)
    (lo := (4593851 / 50000000)) (hi := (91877021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109623 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109623 / 100000) = 1/(100000 / 109623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5702 : Bounds (4593851 / 50000000) (91877021 / 1000000000) (Real.log (109623 / 100000)) := by
  have h := reflection_log_5702_neg
  have he : Real.log (109623 / 100000) = -Real.log (100000 / 109623) := by
    rw [show ((109623 / 100000) : ℝ) = ((100000 / 109623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5703_neg : (809443 / 8000000) ≤ -Real.log (90377 / 100000) ∧
    -Real.log (90377 / 100000) ≤ (12647547 / 125000000) := by
  have h := checkLog_sound (w := (9623 / 190377)) (n := 12)
    (lo := (809443 / 8000000)) (hi := (12647547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90377) = 1/(90377 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5703 : Bounds (-12647547 / 125000000) (-809443 / 8000000) (Real.log (90377 / 100000)) := by
  have h := reflection_log_5703_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5704_neg : (1860671 / 200000000) ≤ -Real.log (9907397871 / 10000000000) ∧
    -Real.log (9907397871 / 10000000000) ≤ (2325839 / 250000000) := by
  have h := checkLog_sound (w := (92602129 / 19907397871)) (n := 12)
    (lo := (1860671 / 200000000)) (hi := (2325839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9907397871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9907397871) = 1/(9907397871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5704 : Bounds (-2325839 / 250000000) (-1860671 / 200000000) (Real.log (9907397871 / 10000000000)) := by
  have h := reflection_log_5704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5705_neg : (4628299 / 500000000) ≤ -Real.log (990786111879 / 1000000000000) ∧
    -Real.log (990786111879 / 1000000000000) ≤ (9256599 / 1000000000) := by
  have h := checkLog_sound (w := (9213888121 / 1990786111879)) (n := 12)
    (lo := (4628299 / 500000000)) (hi := (9256599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990786111879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990786111879) = 1/(990786111879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5705 : Bounds (-9256599 / 1000000000) (-4628299 / 500000000) (Real.log (990786111879 / 1000000000000)) := by
  have h := reflection_log_5705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5706_neg : (96285451 / 500000000) ≤ -Real.log (100000000000 / 121236246019) ∧
    -Real.log (100000000000 / 121236246019) ≤ (192570903 / 1000000000) := by
  have h := checkLog_sound (w := (21236246019 / 221236246019)) (n := 12)
    (lo := (96285451 / 500000000)) (hi := (192570903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121236246019 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121236246019 / 100000000000) = 1/(100000000000 / 121236246019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5706 : Bounds (96285451 / 500000000) (192570903 / 1000000000) (Real.log (121236246019 / 100000000000)) := by
  have h := reflection_log_5706_neg
  have he : Real.log (121236246019 / 100000000000) = -Real.log (100000000000 / 121236246019) := by
    rw [show ((121236246019 / 100000000000) : ℝ) = ((100000000000 / 121236246019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5707_neg : (48264349 / 250000000) ≤ -Real.log (50000000000 / 60647620523) ∧
    -Real.log (50000000000 / 60647620523) ≤ (193057397 / 1000000000) := by
  have h := checkLog_sound (w := (10647620523 / 110647620523)) (n := 12)
    (lo := (48264349 / 250000000)) (hi := (193057397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60647620523 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60647620523 / 50000000000) = 1/(50000000000 / 60647620523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5707 : Bounds (48264349 / 250000000) (193057397 / 1000000000) (Real.log (60647620523 / 50000000000)) := by
  have h := reflection_log_5707_neg
  have he : Real.log (60647620523 / 50000000000) = -Real.log (50000000000 / 60647620523) := by
    rw [show ((60647620523 / 50000000000) : ℝ) = ((50000000000 / 60647620523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5708_neg : (386542083 / 1000000000) ≤ -Real.log (1250000000 / 1839852923) ∧
    -Real.log (1250000000 / 1839852923) ≤ (96635521 / 250000000) := by
  have h := checkLog_sound (w := (589852923 / 3089852923)) (n := 12)
    (lo := (386542083 / 1000000000)) (hi := (96635521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839852923 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839852923 / 1250000000) = 1/(1250000000 / 1839852923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5708 : Bounds (386542083 / 1000000000) (96635521 / 250000000) (Real.log (1839852923 / 1250000000)) := by
  have h := reflection_log_5708_neg
  have he : Real.log (1839852923 / 1250000000) = -Real.log (1250000000 / 1839852923) := by
    rw [show ((1839852923 / 1250000000) : ℝ) = ((1250000000 / 1839852923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5709_neg : (96687413 / 250000000) ≤ -Real.log (25000000000 / 36804697157) ∧
    -Real.log (25000000000 / 36804697157) ≤ (386749653 / 1000000000) := by
  have h := checkLog_sound (w := (11804697157 / 61804697157)) (n := 12)
    (lo := (96687413 / 250000000)) (hi := (386749653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36804697157 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36804697157 / 25000000000) = 1/(25000000000 / 36804697157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5709 : Bounds (96687413 / 250000000) (386749653 / 1000000000) (Real.log (36804697157 / 25000000000)) := by
  have h := reflection_log_5709_neg
  have he : Real.log (36804697157 / 25000000000) = -Real.log (25000000000 / 36804697157) := by
    rw [show ((36804697157 / 25000000000) : ℝ) = ((25000000000 / 36804697157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5710_neg : (174877249 / 1000000000) ≤ -Real.log (10000 / 11911) ∧
    -Real.log (10000 / 11911) ≤ (699509 / 4000000) := by
  have h := checkLog_sound (w := (1911 / 21911)) (n := 12)
    (lo := (174877249 / 1000000000)) (hi := (699509 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11911 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11911 / 10000) = 1/(10000 / 11911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5710 : Bounds (174877249 / 1000000000) (699509 / 4000000) (Real.log (11911 / 10000)) := by
  have h := reflection_log_5710_neg
  have he : Real.log (11911 / 10000) = -Real.log (10000 / 11911) := by
    rw [show ((11911 / 10000) : ℝ) = ((10000 / 11911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5711_neg : (106039989 / 500000000) ≤ -Real.log (8089 / 10000) ∧
    -Real.log (8089 / 10000) ≤ (212079979 / 1000000000) := by
  have h := checkLog_sound (w := (1911 / 18089)) (n := 12)
    (lo := (106039989 / 500000000)) (hi := (212079979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8089) = 1/(8089 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5711 : Bounds (-212079979 / 1000000000) (-106039989 / 500000000) (Real.log (8089 / 10000)) := by
  have h := reflection_log_5711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5712_neg : (191081 / 1000000000) ≤ -Real.log (10000000 / 10001911) ∧
    -Real.log (10000000 / 10001911) ≤ (95541 / 500000000) := by
  have h := checkLog_sound (w := (1911 / 20001911)) (n := 12)
    (lo := (191081 / 1000000000)) (hi := (95541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001911 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001911 / 10000000) = 1/(10000000 / 10001911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5712 : Bounds (191081 / 1000000000) (95541 / 500000000) (Real.log (10001911 / 10000000)) := by
  have h := reflection_log_5712_neg
  have he : Real.log (10001911 / 10000000) = -Real.log (10000000 / 10001911) := by
    rw [show ((10001911 / 10000000) : ℝ) = ((10000000 / 10001911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5713_neg : (95559 / 500000000) ≤ -Real.log (9998089 / 10000000) ∧
    -Real.log (9998089 / 10000000) ≤ (191119 / 1000000000) := by
  have h := checkLog_sound (w := (1911 / 19998089)) (n := 12)
    (lo := (95559 / 500000000)) (hi := (191119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998089) = 1/(9998089 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5713 : Bounds (-191119 / 1000000000) (-95559 / 500000000) (Real.log (9998089 / 10000000)) := by
  have h := reflection_log_5713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5714_neg : (22925921 / 250000000) ≤ -Real.log (25000 / 27401) ∧
    -Real.log (25000 / 27401) ≤ (18340737 / 200000000) := by
  have h := checkLog_sound (w := (2401 / 52401)) (n := 12)
    (lo := (22925921 / 250000000)) (hi := (18340737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27401 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27401 / 25000) = 1/(25000 / 27401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5714 : Bounds (22925921 / 250000000) (18340737 / 200000000) (Real.log (27401 / 25000)) := by
  have h := reflection_log_5714_neg
  have he : Real.log (27401 / 25000) = -Real.log (25000 / 27401) := by
    rw [show ((27401 / 25000) : ℝ) = ((25000 / 27401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5715_neg : (100970167 / 1000000000) ≤ -Real.log (22599 / 25000) ∧
    -Real.log (22599 / 25000) ≤ (12621271 / 125000000) := by
  have h := checkLog_sound (w := (2401 / 47599)) (n := 12)
    (lo := (100970167 / 1000000000)) (hi := (12621271 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22599) = 1/(22599 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5715 : Bounds (-12621271 / 125000000) (-100970167 / 1000000000) (Real.log (22599 / 25000)) := by
  have h := reflection_log_5715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5716_neg : (45961771 / 500000000) ≤ -Real.log (1000000 / 1096281) ∧
    -Real.log (1000000 / 1096281) ≤ (91923543 / 1000000000) := by
  have h := checkLog_sound (w := (96281 / 2096281)) (n := 12)
    (lo := (45961771 / 500000000)) (hi := (91923543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096281 / 1000000) = 1/(1000000 / 1096281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5716 : Bounds (45961771 / 500000000) (91923543 / 1000000000) (Real.log (1096281 / 1000000)) := by
  have h := reflection_log_5716_neg
  have he : Real.log (1096281 / 1000000) = -Real.log (1000000 / 1096281) := by
    rw [show ((1096281 / 1000000) : ℝ) = ((1000000 / 1096281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5717_neg : (101236807 / 1000000000) ≤ -Real.log (903719 / 1000000) ∧
    -Real.log (903719 / 1000000) ≤ (12654601 / 125000000) := by
  have h := checkLog_sound (w := (96281 / 1903719)) (n := 12)
    (lo := (101236807 / 1000000000)) (hi := (12654601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903719) = 1/(903719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5717 : Bounds (-12654601 / 125000000) (-101236807 / 1000000000) (Real.log (903719 / 1000000)) := by
  have h := reflection_log_5717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5718_neg : (1862653 / 200000000) ≤ -Real.log (990729969039 / 1000000000000) ∧
    -Real.log (990729969039 / 1000000000000) ≤ (4656633 / 500000000) := by
  have h := checkLog_sound (w := (9270030961 / 1990729969039)) (n := 12)
    (lo := (1862653 / 200000000)) (hi := (4656633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990729969039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990729969039) = 1/(990729969039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5718 : Bounds (-4656633 / 500000000) (-1862653 / 200000000) (Real.log (990729969039 / 1000000000000)) := by
  have h := reflection_log_5718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5719_neg : (9266483 / 1000000000) ≤ -Real.log (619235199 / 625000000) ∧
    -Real.log (619235199 / 625000000) ≤ (2316621 / 250000000) := by
  have h := checkLog_sound (w := (5764801 / 1244235199)) (n := 12)
    (lo := (9266483 / 1000000000)) (hi := (2316621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 619235199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 619235199) = 1/(619235199 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5719 : Bounds (-2316621 / 250000000) (-9266483 / 1000000000) (Real.log (619235199 / 625000000)) := by
  have h := reflection_log_5719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5720_neg : (192673851 / 1000000000) ≤ -Real.log (500000000000 / 606243639099) ∧
    -Real.log (500000000000 / 606243639099) ≤ (48168463 / 250000000) := by
  have h := checkLog_sound (w := (106243639099 / 1106243639099)) (n := 12)
    (lo := (192673851 / 1000000000)) (hi := (48168463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606243639099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606243639099 / 500000000000) = 1/(500000000000 / 606243639099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5720 : Bounds (192673851 / 1000000000) (48168463 / 250000000) (Real.log (606243639099 / 500000000000)) := by
  have h := reflection_log_5720_neg
  have he : Real.log (606243639099 / 500000000000) = -Real.log (500000000000 / 606243639099) := by
    rw [show ((606243639099 / 500000000000) : ℝ) = ((500000000000 / 606243639099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5721_neg : (3863207 / 20000000) ≤ -Real.log (500000000000 / 606538647523) ∧
    -Real.log (500000000000 / 606538647523) ≤ (193160351 / 1000000000) := by
  have h := checkLog_sound (w := (106538647523 / 1106538647523)) (n := 12)
    (lo := (3863207 / 20000000)) (hi := (193160351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606538647523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606538647523 / 500000000000) = 1/(500000000000 / 606538647523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5721 : Bounds (3863207 / 20000000) (193160351 / 1000000000) (Real.log (606538647523 / 500000000000)) := by
  have h := reflection_log_5721_neg
  have he : Real.log (606538647523 / 500000000000) = -Real.log (500000000000 / 606538647523) := by
    rw [show ((606538647523 / 500000000000) : ℝ) = ((500000000000 / 606538647523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5722_neg : (96687413 / 250000000) ≤ -Real.log (500000000000 / 736093943139) ∧
    -Real.log (500000000000 / 736093943139) ≤ (386749653 / 1000000000) := by
  have h := checkLog_sound (w := (236093943139 / 1236093943139)) (n := 12)
    (lo := (96687413 / 250000000)) (hi := (386749653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736093943139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736093943139 / 500000000000) = 1/(500000000000 / 736093943139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5722 : Bounds (96687413 / 250000000) (386749653 / 1000000000) (Real.log (736093943139 / 500000000000)) := by
  have h := reflection_log_5722_neg
  have he : Real.log (736093943139 / 500000000000) = -Real.log (500000000000 / 736093943139) := by
    rw [show ((736093943139 / 500000000000) : ℝ) = ((500000000000 / 736093943139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5723_neg : (96739307 / 250000000) ≤ -Real.log (500000000000 / 736246754853) ∧
    -Real.log (500000000000 / 736246754853) ≤ (386957229 / 1000000000) := by
  have h := checkLog_sound (w := (236246754853 / 1236246754853)) (n := 12)
    (lo := (96739307 / 250000000)) (hi := (386957229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736246754853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736246754853 / 500000000000) = 1/(500000000000 / 736246754853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5723 : Bounds (96739307 / 250000000) (386957229 / 1000000000) (Real.log (736246754853 / 500000000000)) := by
  have h := reflection_log_5723_neg
  have he : Real.log (736246754853 / 500000000000) = -Real.log (500000000000 / 736246754853) := by
    rw [show ((736246754853 / 500000000000) : ℝ) = ((500000000000 / 736246754853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5724_neg : (87480601 / 500000000) ≤ -Real.log (1250 / 1489) ∧
    -Real.log (1250 / 1489) ≤ (174961203 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2739)) (n := 12)
    (lo := (87480601 / 500000000)) (hi := (174961203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1489 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1489 / 1250) = 1/(1250 / 1489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5724 : Bounds (87480601 / 500000000) (174961203 / 1000000000) (Real.log (1489 / 1250)) := by
  have h := reflection_log_5724_neg
  have he : Real.log (1489 / 1250) = -Real.log (1250 / 1489) := by
    rw [show ((1489 / 1250) : ℝ) = ((1250 / 1489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5725_neg : (212203611 / 1000000000) ≤ -Real.log (1011 / 1250) ∧
    -Real.log (1011 / 1250) ≤ (53050903 / 250000000) := by
  have h := checkLog_sound (w := (239 / 2261)) (n := 12)
    (lo := (212203611 / 1000000000)) (hi := (53050903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1011) = 1/(1011 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5725 : Bounds (-53050903 / 250000000) (-212203611 / 1000000000) (Real.log (1011 / 1250)) := by
  have h := reflection_log_5725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5726_neg : (191181 / 1000000000) ≤ -Real.log (1250000 / 1250239) ∧
    -Real.log (1250000 / 1250239) ≤ (95591 / 500000000) := by
  have h := checkLog_sound (w := (239 / 2500239)) (n := 12)
    (lo := (191181 / 1000000000)) (hi := (95591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250239 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250239 / 1250000) = 1/(1250000 / 1250239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5726 : Bounds (191181 / 1000000000) (95591 / 500000000) (Real.log (1250239 / 1250000)) := by
  have h := reflection_log_5726_neg
  have he : Real.log (1250239 / 1250000) = -Real.log (1250000 / 1250239) := by
    rw [show ((1250239 / 1250000) : ℝ) = ((1250000 / 1250239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5727_neg : (95609 / 500000000) ≤ -Real.log (1249761 / 1250000) ∧
    -Real.log (1249761 / 1250000) ≤ (191219 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2499761)) (n := 12)
    (lo := (95609 / 500000000)) (hi := (191219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249761) = 1/(1249761 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5727 : Bounds (-191219 / 1000000000) (-95609 / 500000000) (Real.log (1249761 / 1250000)) := by
  have h := reflection_log_5727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5728_neg : (45875107 / 500000000) ≤ -Real.log (1000000 / 1096091) ∧
    -Real.log (1000000 / 1096091) ≤ (18350043 / 200000000) := by
  have h := checkLog_sound (w := (96091 / 2096091)) (n := 12)
    (lo := (45875107 / 500000000)) (hi := (18350043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096091 / 1000000) = 1/(1000000 / 1096091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5728 : Bounds (45875107 / 500000000) (18350043 / 200000000) (Real.log (1096091 / 1000000)) := by
  have h := reflection_log_5728_neg
  have he : Real.log (1096091 / 1000000) = -Real.log (1000000 / 1096091) := by
    rw [show ((1096091 / 1000000) : ℝ) = ((1000000 / 1096091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5729_neg : (101026587 / 1000000000) ≤ -Real.log (903909 / 1000000) ∧
    -Real.log (903909 / 1000000) ≤ (25256647 / 250000000) := by
  have h := checkLog_sound (w := (96091 / 1903909)) (n := 12)
    (lo := (101026587 / 1000000000)) (hi := (25256647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903909) = 1/(903909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5729 : Bounds (-25256647 / 250000000) (-101026587 / 1000000000) (Real.log (903909 / 1000000)) := by
  have h := reflection_log_5729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5730_neg : (45985487 / 500000000) ≤ -Real.log (1000000 / 1096333) ∧
    -Real.log (1000000 / 1096333) ≤ (3678839 / 40000000) := by
  have h := checkLog_sound (w := (96333 / 2096333)) (n := 12)
    (lo := (45985487 / 500000000)) (hi := (3678839 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096333 / 1000000) = 1/(1000000 / 1096333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5730 : Bounds (45985487 / 500000000) (3678839 / 40000000) (Real.log (1096333 / 1000000)) := by
  have h := reflection_log_5730_neg
  have he : Real.log (1096333 / 1000000) = -Real.log (1000000 / 1096333) := by
    rw [show ((1096333 / 1000000) : ℝ) = ((1000000 / 1096333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5731_neg : (101294349 / 1000000000) ≤ -Real.log (903667 / 1000000) ∧
    -Real.log (903667 / 1000000) ≤ (2025887 / 20000000) := by
  have h := checkLog_sound (w := (96333 / 1903667)) (n := 12)
    (lo := (101294349 / 1000000000)) (hi := (2025887 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903667) = 1/(903667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5731 : Bounds (-2025887 / 20000000) (-101294349 / 1000000000) (Real.log (903667 / 1000000)) := by
  have h := reflection_log_5731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5732_neg : (4661687 / 500000000) ≤ -Real.log (990719953111 / 1000000000000) ∧
    -Real.log (990719953111 / 1000000000000) ≤ (74587 / 8000000) := by
  have h := checkLog_sound (w := (9280046889 / 1990719953111)) (n := 12)
    (lo := (4661687 / 500000000)) (hi := (74587 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990719953111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990719953111) = 1/(990719953111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5732 : Bounds (-74587 / 8000000) (-4661687 / 500000000) (Real.log (990719953111 / 1000000000000)) := by
  have h := reflection_log_5732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5733_neg : (9276373 / 1000000000) ≤ -Real.log (990766519719 / 1000000000000) ∧
    -Real.log (990766519719 / 1000000000000) ≤ (4638187 / 500000000) := by
  have h := checkLog_sound (w := (9233480281 / 1990766519719)) (n := 12)
    (lo := (9276373 / 1000000000)) (hi := (4638187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990766519719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990766519719) = 1/(990766519719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5733 : Bounds (-4638187 / 500000000) (-9276373 / 1000000000) (Real.log (990766519719 / 1000000000000)) := by
  have h := reflection_log_5733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5734_neg : (192776801 / 1000000000) ≤ -Real.log (62500000000 / 75788256893) ∧
    -Real.log (62500000000 / 75788256893) ≤ (96388401 / 500000000) := by
  have h := checkLog_sound (w := (13288256893 / 138288256893)) (n := 12)
    (lo := (192776801 / 1000000000)) (hi := (96388401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75788256893 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75788256893 / 62500000000) = 1/(62500000000 / 75788256893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5734 : Bounds (192776801 / 1000000000) (96388401 / 500000000) (Real.log (75788256893 / 62500000000)) := by
  have h := reflection_log_5734_neg
  have he : Real.log (75788256893 / 62500000000) = -Real.log (62500000000 / 75788256893) := by
    rw [show ((75788256893 / 62500000000) : ℝ) = ((62500000000 / 75788256893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5735_neg : (193265323 / 1000000000) ≤ -Real.log (500000000000 / 606602321431) ∧
    -Real.log (500000000000 / 606602321431) ≤ (48316331 / 250000000) := by
  have h := checkLog_sound (w := (106602321431 / 1106602321431)) (n := 12)
    (lo := (193265323 / 1000000000)) (hi := (48316331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606602321431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606602321431 / 500000000000) = 1/(500000000000 / 606602321431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5735 : Bounds (193265323 / 1000000000) (48316331 / 250000000) (Real.log (606602321431 / 500000000000)) := by
  have h := reflection_log_5735_neg
  have he : Real.log (606602321431 / 500000000000) = -Real.log (500000000000 / 606602321431) := by
    rw [show ((606602321431 / 500000000000) : ℝ) = ((500000000000 / 606602321431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5736_neg : (96739307 / 250000000) ≤ -Real.log (125000000000 / 184061688713) ∧
    -Real.log (125000000000 / 184061688713) ≤ (386957229 / 1000000000) := by
  have h := checkLog_sound (w := (59061688713 / 309061688713)) (n := 12)
    (lo := (96739307 / 250000000)) (hi := (386957229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184061688713 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184061688713 / 125000000000) = 1/(125000000000 / 184061688713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5736 : Bounds (96739307 / 250000000) (386957229 / 1000000000) (Real.log (184061688713 / 125000000000)) := by
  have h := reflection_log_5736_neg
  have he : Real.log (184061688713 / 125000000000) = -Real.log (125000000000 / 184061688713) := by
    rw [show ((184061688713 / 125000000000) : ℝ) = ((125000000000 / 184061688713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5737_neg : (387164813 / 1000000000) ≤ -Real.log (500000000000 / 736399604353) ∧
    -Real.log (500000000000 / 736399604353) ≤ (193582407 / 500000000) := by
  have h := checkLog_sound (w := (236399604353 / 1236399604353)) (n := 12)
    (lo := (387164813 / 1000000000)) (hi := (193582407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736399604353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736399604353 / 500000000000) = 1/(500000000000 / 736399604353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5737 : Bounds (387164813 / 1000000000) (193582407 / 500000000) (Real.log (736399604353 / 500000000000)) := by
  have h := reflection_log_5737_neg
  have he : Real.log (736399604353 / 500000000000) = -Real.log (500000000000 / 736399604353) := by
    rw [show ((736399604353 / 500000000000) : ℝ) = ((500000000000 / 736399604353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5738_neg : (175045147 / 1000000000) ≤ -Real.log (10000 / 11913) ∧
    -Real.log (10000 / 11913) ≤ (43761287 / 250000000) := by
  have h := checkLog_sound (w := (1913 / 21913)) (n := 12)
    (lo := (175045147 / 1000000000)) (hi := (43761287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11913 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11913 / 10000) = 1/(10000 / 11913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5738 : Bounds (175045147 / 1000000000) (43761287 / 250000000) (Real.log (11913 / 10000)) := by
  have h := reflection_log_5738_neg
  have he : Real.log (11913 / 10000) = -Real.log (10000 / 11913) := by
    rw [show ((11913 / 10000) : ℝ) = ((10000 / 11913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5739_neg : (106163629 / 500000000) ≤ -Real.log (8087 / 10000) ∧
    -Real.log (8087 / 10000) ≤ (212327259 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 18087)) (n := 12)
    (lo := (106163629 / 500000000)) (hi := (212327259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8087) = 1/(8087 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5739 : Bounds (-212327259 / 1000000000) (-106163629 / 500000000) (Real.log (8087 / 10000)) := by
  have h := reflection_log_5739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5740_neg : (191281 / 1000000000) ≤ -Real.log (10000000 / 10001913) ∧
    -Real.log (10000000 / 10001913) ≤ (95641 / 500000000) := by
  have h := checkLog_sound (w := (1913 / 20001913)) (n := 12)
    (lo := (191281 / 1000000000)) (hi := (95641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001913 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001913 / 10000000) = 1/(10000000 / 10001913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5740 : Bounds (191281 / 1000000000) (95641 / 500000000) (Real.log (10001913 / 10000000)) := by
  have h := reflection_log_5740_neg
  have he : Real.log (10001913 / 10000000) = -Real.log (10000000 / 10001913) := by
    rw [show ((10001913 / 10000000) : ℝ) = ((10000000 / 10001913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5741_neg : (95659 / 500000000) ≤ -Real.log (9998087 / 10000000) ∧
    -Real.log (9998087 / 10000000) ≤ (191319 / 1000000000) := by
  have h := checkLog_sound (w := (1913 / 19998087)) (n := 12)
    (lo := (95659 / 500000000)) (hi := (191319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998087) = 1/(9998087 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5741 : Bounds (-191319 / 1000000000) (-95659 / 500000000) (Real.log (9998087 / 10000000)) := by
  have h := reflection_log_5741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5742_neg : (45898371 / 500000000) ≤ -Real.log (500000 / 548071) ∧
    -Real.log (500000 / 548071) ≤ (91796743 / 1000000000) := by
  have h := checkLog_sound (w := (48071 / 1048071)) (n := 12)
    (lo := (45898371 / 500000000)) (hi := (91796743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548071 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548071 / 500000) = 1/(500000 / 548071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5742 : Bounds (45898371 / 500000000) (91796743 / 1000000000) (Real.log (548071 / 500000)) := by
  have h := reflection_log_5742_neg
  have he : Real.log (548071 / 500000) = -Real.log (500000 / 548071) := by
    rw [show ((548071 / 500000) : ℝ) = ((500000 / 548071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5743_neg : (10108301 / 100000000) ≤ -Real.log (451929 / 500000) ∧
    -Real.log (451929 / 500000) ≤ (101083011 / 1000000000) := by
  have h := checkLog_sound (w := (48071 / 951929)) (n := 12)
    (lo := (10108301 / 100000000)) (hi := (101083011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451929) = 1/(451929 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5743 : Bounds (-101083011 / 1000000000) (-10108301 / 100000000) (Real.log (451929 / 500000)) := by
  have h := reflection_log_5743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5744_neg : (23004373 / 250000000) ≤ -Real.log (15625 / 17131) ∧
    -Real.log (15625 / 17131) ≤ (92017493 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 16378)) (n := 12)
    (lo := (23004373 / 250000000)) (hi := (92017493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17131 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17131 / 15625) = 1/(15625 / 17131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5744 : Bounds (23004373 / 250000000) (92017493 / 1000000000) (Real.log (17131 / 15625)) := by
  have h := reflection_log_5744_neg
  have he : Real.log (17131 / 15625) = -Real.log (15625 / 17131) := by
    rw [show ((17131 / 15625) : ℝ) = ((15625 / 17131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5745_neg : (101350787 / 1000000000) ≤ -Real.log (14119 / 15625) ∧
    -Real.log (14119 / 15625) ≤ (25337697 / 250000000) := by
  have h := checkLog_sound (w := (753 / 14872)) (n := 12)
    (lo := (101350787 / 1000000000)) (hi := (25337697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14119) = 1/(14119 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5745 : Bounds (-25337697 / 250000000) (-101350787 / 1000000000) (Real.log (14119 / 15625)) := by
  have h := reflection_log_5745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5746_neg : (1866659 / 200000000) ≤ -Real.log (241872589 / 244140625) ∧
    -Real.log (241872589 / 244140625) ≤ (583331 / 62500000) := by
  have h := checkLog_sound (w := (1134018 / 243006607)) (n := 12)
    (lo := (1866659 / 200000000)) (hi := (583331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 241872589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 241872589) = 1/(241872589 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5746 : Bounds (-583331 / 62500000) (-1866659 / 200000000) (Real.log (241872589 / 244140625)) := by
  have h := reflection_log_5746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5747_neg : (2321567 / 250000000) ≤ -Real.log (247689178959 / 250000000000) ∧
    -Real.log (247689178959 / 250000000000) ≤ (9286269 / 1000000000) := by
  have h := checkLog_sound (w := (2310821041 / 497689178959)) (n := 12)
    (lo := (2321567 / 250000000)) (hi := (9286269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247689178959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247689178959) = 1/(247689178959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5747 : Bounds (-9286269 / 1000000000) (-2321567 / 250000000) (Real.log (247689178959 / 250000000000)) := by
  have h := reflection_log_5747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5748_neg : (24109969 / 125000000) ≤ -Real.log (250000000000 / 303184239117) ∧
    -Real.log (250000000000 / 303184239117) ≤ (192879753 / 1000000000) := by
  have h := checkLog_sound (w := (53184239117 / 553184239117)) (n := 12)
    (lo := (24109969 / 125000000)) (hi := (192879753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303184239117 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303184239117 / 250000000000) = 1/(250000000000 / 303184239117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5748 : Bounds (24109969 / 125000000) (192879753 / 1000000000) (Real.log (303184239117 / 250000000000)) := by
  have h := reflection_log_5748_neg
  have he : Real.log (303184239117 / 250000000000) = -Real.log (250000000000 / 303184239117) := by
    rw [show ((303184239117 / 250000000000) : ℝ) = ((250000000000 / 303184239117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5749_neg : (193368279 / 1000000000) ≤ -Real.log (500000000000 / 606664777959) ∧
    -Real.log (500000000000 / 606664777959) ≤ (4834207 / 25000000) := by
  have h := checkLog_sound (w := (106664777959 / 1106664777959)) (n := 12)
    (lo := (193368279 / 1000000000)) (hi := (4834207 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606664777959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606664777959 / 500000000000) = 1/(500000000000 / 606664777959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5749 : Bounds (193368279 / 1000000000) (4834207 / 25000000) (Real.log (606664777959 / 500000000000)) := by
  have h := reflection_log_5749_neg
  have he : Real.log (606664777959 / 500000000000) = -Real.log (500000000000 / 606664777959) := by
    rw [show ((606664777959 / 500000000000) : ℝ) = ((500000000000 / 606664777959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5750_neg : (387164813 / 1000000000) ≤ -Real.log (3906250000 / 5753121909) ∧
    -Real.log (3906250000 / 5753121909) ≤ (193582407 / 500000000) := by
  have h := checkLog_sound (w := (1846871909 / 9659371909)) (n := 12)
    (lo := (387164813 / 1000000000)) (hi := (193582407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5753121909 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5753121909 / 3906250000) = 1/(3906250000 / 5753121909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5750 : Bounds (387164813 / 1000000000) (193582407 / 500000000) (Real.log (5753121909 / 3906250000)) := by
  have h := reflection_log_5750_neg
  have he : Real.log (5753121909 / 3906250000) = -Real.log (3906250000 / 5753121909) := by
    rw [show ((5753121909 / 3906250000) : ℝ) = ((3906250000 / 5753121909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5751_neg : (193686203 / 500000000) ≤ -Real.log (250000000000 / 368276245827) ∧
    -Real.log (250000000000 / 368276245827) ≤ (387372407 / 1000000000) := by
  have h := checkLog_sound (w := (118276245827 / 618276245827)) (n := 12)
    (lo := (193686203 / 500000000)) (hi := (387372407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368276245827 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368276245827 / 250000000000) = 1/(250000000000 / 368276245827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5751 : Bounds (193686203 / 500000000) (387372407 / 1000000000) (Real.log (368276245827 / 250000000000)) := by
  have h := reflection_log_5751_neg
  have he : Real.log (368276245827 / 250000000000) = -Real.log (250000000000 / 368276245827) := by
    rw [show ((368276245827 / 250000000000) : ℝ) = ((250000000000 / 368276245827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5752_neg : (87564543 / 500000000) ≤ -Real.log (5000 / 5957) ∧
    -Real.log (5000 / 5957) ≤ (175129087 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 10957)) (n := 12)
    (lo := (87564543 / 500000000)) (hi := (175129087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5957 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5957 / 5000) = 1/(5000 / 5957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5752 : Bounds (87564543 / 500000000) (175129087 / 1000000000) (Real.log (5957 / 5000)) := by
  have h := reflection_log_5752_neg
  have he : Real.log (5957 / 5000) = -Real.log (5000 / 5957) := by
    rw [show ((5957 / 5000) : ℝ) = ((5000 / 5957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5753_neg : (212450921 / 1000000000) ≤ -Real.log (4043 / 5000) ∧
    -Real.log (4043 / 5000) ≤ (106225461 / 500000000) := by
  have h := checkLog_sound (w := (957 / 9043)) (n := 12)
    (lo := (212450921 / 1000000000)) (hi := (106225461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4043) = 1/(4043 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5753 : Bounds (-106225461 / 500000000) (-212450921 / 1000000000) (Real.log (4043 / 5000)) := by
  have h := reflection_log_5753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5754_neg : (191381 / 1000000000) ≤ -Real.log (5000000 / 5000957) ∧
    -Real.log (5000000 / 5000957) ≤ (95691 / 500000000) := by
  have h := checkLog_sound (w := (957 / 10000957)) (n := 12)
    (lo := (191381 / 1000000000)) (hi := (95691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000957 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000957 / 5000000) = 1/(5000000 / 5000957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5754 : Bounds (191381 / 1000000000) (95691 / 500000000) (Real.log (5000957 / 5000000)) := by
  have h := reflection_log_5754_neg
  have he : Real.log (5000957 / 5000000) = -Real.log (5000000 / 5000957) := by
    rw [show ((5000957 / 5000000) : ℝ) = ((5000000 / 5000957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5755_neg : (95709 / 500000000) ≤ -Real.log (4999043 / 5000000) ∧
    -Real.log (4999043 / 5000000) ≤ (191419 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 9999043)) (n := 12)
    (lo := (95709 / 500000000)) (hi := (191419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999043) = 1/(4999043 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5755 : Bounds (-191419 / 1000000000) (-95709 / 500000000) (Real.log (4999043 / 5000000)) := by
  have h := reflection_log_5755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5756_neg : (91843267 / 1000000000) ≤ -Real.log (1000000 / 1096193) ∧
    -Real.log (1000000 / 1096193) ≤ (22960817 / 250000000) := by
  have h := checkLog_sound (w := (96193 / 2096193)) (n := 12)
    (lo := (91843267 / 1000000000)) (hi := (22960817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096193 / 1000000) = 1/(1000000 / 1096193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5756 : Bounds (91843267 / 1000000000) (22960817 / 250000000) (Real.log (1096193 / 1000000)) := by
  have h := reflection_log_5756_neg
  have he : Real.log (1096193 / 1000000) = -Real.log (1000000 / 1096193) := by
    rw [show ((1096193 / 1000000) : ℝ) = ((1000000 / 1096193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5757_neg : (25284859 / 250000000) ≤ -Real.log (903807 / 1000000) ∧
    -Real.log (903807 / 1000000) ≤ (101139437 / 1000000000) := by
  have h := checkLog_sound (w := (96193 / 1903807)) (n := 12)
    (lo := (25284859 / 250000000)) (hi := (101139437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903807) = 1/(903807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5757 : Bounds (-101139437 / 1000000000) (-25284859 / 250000000) (Real.log (903807 / 1000000)) := by
  have h := reflection_log_5757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5758_neg : (92064007 / 1000000000) ≤ -Real.log (200000 / 219287) ∧
    -Real.log (200000 / 219287) ≤ (11508001 / 125000000) := by
  have h := checkLog_sound (w := (19287 / 419287)) (n := 12)
    (lo := (92064007 / 1000000000)) (hi := (11508001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219287 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219287 / 200000) = 1/(200000 / 219287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5758 : Bounds (92064007 / 1000000000) (11508001 / 125000000) (Real.log (219287 / 200000)) := by
  have h := reflection_log_5758_neg
  have he : Real.log (219287 / 200000) = -Real.log (200000 / 219287) := by
    rw [show ((219287 / 200000) : ℝ) = ((200000 / 219287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5759_neg : (101407229 / 1000000000) ≤ -Real.log (180713 / 200000) ∧
    -Real.log (180713 / 200000) ≤ (10140723 / 100000000) := by
  have h := checkLog_sound (w := (19287 / 380713)) (n := 12)
    (lo := (101407229 / 1000000000)) (hi := (10140723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180713) = 1/(180713 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5759 : Bounds (-10140723 / 100000000) (-101407229 / 1000000000) (Real.log (180713 / 200000)) := by
  have h := reflection_log_5759_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
