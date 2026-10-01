import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15616_neg : (6212606091 / 1000000000) ≤ -Real.log (1 / 499) ∧
    -Real.log (1 / 499) ≤ (62126061 / 10000000) := by
  have h := checkLog_sound (w := (243 / 755)) (n := 12)
    (lo := (667428651 / 1000000000)) (hi := (166857163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 256) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(499 / 256) = 1/(1 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15616 : Bounds (6212606091 / 1000000000) (62126061 / 10000000) (Real.log (499 / 1)) := by
  have h := reflection_log_15616_neg
  have he : Real.log (499 / 1) = -Real.log (1 / 499) := by
    rw [show ((499 / 1) : ℝ) = ((1 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15617_neg : (691245373 / 1000000000) ≤ -Real.log (5000 / 9981) ∧
    -Real.log (5000 / 9981) ≤ (345622687 / 500000000) := by
  have h := checkLog_sound (w := (4981 / 14981)) (n := 12)
    (lo := (691245373 / 1000000000)) (hi := (345622687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9981 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9981 / 5000) = 1/(5000 / 9981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15617 : Bounds (691245373 / 1000000000) (345622687 / 500000000) (Real.log (9981 / 5000)) := by
  have h := reflection_log_15617_neg
  have he : Real.log (9981 / 5000) = -Real.log (5000 / 9981) := by
    rw [show ((9981 / 5000) : ℝ) = ((5000 / 9981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15618_neg : (5572754207 / 1000000000) ≤ -Real.log (19 / 5000) ∧
    -Real.log (19 / 5000) ≤ (696594277 / 125000000) := by
  have h := checkLog_sound (w := (17 / 1233)) (n := 12)
    (lo := (27576767 / 1000000000)) (hi := (430887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 608) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 608) = 1/(19 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15618 : Bounds (-696594277 / 125000000) (-5572754207 / 1000000000) (Real.log (19 / 5000)) := by
  have h := reflection_log_15618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15619_neg : (124463 / 125000000) ≤ -Real.log (5000000 / 5004981) ∧
    -Real.log (5000000 / 5004981) ≤ (199141 / 200000000) := by
  have h := checkLog_sound (w := (4981 / 10004981)) (n := 12)
    (lo := (124463 / 125000000)) (hi := (199141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004981 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004981 / 5000000) = 1/(5000000 / 5004981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15619 : Bounds (124463 / 125000000) (199141 / 200000000) (Real.log (5004981 / 5000000)) := by
  have h := reflection_log_15619_neg
  have he : Real.log (5004981 / 5000000) = -Real.log (5000000 / 5004981) := by
    rw [show ((5004981 / 5000000) : ℝ) = ((5000000 / 5004981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15620_neg : (124587 / 125000000) ≤ -Real.log (4995019 / 5000000) ∧
    -Real.log (4995019 / 5000000) ≤ (996697 / 1000000000) := by
  have h := checkLog_sound (w := (4981 / 9995019)) (n := 12)
    (lo := (124587 / 125000000)) (hi := (996697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995019) = 1/(4995019 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15620 : Bounds (-996697 / 1000000000) (-124587 / 125000000) (Real.log (4995019 / 5000000)) := by
  have h := reflection_log_15620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15621_neg : (501383587 / 1000000000) ≤ -Real.log (250000 / 412751) ∧
    -Real.log (250000 / 412751) ≤ (125345897 / 250000000) := by
  have h := checkLog_sound (w := (162751 / 662751)) (n := 12)
    (lo := (501383587 / 1000000000)) (hi := (125345897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412751 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412751 / 250000) = 1/(250000 / 412751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15621 : Bounds (501383587 / 1000000000) (125345897 / 250000000) (Real.log (412751 / 250000)) := by
  have h := reflection_log_15621_neg
  have he : Real.log (412751 / 250000) = -Real.log (250000 / 412751) := by
    rw [show ((412751 / 250000) : ℝ) = ((250000 / 412751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15622_neg : (1052694817 / 1000000000) ≤ -Real.log (87249 / 250000) ∧
    -Real.log (87249 / 250000) ≤ (1052694819 / 1000000000) := by
  have h := checkLog_sound (w := (37751 / 212249)) (n := 12)
    (lo := (359547637 / 1000000000)) (hi := (179773819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 87249) = 1/(87249 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15622 : Bounds (-1052694819 / 1000000000) (-1052694817 / 1000000000) (Real.log (87249 / 250000)) := by
  have h := reflection_log_15622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15623_neg : (501964277 / 1000000000) ≤ -Real.log (1000000 / 1651963) ∧
    -Real.log (1000000 / 1651963) ≤ (250982139 / 500000000) := by
  have h := checkLog_sound (w := (651963 / 2651963)) (n := 12)
    (lo := (501964277 / 1000000000)) (hi := (250982139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651963 / 1000000) = 1/(1000000 / 1651963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15623 : Bounds (501964277 / 1000000000) (250982139 / 500000000) (Real.log (1651963 / 1000000)) := by
  have h := reflection_log_15623_neg
  have he : Real.log (1651963 / 1000000) = -Real.log (1000000 / 1651963) := by
    rw [show ((1651963 / 1000000) : ℝ) = ((1000000 / 1651963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15624_neg : (527723241 / 500000000) ≤ -Real.log (348037 / 1000000) ∧
    -Real.log (348037 / 1000000) ≤ (263861621 / 250000000) := by
  have h := checkLog_sound (w := (151963 / 848037)) (n := 12)
    (lo := (181149651 / 500000000)) (hi := (362299303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348037) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348037) = 1/(348037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15624 : Bounds (-263861621 / 250000000) (-527723241 / 500000000) (Real.log (348037 / 1000000)) := by
  have h := reflection_log_15624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15625_neg : (110696441 / 200000000) ≤ -Real.log (574944246631 / 1000000000000) ∧
    -Real.log (574944246631 / 1000000000000) ≤ (276741103 / 500000000) := by
  have h := checkLog_sound (w := (425055753369 / 1574944246631)) (n := 12)
    (lo := (110696441 / 200000000)) (hi := (276741103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 574944246631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 574944246631) = 1/(574944246631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15625 : Bounds (-276741103 / 500000000) (-110696441 / 200000000) (Real.log (574944246631 / 1000000000000)) := by
  have h := reflection_log_15625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15626_neg : (55131123 / 100000000) ≤ -Real.log (36012111999 / 62500000000) ∧
    -Real.log (36012111999 / 62500000000) ≤ (551311231 / 1000000000) := by
  have h := checkLog_sound (w := (26487888001 / 98512111999)) (n := 12)
    (lo := (55131123 / 100000000)) (hi := (551311231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36012111999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36012111999) = 1/(36012111999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15626 : Bounds (-551311231 / 1000000000) (-55131123 / 100000000) (Real.log (36012111999 / 62500000000)) := by
  have h := reflection_log_15626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15627_neg : (388519601 / 250000000) ≤ -Real.log (500000000000 / 2365362353723) ∧
    -Real.log (500000000000 / 2365362353723) ≤ (1554078407 / 1000000000) := by
  have h := checkLog_sound (w := (365362353723 / 4365362353723)) (n := 12)
    (lo := (41946011 / 250000000)) (hi := (33556809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365362353723 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365362353723 / 2000000000000) = 1/(500000000000 / 2365362353723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15627 : Bounds (388519601 / 250000000) (1554078407 / 1000000000) (Real.log (2365362353723 / 500000000000)) := by
  have h := reflection_log_15627_neg
  have he : Real.log (2365362353723 / 500000000000) = -Real.log (500000000000 / 2365362353723) := by
    rw [show ((2365362353723 / 500000000000) : ℝ) = ((500000000000 / 2365362353723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15628_neg : (1557410759 / 1000000000) ≤ -Real.log (100000000000 / 474651545669) ∧
    -Real.log (100000000000 / 474651545669) ≤ (778705381 / 500000000) := by
  have h := checkLog_sound (w := (74651545669 / 874651545669)) (n := 12)
    (lo := (171116399 / 1000000000)) (hi := (427791 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474651545669 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(474651545669 / 400000000000) = 1/(100000000000 / 474651545669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15628 : Bounds (1557410759 / 1000000000) (778705381 / 500000000) (Real.log (474651545669 / 100000000000)) := by
  have h := reflection_log_15628_neg
  have he : Real.log (474651545669 / 100000000000) = -Real.log (100000000000 / 474651545669) := by
    rw [show ((474651545669 / 100000000000) : ℝ) = ((100000000000 / 474651545669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15629_neg : (313199979 / 50000000) ≤ -Real.log (500000000000 / 262657894736843) ∧
    -Real.log (500000000000 / 262657894736843) ≤ (626399959 / 100000000) := by
  have h := checkLog_sound (w := (6657894736843 / 518657894736843)) (n := 12)
    (lo := (320937 / 12500000)) (hi := (25674961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262657894736843 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(262657894736843 / 256000000000000) = 1/(500000000000 / 262657894736843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15629 : Bounds (313199979 / 50000000) (626399959 / 100000000) (Real.log (262657894736843 / 500000000000)) := by
  have h := reflection_log_15629_neg
  have he : Real.log (262657894736843 / 500000000000) = -Real.log (500000000000 / 262657894736843) := by
    rw [show ((262657894736843 / 500000000000) : ℝ) = ((500000000000 / 262657894736843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15630_neg : (345672779 / 500000000) ≤ -Real.log (2500 / 4991) ∧
    -Real.log (2500 / 4991) ≤ (691345559 / 1000000000) := by
  have h := checkLog_sound (w := (2491 / 7491)) (n := 12)
    (lo := (345672779 / 500000000)) (hi := (691345559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4991 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4991 / 2500) = 1/(2500 / 4991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15630 : Bounds (345672779 / 500000000) (691345559 / 1000000000) (Real.log (4991 / 2500)) := by
  have h := reflection_log_15630_neg
  have he : Real.log (4991 / 2500) = -Real.log (2500 / 4991) := by
    rw [show ((4991 / 2500) : ℝ) = ((2500 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15631_neg : (5626821429 / 1000000000) ≤ -Real.log (9 / 2500) ∧
    -Real.log (9 / 2500) ≤ (2813410719 / 500000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 576) = 1/(9 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15631 : Bounds (-2813410719 / 500000000) (-5626821429 / 1000000000) (Real.log (9 / 2500)) := by
  have h := reflection_log_15631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15632_neg : (995903 / 1000000000) ≤ -Real.log (2500000 / 2502491) ∧
    -Real.log (2500000 / 2502491) ≤ (15561 / 15625000) := by
  have h := checkLog_sound (w := (2491 / 5002491)) (n := 12)
    (lo := (995903 / 1000000000)) (hi := (15561 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502491 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502491 / 2500000) = 1/(2500000 / 2502491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15632 : Bounds (995903 / 1000000000) (15561 / 15625000) (Real.log (2502491 / 2500000)) := by
  have h := reflection_log_15632_neg
  have he : Real.log (2502491 / 2500000) = -Real.log (2500000 / 2502491) := by
    rw [show ((2502491 / 2500000) : ℝ) = ((2500000 / 2502491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15633_neg : (31153 / 31250000) ≤ -Real.log (2497509 / 2500000) ∧
    -Real.log (2497509 / 2500000) ≤ (996897 / 1000000000) := by
  have h := checkLog_sound (w := (2491 / 4997509)) (n := 12)
    (lo := (31153 / 31250000)) (hi := (996897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497509) = 1/(2497509 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15633 : Bounds (-996897 / 1000000000) (-31153 / 31250000) (Real.log (2497509 / 2500000)) := by
  have h := reflection_log_15633_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15634_neg : (100317537 / 200000000) ≤ -Real.log (1000000 / 1651341) ∧
    -Real.log (1000000 / 1651341) ≤ (250793843 / 500000000) := by
  have h := checkLog_sound (w := (651341 / 2651341)) (n := 12)
    (lo := (100317537 / 200000000)) (hi := (250793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651341 / 1000000) = 1/(1000000 / 1651341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15634 : Bounds (100317537 / 200000000) (250793843 / 500000000) (Real.log (1651341 / 1000000)) := by
  have h := reflection_log_15634_neg
  have he : Real.log (1651341 / 1000000) = -Real.log (1000000 / 1651341) := by
    rw [show ((1651341 / 1000000) : ℝ) = ((1000000 / 1651341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15635_neg : (1053660911 / 1000000000) ≤ -Real.log (348659 / 1000000) ∧
    -Real.log (348659 / 1000000) ≤ (1053660913 / 1000000000) := by
  have h := checkLog_sound (w := (151341 / 848659)) (n := 12)
    (lo := (360513731 / 1000000000)) (hi := (90128433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348659) = 1/(348659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15635 : Bounds (-1053660913 / 1000000000) (-1053660911 / 1000000000) (Real.log (348659 / 1000000)) := by
  have h := reflection_log_15635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15636_neg : (502169467 / 1000000000) ≤ -Real.log (500000 / 826151) ∧
    -Real.log (500000 / 826151) ≤ (125542367 / 250000000) := by
  have h := checkLog_sound (w := (326151 / 1326151)) (n := 12)
    (lo := (502169467 / 1000000000)) (hi := (125542367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826151 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826151 / 500000) = 1/(500000 / 826151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15636 : Bounds (502169467 / 1000000000) (125542367 / 250000000) (Real.log (826151 / 500000)) := by
  have h := reflection_log_15636_neg
  have he : Real.log (826151 / 500000) = -Real.log (500000 / 826151) := by
    rw [show ((826151 / 500000) : ℝ) = ((500000 / 826151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15637_neg : (1056420991 / 1000000000) ≤ -Real.log (173849 / 500000) ∧
    -Real.log (173849 / 500000) ≤ (1056420993 / 1000000000) := by
  have h := checkLog_sound (w := (76151 / 423849)) (n := 12)
    (lo := (363273811 / 1000000000)) (hi := (90818453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173849) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173849) = 1/(173849 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15637 : Bounds (-1056420993 / 1000000000) (-1056420991 / 1000000000) (Real.log (173849 / 500000)) := by
  have h := reflection_log_15637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15638_neg : (138562881 / 250000000) ≤ -Real.log (143625525199 / 250000000000) ∧
    -Real.log (143625525199 / 250000000000) ≤ (22170061 / 40000000) := by
  have h := checkLog_sound (w := (106374474801 / 393625525199)) (n := 12)
    (lo := (138562881 / 250000000)) (hi := (22170061 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143625525199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143625525199) = 1/(143625525199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15638 : Bounds (-22170061 / 40000000) (-138562881 / 250000000) (Real.log (143625525199 / 250000000000)) := by
  have h := reflection_log_15638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15639_neg : (276036613 / 500000000) ≤ -Real.log (575754901719 / 1000000000000) ∧
    -Real.log (575754901719 / 1000000000000) ≤ (552073227 / 1000000000) := by
  have h := checkLog_sound (w := (424245098281 / 1575754901719)) (n := 12)
    (lo := (276036613 / 500000000)) (hi := (552073227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575754901719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575754901719) = 1/(575754901719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15639 : Bounds (-552073227 / 1000000000) (-276036613 / 500000000) (Real.log (575754901719 / 1000000000000)) := by
  have h := reflection_log_15639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15640_neg : (311049719 / 200000000) ≤ -Real.log (500000000000 / 2368131899649) ∧
    -Real.log (500000000000 / 2368131899649) ≤ (777624299 / 500000000) := by
  have h := checkLog_sound (w := (368131899649 / 4368131899649)) (n := 12)
    (lo := (33790847 / 200000000)) (hi := (42238559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2368131899649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2368131899649 / 2000000000000) = 1/(500000000000 / 2368131899649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15640 : Bounds (311049719 / 200000000) (777624299 / 500000000) (Real.log (2368131899649 / 500000000000)) := by
  have h := reflection_log_15640_neg
  have he : Real.log (2368131899649 / 500000000000) = -Real.log (500000000000 / 2368131899649) := by
    rw [show ((2368131899649 / 500000000000) : ℝ) = ((500000000000 / 2368131899649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15641_neg : (779295229 / 500000000) ≤ -Real.log (500000000000 / 2376059108767) ∧
    -Real.log (500000000000 / 2376059108767) ≤ (1558590461 / 1000000000) := by
  have h := checkLog_sound (w := (376059108767 / 4376059108767)) (n := 12)
    (lo := (86148049 / 500000000)) (hi := (172296099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2376059108767 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2376059108767 / 2000000000000) = 1/(500000000000 / 2376059108767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15641 : Bounds (779295229 / 500000000) (1558590461 / 1000000000) (Real.log (2376059108767 / 500000000000)) := by
  have h := reflection_log_15641_neg
  have he : Real.log (2376059108767 / 500000000000) = -Real.log (500000000000 / 2376059108767) := by
    rw [show ((2376059108767 / 500000000000) : ℝ) = ((500000000000 / 2376059108767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15642_neg : (313199979 / 50000000) ≤ -Real.log (250000000000 / 131328947368421) ∧
    -Real.log (250000000000 / 131328947368421) ≤ (626399959 / 100000000) := by
  have h := checkLog_sound (w := (3328947368421 / 259328947368421)) (n := 12)
    (lo := (320937 / 12500000)) (hi := (25674961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131328947368421 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(131328947368421 / 128000000000000) = 1/(250000000000 / 131328947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15642 : Bounds (313199979 / 50000000) (626399959 / 100000000) (Real.log (131328947368421 / 250000000000)) := by
  have h := reflection_log_15642_neg
  have he : Real.log (131328947368421 / 250000000000) = -Real.log (250000000000 / 131328947368421) := by
    rw [show ((131328947368421 / 250000000000) : ℝ) = ((250000000000 / 131328947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15643_neg : (6318166987 / 1000000000) ≤ -Real.log (250000000000 / 138638888888889) ∧
    -Real.log (250000000000 / 138638888888889) ≤ (6318166997 / 1000000000) := by
  have h := checkLog_sound (w := (10638888888889 / 266638888888889)) (n := 12)
    (lo := (79842367 / 1000000000)) (hi := (1247537 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138638888888889 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(138638888888889 / 128000000000000) = 1/(250000000000 / 138638888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15643 : Bounds (6318166987 / 1000000000) (6318166997 / 1000000000) (Real.log (138638888888889 / 250000000000)) := by
  have h := reflection_log_15643_neg
  have he : Real.log (138638888888889 / 250000000000) = -Real.log (250000000000 / 138638888888889) := by
    rw [show ((138638888888889 / 250000000000) : ℝ) = ((250000000000 / 138638888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15644_neg : (691445733 / 1000000000) ≤ -Real.log (5000 / 9983) ∧
    -Real.log (5000 / 9983) ≤ (345722867 / 500000000) := by
  have h := checkLog_sound (w := (4983 / 14983)) (n := 12)
    (lo := (691445733 / 1000000000)) (hi := (345722867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9983 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9983 / 5000) = 1/(5000 / 9983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15644 : Bounds (691445733 / 1000000000) (345722867 / 500000000) (Real.log (9983 / 5000)) := by
  have h := reflection_log_15644_neg
  have he : Real.log (9983 / 5000) = -Real.log (5000 / 9983) := by
    rw [show ((9983 / 5000) : ℝ) = ((5000 / 9983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15645_neg : (2841989921 / 500000000) ≤ -Real.log (17 / 5000) ∧
    -Real.log (17 / 5000) ≤ (5683979851 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1169)) (n := 12)
    (lo := (69401201 / 500000000)) (hi := (138802403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 544) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 544) = 1/(17 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15645 : Bounds (-5683979851 / 1000000000) (-2841989921 / 500000000) (Real.log (17 / 5000)) := by
  have h := reflection_log_15645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15646_neg : (996103 / 1000000000) ≤ -Real.log (5000000 / 5004983) ∧
    -Real.log (5000000 / 5004983) ≤ (124513 / 125000000) := by
  have h := checkLog_sound (w := (4983 / 10004983)) (n := 12)
    (lo := (996103 / 1000000000)) (hi := (124513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004983 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004983 / 5000000) = 1/(5000000 / 5004983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15646 : Bounds (996103 / 1000000000) (124513 / 125000000) (Real.log (5004983 / 5000000)) := by
  have h := reflection_log_15646_neg
  have he : Real.log (5004983 / 5000000) = -Real.log (5000000 / 5004983) := by
    rw [show ((5004983 / 5000000) : ℝ) = ((5000000 / 5004983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15647_neg : (124637 / 125000000) ≤ -Real.log (4995017 / 5000000) ∧
    -Real.log (4995017 / 5000000) ≤ (997097 / 1000000000) := by
  have h := checkLog_sound (w := (4983 / 9995017)) (n := 12)
    (lo := (124637 / 125000000)) (hi := (997097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995017) = 1/(4995017 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15647 : Bounds (-997097 / 1000000000) (-124637 / 125000000) (Real.log (4995017 / 5000000)) := by
  have h := reflection_log_15647_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15648_neg : (501792951 / 1000000000) ≤ -Real.log (6250 / 10323) ∧
    -Real.log (6250 / 10323) ≤ (62724119 / 125000000) := by
  have h := checkLog_sound (w := (4073 / 16573)) (n := 12)
    (lo := (501792951 / 1000000000)) (hi := (62724119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10323 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10323 / 6250) = 1/(6250 / 10323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15648 : Bounds (501792951 / 1000000000) (62724119 / 125000000) (Real.log (10323 / 6250)) := by
  have h := reflection_log_15648_neg
  have he : Real.log (10323 / 6250) = -Real.log (6250 / 10323) := by
    rw [show ((10323 / 6250) : ℝ) = ((6250 / 10323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15649_neg : (13182921 / 12500000) ≤ -Real.log (2177 / 6250) ∧
    -Real.log (2177 / 6250) ≤ (527316841 / 500000000) := by
  have h := checkLog_sound (w := (474 / 2651)) (n := 12)
    (lo := (722973 / 2000000)) (hi := (361486501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2177) = 1/(2177 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15649 : Bounds (-527316841 / 500000000) (-13182921 / 12500000) (Real.log (2177 / 6250)) := by
  have h := reflection_log_15649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15650_neg : (502376429 / 1000000000) ≤ -Real.log (250000 / 413161) ∧
    -Real.log (250000 / 413161) ≤ (50237643 / 100000000) := by
  have h := checkLog_sound (w := (163161 / 663161)) (n := 12)
    (lo := (502376429 / 1000000000)) (hi := (50237643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413161 / 250000) = 1/(250000 / 413161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15650 : Bounds (502376429 / 1000000000) (50237643 / 100000000) (Real.log (413161 / 250000)) := by
  have h := reflection_log_15650_neg
  have he : Real.log (413161 / 250000) = -Real.log (250000 / 413161) := by
    rw [show ((413161 / 250000) : ℝ) = ((250000 / 413161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15651_neg : (1057405087 / 1000000000) ≤ -Real.log (86839 / 250000) ∧
    -Real.log (86839 / 250000) ≤ (1057405089 / 1000000000) := by
  have h := checkLog_sound (w := (38161 / 211839)) (n := 12)
    (lo := (364257907 / 1000000000)) (hi := (91064477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86839) = 1/(86839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15651 : Bounds (-1057405089 / 1000000000) (-1057405087 / 1000000000) (Real.log (86839 / 250000)) := by
  have h := reflection_log_15651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15652_neg : (277514329 / 500000000) ≤ -Real.log (35878488079 / 62500000000) ∧
    -Real.log (35878488079 / 62500000000) ≤ (555028659 / 1000000000) := by
  have h := checkLog_sound (w := (26621511921 / 98378488079)) (n := 12)
    (lo := (277514329 / 500000000)) (hi := (555028659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35878488079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35878488079) = 1/(35878488079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15652 : Bounds (-555028659 / 1000000000) (-277514329 / 500000000) (Real.log (35878488079 / 62500000000)) := by
  have h := reflection_log_15652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15653_neg : (552840729 / 1000000000) ≤ -Real.log (22473171 / 39062500) ∧
    -Real.log (22473171 / 39062500) ≤ (55284073 / 100000000) := by
  have h := checkLog_sound (w := (16589329 / 61535671)) (n := 12)
    (lo := (552840729 / 1000000000)) (hi := (55284073 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 22473171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 22473171) = 1/(22473171 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15653 : Bounds (-55284073 / 100000000) (-552840729 / 1000000000) (Real.log (22473171 / 39062500)) := by
  have h := reflection_log_15653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15654_neg : (194553329 / 125000000) ≤ -Real.log (500000000000 / 2370923288929) ∧
    -Real.log (500000000000 / 2370923288929) ≤ (311285327 / 200000000) := by
  have h := checkLog_sound (w := (370923288929 / 4370923288929)) (n := 12)
    (lo := (10633267 / 62500000)) (hi := (170132273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2370923288929 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2370923288929 / 2000000000000) = 1/(500000000000 / 2370923288929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15654 : Bounds (194553329 / 125000000) (311285327 / 200000000) (Real.log (2370923288929 / 500000000000)) := by
  have h := reflection_log_15654_neg
  have he : Real.log (2370923288929 / 500000000000) = -Real.log (500000000000 / 2370923288929) := by
    rw [show ((2370923288929 / 500000000000) : ℝ) = ((500000000000 / 2370923288929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15655_neg : (389945379 / 250000000) ≤ -Real.log (100000000000 / 475778164189) ∧
    -Real.log (100000000000 / 475778164189) ≤ (1559781519 / 1000000000) := by
  have h := checkLog_sound (w := (75778164189 / 875778164189)) (n := 12)
    (lo := (43371789 / 250000000)) (hi := (173487157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475778164189 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(475778164189 / 400000000000) = 1/(100000000000 / 475778164189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15655 : Bounds (389945379 / 250000000) (1559781519 / 1000000000) (Real.log (475778164189 / 100000000000)) := by
  have h := reflection_log_15655_neg
  have he : Real.log (475778164189 / 100000000000) = -Real.log (100000000000 / 475778164189) := by
    rw [show ((475778164189 / 100000000000) : ℝ) = ((100000000000 / 475778164189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15656_neg : (6318166987 / 1000000000) ≤ -Real.log (500000000000 / 277277777777777) ∧
    -Real.log (500000000000 / 277277777777777) ≤ (6318166997 / 1000000000) := by
  have h := checkLog_sound (w := (21277777777777 / 533277777777777)) (n := 12)
    (lo := (79842367 / 1000000000)) (hi := (1247537 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277277777777777 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(277277777777777 / 256000000000000) = 1/(500000000000 / 277277777777777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15656 : Bounds (6318166987 / 1000000000) (6318166997 / 1000000000) (Real.log (277277777777777 / 500000000000)) := by
  have h := reflection_log_15656_neg
  have he : Real.log (277277777777777 / 500000000000) = -Real.log (500000000000 / 277277777777777) := by
    rw [show ((277277777777777 / 500000000000) : ℝ) = ((500000000000 / 277277777777777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15657_neg : (796928197 / 125000000) ≤ -Real.log (62500000000 / 36702205882353) ∧
    -Real.log (62500000000 / 36702205882353) ≤ (3187712793 / 500000000) := by
  have h := checkLog_sound (w := (4702205882353 / 68702205882353)) (n := 12)
    (lo := (34275239 / 250000000)) (hi := (137100957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36702205882353 / 32000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(36702205882353 / 32000000000000) = 1/(62500000000 / 36702205882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15657 : Bounds (796928197 / 125000000) (3187712793 / 500000000) (Real.log (36702205882353 / 62500000000)) := by
  have h := reflection_log_15657_neg
  have he : Real.log (36702205882353 / 62500000000) = -Real.log (62500000000 / 36702205882353) := by
    rw [show ((36702205882353 / 62500000000) : ℝ) = ((62500000000 / 36702205882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15658_neg : (691545899 / 1000000000) ≤ -Real.log (625 / 1248) ∧
    -Real.log (625 / 1248) ≤ (6915459 / 10000000) := by
  have h := checkLog_sound (w := (623 / 1873)) (n := 12)
    (lo := (691545899 / 1000000000)) (hi := (6915459 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248 / 625) = 1/(625 / 1248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15658 : Bounds (691545899 / 1000000000) (6915459 / 10000000) (Real.log (1248 / 625)) := by
  have h := reflection_log_15658_neg
  have he : Real.log (1248 / 625) = -Real.log (625 / 1248) := by
    rw [show ((1248 / 625) : ℝ) = ((625 / 1248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15659_neg : (359037779 / 62500000) ≤ -Real.log (2 / 625) ∧
    -Real.log (2 / 625) ≤ (5744604473 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 512) = 1/(2 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15659 : Bounds (-5744604473 / 1000000000) (-359037779 / 62500000) (Real.log (2 / 625)) := by
  have h := reflection_log_15659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15660_neg : (996303 / 1000000000) ≤ -Real.log (625000 / 625623) ∧
    -Real.log (625000 / 625623) ≤ (62269 / 62500000) := by
  have h := checkLog_sound (w := (623 / 1250623)) (n := 12)
    (lo := (996303 / 1000000000)) (hi := (62269 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625623 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625623 / 625000) = 1/(625000 / 625623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15660 : Bounds (996303 / 1000000000) (62269 / 62500000) (Real.log (625623 / 625000)) := by
  have h := reflection_log_15660_neg
  have he : Real.log (625623 / 625000) = -Real.log (625000 / 625623) := by
    rw [show ((625623 / 625000) : ℝ) = ((625000 / 625623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15661_neg : (997297 / 1000000000) ≤ -Real.log (624377 / 625000) ∧
    -Real.log (624377 / 625000) ≤ (498649 / 500000000) := by
  have h := checkLog_sound (w := (623 / 1249377)) (n := 12)
    (lo := (997297 / 1000000000)) (hi := (498649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624377) = 1/(624377 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15661 : Bounds (-498649 / 500000000) (-997297 / 1000000000) (Real.log (624377 / 625000)) := by
  have h := reflection_log_15661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15662_neg : (250999693 / 500000000) ≤ -Real.log (1000000 / 1652021) ∧
    -Real.log (1000000 / 1652021) ≤ (501999387 / 1000000000) := by
  have h := checkLog_sound (w := (652021 / 2652021)) (n := 12)
    (lo := (250999693 / 500000000)) (hi := (501999387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1652021 / 1000000) = 1/(1000000 / 1652021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15662 : Bounds (250999693 / 500000000) (501999387 / 1000000000) (Real.log (1652021 / 1000000)) := by
  have h := reflection_log_15662_neg
  have he : Real.log (1652021 / 1000000) = -Real.log (1000000 / 1652021) := by
    rw [show ((1652021 / 1000000) : ℝ) = ((1000000 / 1652021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15663_neg : (211122629 / 200000000) ≤ -Real.log (347979 / 1000000) ∧
    -Real.log (347979 / 1000000) ≤ (1055613147 / 1000000000) := by
  have h := checkLog_sound (w := (152021 / 847979)) (n := 12)
    (lo := (72493193 / 200000000)) (hi := (181232983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 347979) = 1/(347979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15663 : Bounds (-1055613147 / 1000000000) (-211122629 / 200000000) (Real.log (347979 / 1000000)) := by
  have h := reflection_log_15663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15664_neg : (502584559 / 1000000000) ≤ -Real.log (250000 / 413247) ∧
    -Real.log (250000 / 413247) ≤ (6282307 / 12500000) := by
  have h := checkLog_sound (w := (163247 / 663247)) (n := 12)
    (lo := (502584559 / 1000000000)) (hi := (6282307 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413247 / 250000) = 1/(250000 / 413247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15664 : Bounds (502584559 / 1000000000) (6282307 / 12500000) (Real.log (413247 / 250000)) := by
  have h := reflection_log_15664_neg
  have he : Real.log (413247 / 250000) = -Real.log (250000 / 413247) := by
    rw [show ((413247 / 250000) : ℝ) = ((250000 / 413247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15665_neg : (264598979 / 250000000) ≤ -Real.log (86753 / 250000) ∧
    -Real.log (86753 / 250000) ≤ (529197959 / 500000000) := by
  have h := checkLog_sound (w := (38247 / 211753)) (n := 12)
    (lo := (11414023 / 31250000)) (hi := (365248737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86753) = 1/(86753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15665 : Bounds (-529197959 / 500000000) (-264598979 / 250000000) (Real.log (86753 / 250000)) := by
  have h := reflection_log_15665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15666_neg : (277905679 / 500000000) ≤ -Real.log (35850416991 / 62500000000) ∧
    -Real.log (35850416991 / 62500000000) ≤ (555811359 / 1000000000) := by
  have h := checkLog_sound (w := (26649583009 / 98350416991)) (n := 12)
    (lo := (277905679 / 500000000)) (hi := (555811359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35850416991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35850416991) = 1/(35850416991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15666 : Bounds (-555811359 / 1000000000) (-277905679 / 500000000) (Real.log (35850416991 / 62500000000)) := by
  have h := reflection_log_15666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15667_neg : (276806879 / 500000000) ≤ -Real.log (574868615559 / 1000000000000) ∧
    -Real.log (574868615559 / 1000000000000) ≤ (553613759 / 1000000000) := by
  have h := checkLog_sound (w := (425131384441 / 1574868615559)) (n := 12)
    (lo := (276806879 / 500000000)) (hi := (553613759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 574868615559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 574868615559) = 1/(574868615559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15667 : Bounds (-553613759 / 1000000000) (-276806879 / 500000000) (Real.log (574868615559 / 1000000000000)) := by
  have h := reflection_log_15667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15668_neg : (1557612531 / 1000000000) ≤ -Real.log (125000000000 / 593434158383) ∧
    -Real.log (125000000000 / 593434158383) ≤ (778806267 / 500000000) := by
  have h := checkLog_sound (w := (93434158383 / 1093434158383)) (n := 12)
    (lo := (171318171 / 1000000000)) (hi := (42829543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593434158383 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(593434158383 / 500000000000) = 1/(125000000000 / 593434158383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15668 : Bounds (1557612531 / 1000000000) (778806267 / 500000000) (Real.log (593434158383 / 125000000000)) := by
  have h := reflection_log_15668_neg
  have he : Real.log (593434158383 / 125000000000) = -Real.log (125000000000 / 593434158383) := by
    rw [show ((593434158383 / 125000000000) : ℝ) = ((125000000000 / 593434158383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15669_neg : (62439219 / 40000000) ≤ -Real.log (250000000000 / 1190872361763) ∧
    -Real.log (250000000000 / 1190872361763) ≤ (780490239 / 500000000) := by
  have h := checkLog_sound (w := (190872361763 / 2190872361763)) (n := 12)
    (lo := (34937223 / 200000000)) (hi := (43671529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190872361763 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1190872361763 / 1000000000000) = 1/(250000000000 / 1190872361763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15669 : Bounds (62439219 / 40000000) (780490239 / 500000000) (Real.log (1190872361763 / 250000000000)) := by
  have h := reflection_log_15669_neg
  have he : Real.log (1190872361763 / 250000000000) = -Real.log (250000000000 / 1190872361763) := by
    rw [show ((1190872361763 / 250000000000) : ℝ) = ((250000000000 / 1190872361763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15670_neg : (796928197 / 125000000) ≤ -Real.log (500000000000 / 293617647058823) ∧
    -Real.log (500000000000 / 293617647058823) ≤ (3187712793 / 500000000) := by
  have h := checkLog_sound (w := (37617647058823 / 549617647058823)) (n := 12)
    (lo := (34275239 / 250000000)) (hi := (137100957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293617647058823 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(293617647058823 / 256000000000000) = 1/(500000000000 / 293617647058823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15670 : Bounds (796928197 / 125000000) (3187712793 / 500000000) (Real.log (293617647058823 / 500000000000)) := by
  have h := reflection_log_15670_neg
  have he : Real.log (293617647058823 / 500000000000) = -Real.log (500000000000 / 293617647058823) := by
    rw [show ((293617647058823 / 500000000000) : ℝ) = ((500000000000 / 293617647058823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15671_neg : (6436150363 / 1000000000) ≤ -Real.log (1 / 624) ∧
    -Real.log (1 / 624) ≤ (6436150373 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(39 / 32) = 1/(1 / 624) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15671 : Bounds (6436150363 / 1000000000) (6436150373 / 1000000000) (Real.log (624 / 1)) := by
  have h := reflection_log_15671_neg
  have he : Real.log (624 / 1) = -Real.log (1 / 624) := by
    rw [show ((624 / 1) : ℝ) = ((1 / 624) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15672_neg : (345823027 / 500000000) ≤ -Real.log (1000 / 1997) ∧
    -Real.log (1000 / 1997) ≤ (138329211 / 200000000) := by
  have h := checkLog_sound (w := (997 / 2997)) (n := 12)
    (lo := (345823027 / 500000000)) (hi := (138329211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1997 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1997 / 1000) = 1/(1000 / 1997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15672 : Bounds (345823027 / 500000000) (138329211 / 200000000) (Real.log (1997 / 1000)) := by
  have h := reflection_log_15672_neg
  have he : Real.log (1997 / 1000) = -Real.log (1000 / 1997) := by
    rw [show ((1997 / 1000) : ℝ) = ((1000 / 1997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15673_neg : (1161828597 / 200000000) ≤ -Real.log (3 / 1000) ∧
    -Real.log (3 / 1000) ≤ (2904571497 / 500000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(125 / 96) = 1/(3 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15673 : Bounds (-2904571497 / 500000000) (-1161828597 / 200000000) (Real.log (3 / 1000)) := by
  have h := reflection_log_15673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15674_neg : (996503 / 1000000000) ≤ -Real.log (1000000 / 1000997) ∧
    -Real.log (1000000 / 1000997) ≤ (124563 / 125000000) := by
  have h := checkLog_sound (w := (997 / 2000997)) (n := 12)
    (lo := (996503 / 1000000000)) (hi := (124563 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000997 / 1000000) = 1/(1000000 / 1000997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15674 : Bounds (996503 / 1000000000) (124563 / 125000000) (Real.log (1000997 / 1000000)) := by
  have h := reflection_log_15674_neg
  have he : Real.log (1000997 / 1000000) = -Real.log (1000000 / 1000997) := by
    rw [show ((1000997 / 1000000) : ℝ) = ((1000000 / 1000997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15675_neg : (997497 / 1000000000) ≤ -Real.log (999003 / 1000000) ∧
    -Real.log (999003 / 1000000) ≤ (498749 / 500000000) := by
  have h := checkLog_sound (w := (997 / 1999003)) (n := 12)
    (lo := (997497 / 1000000000)) (hi := (498749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999003) = 1/(999003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15675 : Bounds (-498749 / 500000000) (-997497 / 1000000000) (Real.log (999003 / 1000000)) := by
  have h := reflection_log_15675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15676_neg : (2511041 / 5000000) ≤ -Real.log (500000 / 826183) ∧
    -Real.log (500000 / 826183) ≤ (502208201 / 1000000000) := by
  have h := checkLog_sound (w := (326183 / 1326183)) (n := 12)
    (lo := (2511041 / 5000000)) (hi := (502208201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826183 / 500000) = 1/(500000 / 826183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15676 : Bounds (2511041 / 5000000) (502208201 / 1000000000) (Real.log (826183 / 500000)) := by
  have h := reflection_log_15676_neg
  have he : Real.log (826183 / 500000) = -Real.log (500000 / 826183) := by
    rw [show ((826183 / 500000) : ℝ) = ((500000 / 826183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15677_neg : (264151269 / 250000000) ≤ -Real.log (173817 / 500000) ∧
    -Real.log (173817 / 500000) ≤ (528302539 / 500000000) := by
  have h := checkLog_sound (w := (76183 / 423817)) (n := 12)
    (lo := (45432237 / 125000000)) (hi := (363457897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173817) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173817) = 1/(173817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15677 : Bounds (-528302539 / 500000000) (-264151269 / 250000000) (Real.log (173817 / 500000)) := by
  have h := reflection_log_15677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15678_neg : (25139723 / 50000000) ≤ -Real.log (200000 / 330667) ∧
    -Real.log (200000 / 330667) ≤ (502794461 / 1000000000) := by
  have h := checkLog_sound (w := (130667 / 530667)) (n := 12)
    (lo := (25139723 / 50000000)) (hi := (502794461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330667 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330667 / 200000) = 1/(200000 / 330667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15678 : Bounds (25139723 / 50000000) (502794461 / 1000000000) (Real.log (330667 / 200000)) := by
  have h := reflection_log_15678_neg
  have he : Real.log (330667 / 200000) = -Real.log (200000 / 330667) := by
    rw [show ((330667 / 200000) : ℝ) = ((200000 / 330667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15679_neg : (529698191 / 500000000) ≤ -Real.log (69333 / 200000) ∧
    -Real.log (69333 / 200000) ≤ (33106137 / 31250000) := by
  have h := checkLog_sound (w := (30667 / 169333)) (n := 12)
    (lo := (183124601 / 500000000)) (hi := (366249203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69333) = 1/(69333 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15679 : Bounds (-33106137 / 31250000) (-529698191 / 500000000) (Real.log (69333 / 200000)) := by
  have h := reflection_log_15679_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
