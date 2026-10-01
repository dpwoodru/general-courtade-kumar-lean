import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13632_neg : (734269 / 1000000000) ≤ -Real.log (499633 / 500000) ∧
    -Real.log (499633 / 500000) ≤ (73427 / 100000000) := by
  have h := checkLog_sound (w := (367 / 999633)) (n := 12)
    (lo := (734269 / 1000000000)) (hi := (73427 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499633) = 1/(499633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13632 : Bounds (-73427 / 100000000) (-734269 / 1000000000) (Real.log (499633 / 500000)) := by
  have h := reflection_log_13632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13633_neg : (171006287 / 500000000) ≤ -Real.log (500000 / 703889) ∧
    -Real.log (500000 / 703889) ≤ (13680503 / 40000000) := by
  have h := checkLog_sound (w := (203889 / 1203889)) (n := 12)
    (lo := (171006287 / 500000000)) (hi := (13680503 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703889 / 500000) = 1/(500000 / 703889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13633 : Bounds (171006287 / 500000000) (13680503 / 40000000) (Real.log (703889 / 500000)) := by
  have h := reflection_log_13633_neg
  have he : Real.log (703889 / 500000) = -Real.log (500000 / 703889) := by
    rw [show ((703889 / 500000) : ℝ) = ((500000 / 703889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13634_neg : (261936857 / 500000000) ≤ -Real.log (296111 / 500000) ∧
    -Real.log (296111 / 500000) ≤ (104774743 / 200000000) := by
  have h := checkLog_sound (w := (203889 / 796111)) (n := 12)
    (lo := (261936857 / 500000000)) (hi := (104774743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296111) = 1/(296111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13634 : Bounds (-104774743 / 200000000) (-261936857 / 500000000) (Real.log (296111 / 500000)) := by
  have h := reflection_log_13634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13635_neg : (171980633 / 500000000) ≤ -Real.log (250000 / 352631) ∧
    -Real.log (250000 / 352631) ≤ (343961267 / 1000000000) := by
  have h := checkLog_sound (w := (102631 / 602631)) (n := 12)
    (lo := (171980633 / 500000000)) (hi := (343961267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352631 / 250000) = 1/(250000 / 352631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13635 : Bounds (171980633 / 500000000) (343961267 / 1000000000) (Real.log (352631 / 250000)) := by
  have h := reflection_log_13635_neg
  have he : Real.log (352631 / 250000) = -Real.log (250000 / 352631) := by
    rw [show ((352631 / 250000) : ℝ) = ((250000 / 352631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13636_neg : (66065159 / 125000000) ≤ -Real.log (147369 / 250000) ∧
    -Real.log (147369 / 250000) ≤ (528521273 / 1000000000) := by
  have h := checkLog_sound (w := (102631 / 397369)) (n := 12)
    (lo := (66065159 / 125000000)) (hi := (528521273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147369) = 1/(147369 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13636 : Bounds (-528521273 / 1000000000) (-66065159 / 125000000) (Real.log (147369 / 250000)) := by
  have h := reflection_log_13636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13637_neg : (36912001 / 200000000) ≤ -Real.log (51966877839 / 62500000000) ∧
    -Real.log (51966877839 / 62500000000) ≤ (92280003 / 500000000) := by
  have h := checkLog_sound (w := (10533122161 / 114466877839)) (n := 12)
    (lo := (36912001 / 200000000)) (hi := (92280003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51966877839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51966877839) = 1/(51966877839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13637 : Bounds (-92280003 / 500000000) (-36912001 / 200000000) (Real.log (51966877839 / 62500000000)) := by
  have h := reflection_log_13637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13638_neg : (181861139 / 1000000000) ≤ -Real.log (208429275679 / 250000000000) ∧
    -Real.log (208429275679 / 250000000000) ≤ (9093057 / 50000000) := by
  have h := checkLog_sound (w := (41570724321 / 458429275679)) (n := 12)
    (lo := (181861139 / 1000000000)) (hi := (9093057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 208429275679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 208429275679) = 1/(208429275679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13638 : Bounds (-9093057 / 50000000) (-181861139 / 1000000000) (Real.log (208429275679 / 250000000000)) := by
  have h := reflection_log_13638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13639_neg : (54117893 / 62500000) ≤ -Real.log (62500000000 / 148569497587) ∧
    -Real.log (62500000000 / 148569497587) ≤ (86588629 / 100000000) := by
  have h := checkLog_sound (w := (23569497587 / 273569497587)) (n := 12)
    (lo := (43184777 / 250000000)) (hi := (172739109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148569497587 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(148569497587 / 125000000000) = 1/(62500000000 / 148569497587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13639 : Bounds (54117893 / 62500000) (86588629 / 100000000) (Real.log (148569497587 / 62500000000)) := by
  have h := reflection_log_13639_neg
  have he : Real.log (148569497587 / 62500000000) = -Real.log (62500000000 / 148569497587) := by
    rw [show ((148569497587 / 62500000000) : ℝ) = ((62500000000 / 148569497587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13640_neg : (436241269 / 500000000) ≤ -Real.log (250000000000 / 598210953457) ∧
    -Real.log (250000000000 / 598210953457) ≤ (43624127 / 50000000) := by
  have h := checkLog_sound (w := (98210953457 / 1098210953457)) (n := 12)
    (lo := (89667679 / 500000000)) (hi := (179335359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598210953457 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(598210953457 / 500000000000) = 1/(250000000000 / 598210953457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13640 : Bounds (436241269 / 500000000) (43624127 / 50000000) (Real.log (598210953457 / 250000000000)) := by
  have h := reflection_log_13640_neg
  have he : Real.log (598210953457 / 250000000000) = -Real.log (250000000000 / 598210953457) := by
    rw [show ((598210953457 / 250000000000) : ℝ) = ((250000000000 / 598210953457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13641_neg : (930871587 / 500000000) ≤ -Real.log (500000000000 / 3217472118959) ∧
    -Real.log (500000000000 / 3217472118959) ≤ (1861743177 / 1000000000) := by
  have h := checkLog_sound (w := (1217472118959 / 5217472118959)) (n := 12)
    (lo := (237724407 / 500000000)) (hi := (95089763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3217472118959 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3217472118959 / 2000000000000) = 1/(500000000000 / 3217472118959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13641 : Bounds (930871587 / 500000000) (1861743177 / 1000000000) (Real.log (3217472118959 / 500000000000)) := by
  have h := reflection_log_13641_neg
  have he : Real.log (3217472118959 / 500000000000) = -Real.log (500000000000 / 3217472118959) := by
    rw [show ((3217472118959 / 500000000000) : ℝ) = ((500000000000 / 3217472118959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13642_neg : (1874689847 / 1000000000) ≤ -Real.log (500000000000 / 3259398496241) ∧
    -Real.log (500000000000 / 3259398496241) ≤ (37493797 / 20000000) := by
  have h := checkLog_sound (w := (1259398496241 / 5259398496241)) (n := 12)
    (lo := (488395487 / 1000000000)) (hi := (15262359 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3259398496241 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3259398496241 / 2000000000000) = 1/(500000000000 / 3259398496241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13642 : Bounds (1874689847 / 1000000000) (37493797 / 20000000) (Real.log (3259398496241 / 500000000000)) := by
  have h := reflection_log_13642_neg
  have he : Real.log (3259398496241 / 500000000000) = -Real.log (500000000000 / 3259398496241) := by
    rw [show ((3259398496241 / 500000000000) : ℝ) = ((500000000000 / 3259398496241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13643_neg : (552159487 / 1000000000) ≤ -Real.log (1000 / 1737) ∧
    -Real.log (1000 / 1737) ≤ (2156873 / 3906250) := by
  have h := checkLog_sound (w := (737 / 2737)) (n := 12)
    (lo := (552159487 / 1000000000)) (hi := (2156873 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1000) = 1/(1000 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13643 : Bounds (552159487 / 1000000000) (2156873 / 3906250) (Real.log (1737 / 1000)) := by
  have h := reflection_log_13643_neg
  have he : Real.log (1737 / 1000) = -Real.log (1000 / 1737) := by
    rw [show ((1737 / 1000) : ℝ) = ((1000 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13644_neg : (667800623 / 500000000) ≤ -Real.log (263 / 1000) ∧
    -Real.log (263 / 1000) ≤ (41737539 / 31250000) := by
  have h := checkLog_sound (w := (237 / 763)) (n := 12)
    (lo := (321227033 / 500000000)) (hi := (642454067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 263) = 1/(263 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13644 : Bounds (-41737539 / 31250000) (-667800623 / 500000000) (Real.log (263 / 1000)) := by
  have h := reflection_log_13644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13645_neg : (92091 / 125000000) ≤ -Real.log (1000000 / 1000737) ∧
    -Real.log (1000000 / 1000737) ≤ (736729 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 2000737)) (n := 12)
    (lo := (92091 / 125000000)) (hi := (736729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000737 / 1000000) = 1/(1000000 / 1000737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13645 : Bounds (92091 / 125000000) (736729 / 1000000000) (Real.log (1000737 / 1000000)) := by
  have h := reflection_log_13645_neg
  have he : Real.log (1000737 / 1000000) = -Real.log (1000000 / 1000737) := by
    rw [show ((1000737 / 1000000) : ℝ) = ((1000000 / 1000737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13646_neg : (737271 / 1000000000) ≤ -Real.log (999263 / 1000000) ∧
    -Real.log (999263 / 1000000) ≤ (92159 / 125000000) := by
  have h := checkLog_sound (w := (737 / 1999263)) (n := 12)
    (lo := (737271 / 1000000000)) (hi := (92159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999263) = 1/(999263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13646 : Bounds (-92159 / 125000000) (-737271 / 1000000000) (Real.log (999263 / 1000000)) := by
  have h := reflection_log_13646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13647_neg : (343510977 / 1000000000) ≤ -Real.log (1000000 / 1409889) ∧
    -Real.log (1000000 / 1409889) ≤ (171755489 / 500000000) := by
  have h := checkLog_sound (w := (409889 / 2409889)) (n := 12)
    (lo := (343510977 / 1000000000)) (hi := (171755489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409889 / 1000000) = 1/(1000000 / 1409889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13647 : Bounds (343510977 / 1000000000) (171755489 / 500000000) (Real.log (1409889 / 1000000)) := by
  have h := reflection_log_13647_neg
  have he : Real.log (1409889 / 1000000) = -Real.log (1000000 / 1409889) := by
    rw [show ((1409889 / 1000000) : ℝ) = ((1000000 / 1409889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13648_neg : (32965289 / 62500000) ≤ -Real.log (590111 / 1000000) ∧
    -Real.log (590111 / 1000000) ≤ (4219557 / 8000000) := by
  have h := checkLog_sound (w := (409889 / 1590111)) (n := 12)
    (lo := (32965289 / 62500000)) (hi := (4219557 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590111) = 1/(590111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13648 : Bounds (-4219557 / 8000000) (-32965289 / 62500000) (Real.log (590111 / 1000000)) := by
  have h := reflection_log_13648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13649_neg : (552741 / 1600000) ≤ -Real.log (250000 / 353161) ∧
    -Real.log (250000 / 353161) ≤ (172731563 / 500000000) := by
  have h := checkLog_sound (w := (103161 / 603161)) (n := 12)
    (lo := (552741 / 1600000)) (hi := (172731563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353161 / 250000) = 1/(250000 / 353161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13649 : Bounds (552741 / 1600000) (172731563 / 500000000) (Real.log (353161 / 250000)) := by
  have h := reflection_log_13649_neg
  have he : Real.log (353161 / 250000) = -Real.log (250000 / 353161) := by
    rw [show ((353161 / 250000) : ℝ) = ((250000 / 353161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13650_neg : (532124169 / 1000000000) ≤ -Real.log (146839 / 250000) ∧
    -Real.log (146839 / 250000) ≤ (53212417 / 100000000) := by
  have h := checkLog_sound (w := (103161 / 396839)) (n := 12)
    (lo := (532124169 / 1000000000)) (hi := (53212417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 146839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 146839) = 1/(146839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13650 : Bounds (-53212417 / 100000000) (-532124169 / 1000000000) (Real.log (146839 / 250000)) := by
  have h := reflection_log_13650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13651_neg : (186661043 / 1000000000) ≤ -Real.log (51857808079 / 62500000000) ∧
    -Real.log (51857808079 / 62500000000) ≤ (46665261 / 250000000) := by
  have h := checkLog_sound (w := (10642191921 / 114357808079)) (n := 12)
    (lo := (186661043 / 1000000000)) (hi := (46665261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51857808079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51857808079) = 1/(51857808079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13651 : Bounds (-46665261 / 250000000) (-186661043 / 1000000000) (Real.log (51857808079 / 62500000000)) := by
  have h := reflection_log_13651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13652_neg : (91966823 / 500000000) ≤ -Real.log (831991007679 / 1000000000000) ∧
    -Real.log (831991007679 / 1000000000000) ≤ (183933647 / 1000000000) := by
  have h := checkLog_sound (w := (168008992321 / 1831991007679)) (n := 12)
    (lo := (91966823 / 500000000)) (hi := (183933647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 831991007679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 831991007679) = 1/(831991007679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13652 : Bounds (-183933647 / 1000000000) (-91966823 / 500000000) (Real.log (831991007679 / 1000000000000)) := by
  have h := reflection_log_13652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13653_neg : (870955601 / 1000000000) ≤ -Real.log (50000000000 / 119459644033) ∧
    -Real.log (50000000000 / 119459644033) ≤ (870955603 / 1000000000) := by
  have h := checkLog_sound (w := (19459644033 / 219459644033)) (n := 12)
    (lo := (177808421 / 1000000000)) (hi := (88904211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119459644033 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119459644033 / 100000000000) = 1/(50000000000 / 119459644033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13653 : Bounds (870955601 / 1000000000) (870955603 / 1000000000) (Real.log (119459644033 / 50000000000)) := by
  have h := reflection_log_13653_neg
  have he : Real.log (119459644033 / 50000000000) = -Real.log (50000000000 / 119459644033) := by
    rw [show ((119459644033 / 50000000000) : ℝ) = ((50000000000 / 119459644033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13654_neg : (438793647 / 500000000) ≤ -Real.log (500000000000 / 1202544964213) ∧
    -Real.log (500000000000 / 1202544964213) ≤ (27424603 / 31250000) := by
  have h := checkLog_sound (w := (202544964213 / 2202544964213)) (n := 12)
    (lo := (92220057 / 500000000)) (hi := (36888023 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202544964213 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1202544964213 / 1000000000000) = 1/(500000000000 / 1202544964213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13654 : Bounds (438793647 / 500000000) (27424603 / 31250000) (Real.log (1202544964213 / 500000000000)) := by
  have h := reflection_log_13654_neg
  have he : Real.log (1202544964213 / 500000000000) = -Real.log (500000000000 / 1202544964213) := by
    rw [show ((1202544964213 / 500000000000) : ℝ) = ((500000000000 / 1202544964213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13655_neg : (1874689847 / 1000000000) ≤ -Real.log (6250000000 / 40742481203) ∧
    -Real.log (6250000000 / 40742481203) ≤ (37493797 / 20000000) := by
  have h := checkLog_sound (w := (15742481203 / 65742481203)) (n := 12)
    (lo := (488395487 / 1000000000)) (hi := (15262359 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40742481203 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40742481203 / 25000000000) = 1/(6250000000 / 40742481203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13655 : Bounds (1874689847 / 1000000000) (37493797 / 20000000) (Real.log (40742481203 / 6250000000)) := by
  have h := reflection_log_13655_neg
  have he : Real.log (40742481203 / 6250000000) = -Real.log (6250000000 / 40742481203) := by
    rw [show ((40742481203 / 6250000000) : ℝ) = ((6250000000 / 40742481203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13656_neg : (471940183 / 250000000) ≤ -Real.log (250000000000 / 1651140684411) ∧
    -Real.log (250000000000 / 1651140684411) ≤ (377552147 / 200000000) := by
  have h := checkLog_sound (w := (651140684411 / 2651140684411)) (n := 12)
    (lo := (125366593 / 250000000)) (hi := (501466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651140684411 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1651140684411 / 1000000000000) = 1/(250000000000 / 1651140684411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13656 : Bounds (471940183 / 250000000) (377552147 / 200000000) (Real.log (1651140684411 / 250000000000)) := by
  have h := reflection_log_13656_neg
  have he : Real.log (1651140684411 / 250000000000) = -Real.log (250000000000 / 1651140684411) := by
    rw [show ((1651140684411 / 250000000000) : ℝ) = ((250000000000 / 1651140684411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13657_neg : (553885113 / 1000000000) ≤ -Real.log (50 / 87) ∧
    -Real.log (50 / 87) ≤ (276942557 / 500000000) := by
  have h := checkLog_sound (w := (37 / 137)) (n := 12)
    (lo := (553885113 / 1000000000)) (hi := (276942557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 50) = 1/(50 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13657 : Bounds (553885113 / 1000000000) (276942557 / 500000000) (Real.log (87 / 50)) := by
  have h := reflection_log_13657_neg
  have he : Real.log (87 / 50) = -Real.log (50 / 87) := by
    rw [show ((87 / 50) : ℝ) = ((50 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13658_neg : (1347073647 / 1000000000) ≤ -Real.log (13 / 50) ∧
    -Real.log (13 / 50) ≤ (1347073649 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 13) = 1/(13 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13658 : Bounds (-1347073649 / 1000000000) (-1347073647 / 1000000000) (Real.log (13 / 50)) := by
  have h := reflection_log_13658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13659_neg : (369863 / 500000000) ≤ -Real.log (50000 / 50037) ∧
    -Real.log (50000 / 50037) ≤ (739727 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 100037)) (n := 12)
    (lo := (369863 / 500000000)) (hi := (739727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50037 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50037 / 50000) = 1/(50000 / 50037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13659 : Bounds (369863 / 500000000) (739727 / 1000000000) (Real.log (50037 / 50000)) := by
  have h := reflection_log_13659_neg
  have he : Real.log (50037 / 50000) = -Real.log (50000 / 50037) := by
    rw [show ((50037 / 50000) : ℝ) = ((50000 / 50037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13660_neg : (740273 / 1000000000) ≤ -Real.log (49963 / 50000) ∧
    -Real.log (49963 / 50000) ≤ (370137 / 500000000) := by
  have h := checkLog_sound (w := (37 / 99963)) (n := 12)
    (lo := (740273 / 1000000000)) (hi := (370137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49963) = 1/(49963 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13660 : Bounds (-370137 / 500000000) (-740273 / 1000000000) (Real.log (49963 / 50000)) := by
  have h := reflection_log_13660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13661_neg : (86253201 / 250000000) ≤ -Real.log (125000 / 176501) ∧
    -Real.log (125000 / 176501) ≤ (69002561 / 200000000) := by
  have h := checkLog_sound (w := (51501 / 301501)) (n := 12)
    (lo := (86253201 / 250000000)) (hi := (69002561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176501 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176501 / 125000) = 1/(125000 / 176501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13661 : Bounds (86253201 / 250000000) (69002561 / 200000000) (Real.log (176501 / 125000)) := by
  have h := reflection_log_13661_neg
  have he : Real.log (176501 / 125000) = -Real.log (125000 / 176501) := by
    rw [show ((176501 / 125000) : ℝ) = ((125000 / 176501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13662_neg : (33190121 / 62500000) ≤ -Real.log (73499 / 125000) ∧
    -Real.log (73499 / 125000) ≤ (531041937 / 1000000000) := by
  have h := checkLog_sound (w := (51501 / 198499)) (n := 12)
    (lo := (33190121 / 62500000)) (hi := (531041937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 73499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 73499) = 1/(73499 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13662 : Bounds (-531041937 / 1000000000) (-33190121 / 62500000) (Real.log (73499 / 125000)) := by
  have h := reflection_log_13662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13663_neg : (346968387 / 1000000000) ≤ -Real.log (250000 / 353693) ∧
    -Real.log (250000 / 353693) ≤ (86742097 / 250000000) := by
  have h := checkLog_sound (w := (103693 / 603693)) (n := 12)
    (lo := (346968387 / 1000000000)) (hi := (86742097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353693 / 250000) = 1/(250000 / 353693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13663 : Bounds (346968387 / 1000000000) (86742097 / 250000000) (Real.log (353693 / 250000)) := by
  have h := reflection_log_13663_neg
  have he : Real.log (353693 / 250000) = -Real.log (250000 / 353693) := by
    rw [show ((353693 / 250000) : ℝ) = ((250000 / 353693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13664_neg : (133938441 / 250000000) ≤ -Real.log (146307 / 250000) ∧
    -Real.log (146307 / 250000) ≤ (107150753 / 200000000) := by
  have h := checkLog_sound (w := (103693 / 396307)) (n := 12)
    (lo := (133938441 / 250000000)) (hi := (107150753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 146307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 146307) = 1/(146307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13664 : Bounds (-107150753 / 200000000) (-133938441 / 250000000) (Real.log (146307 / 250000)) := by
  have h := reflection_log_13664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13665_neg : (5899543 / 31250000) ≤ -Real.log (51747761751 / 62500000000) ∧
    -Real.log (51747761751 / 62500000000) ≤ (188785377 / 1000000000) := by
  have h := checkLog_sound (w := (10752238249 / 114247761751)) (n := 12)
    (lo := (5899543 / 31250000)) (hi := (188785377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51747761751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51747761751) = 1/(51747761751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13665 : Bounds (-188785377 / 1000000000) (-5899543 / 31250000) (Real.log (51747761751 / 62500000000)) := by
  have h := reflection_log_13665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13666_neg : (186029131 / 1000000000) ≤ -Real.log (12972646999 / 15625000000) ∧
    -Real.log (12972646999 / 15625000000) ≤ (46507283 / 250000000) := by
  have h := checkLog_sound (w := (2652353001 / 28597646999)) (n := 12)
    (lo := (186029131 / 1000000000)) (hi := (46507283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 12972646999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 12972646999) = 1/(12972646999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13666 : Bounds (-46507283 / 250000000) (-186029131 / 1000000000) (Real.log (12972646999 / 15625000000)) := by
  have h := reflection_log_13666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13667_neg : (43802737 / 50000000) ≤ -Real.log (50000000000 / 120070341093) ∧
    -Real.log (50000000000 / 120070341093) ≤ (438027371 / 500000000) := by
  have h := checkLog_sound (w := (20070341093 / 220070341093)) (n := 12)
    (lo := (4572689 / 25000000)) (hi := (182907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120070341093 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(120070341093 / 100000000000) = 1/(50000000000 / 120070341093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13667 : Bounds (43802737 / 50000000) (438027371 / 500000000) (Real.log (120070341093 / 50000000000)) := by
  have h := reflection_log_13667_neg
  have he : Real.log (120070341093 / 50000000000) = -Real.log (50000000000 / 120070341093) := by
    rw [show ((120070341093 / 50000000000) : ℝ) = ((50000000000 / 120070341093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13668_neg : (17654443 / 20000000) ≤ -Real.log (500000000000 / 1208735740601) ∧
    -Real.log (500000000000 / 1208735740601) ≤ (110340269 / 125000000) := by
  have h := checkLog_sound (w := (208735740601 / 2208735740601)) (n := 12)
    (lo := (18957497 / 100000000)) (hi := (189574971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208735740601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1208735740601 / 1000000000000) = 1/(500000000000 / 1208735740601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13668 : Bounds (17654443 / 20000000) (110340269 / 125000000) (Real.log (1208735740601 / 500000000000)) := by
  have h := reflection_log_13668_neg
  have he : Real.log (1208735740601 / 500000000000) = -Real.log (500000000000 / 1208735740601) := by
    rw [show ((1208735740601 / 500000000000) : ℝ) = ((500000000000 / 1208735740601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13669_neg : (471940183 / 250000000) ≤ -Real.log (500000000000 / 3302281368821) ∧
    -Real.log (500000000000 / 3302281368821) ≤ (377552147 / 200000000) := by
  have h := checkLog_sound (w := (1302281368821 / 5302281368821)) (n := 12)
    (lo := (125366593 / 250000000)) (hi := (501466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3302281368821 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3302281368821 / 2000000000000) = 1/(500000000000 / 3302281368821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13669 : Bounds (471940183 / 250000000) (377552147 / 200000000) (Real.log (3302281368821 / 500000000000)) := by
  have h := reflection_log_13669_neg
  have he : Real.log (3302281368821 / 500000000000) = -Real.log (500000000000 / 3302281368821) := by
    rw [show ((3302281368821 / 500000000000) : ℝ) = ((500000000000 / 3302281368821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13670_neg : (47523969 / 25000000) ≤ -Real.log (250000000000 / 1673076923077) ∧
    -Real.log (250000000000 / 1673076923077) ≤ (1900958763 / 1000000000) := by
  have h := checkLog_sound (w := (673076923077 / 2673076923077)) (n := 12)
    (lo := (1286661 / 2500000)) (hi := (514664401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1673076923077 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1673076923077 / 1000000000000) = 1/(250000000000 / 1673076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13670 : Bounds (47523969 / 25000000) (1900958763 / 1000000000) (Real.log (1673076923077 / 250000000000)) := by
  have h := reflection_log_13670_neg
  have he : Real.log (1673076923077 / 250000000000) = -Real.log (250000000000 / 1673076923077) := by
    rw [show ((1673076923077 / 250000000000) : ℝ) = ((250000000000 / 1673076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13671_neg : (277803883 / 500000000) ≤ -Real.log (1000 / 1743) ∧
    -Real.log (1000 / 1743) ≤ (555607767 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 2743)) (n := 12)
    (lo := (277803883 / 500000000)) (hi := (555607767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743 / 1000) = 1/(1000 / 1743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13671 : Bounds (277803883 / 500000000) (555607767 / 1000000000) (Real.log (1743 / 1000)) := by
  have h := reflection_log_13671_neg
  have he : Real.log (1743 / 1000) = -Real.log (1000 / 1743) := by
    rw [show ((1743 / 1000) : ℝ) = ((1000 / 1743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13672_neg : (1358679193 / 1000000000) ≤ -Real.log (257 / 1000) ∧
    -Real.log (257 / 1000) ≤ (271735839 / 200000000) := by
  have h := checkLog_sound (w := (243 / 757)) (n := 12)
    (lo := (665532013 / 1000000000)) (hi := (332766007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 257) = 1/(257 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13672 : Bounds (-271735839 / 200000000) (-1358679193 / 1000000000) (Real.log (257 / 1000)) := by
  have h := reflection_log_13672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13673_neg : (185681 / 250000000) ≤ -Real.log (1000000 / 1000743) ∧
    -Real.log (1000000 / 1000743) ≤ (29709 / 40000000) := by
  have h := checkLog_sound (w := (743 / 2000743)) (n := 12)
    (lo := (185681 / 250000000)) (hi := (29709 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000743 / 1000000) = 1/(1000000 / 1000743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13673 : Bounds (185681 / 250000000) (29709 / 40000000) (Real.log (1000743 / 1000000)) := by
  have h := reflection_log_13673_neg
  have he : Real.log (1000743 / 1000000) = -Real.log (1000000 / 1000743) := by
    rw [show ((1000743 / 1000000) : ℝ) = ((1000000 / 1000743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13674_neg : (185819 / 250000000) ≤ -Real.log (999257 / 1000000) ∧
    -Real.log (999257 / 1000000) ≤ (743277 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 1999257)) (n := 12)
    (lo := (185819 / 250000000)) (hi := (743277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999257) = 1/(999257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13674 : Bounds (-743277 / 1000000000) (-185819 / 250000000) (Real.log (999257 / 1000000)) := by
  have h := reflection_log_13674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13675_neg : (346517329 / 1000000000) ≤ -Real.log (500000 / 707067) ∧
    -Real.log (500000 / 707067) ≤ (34651733 / 100000000) := by
  have h := checkLog_sound (w := (207067 / 1207067)) (n := 12)
    (lo := (346517329 / 1000000000)) (hi := (34651733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707067 / 500000) = 1/(500000 / 707067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13675 : Bounds (346517329 / 1000000000) (34651733 / 100000000) (Real.log (707067 / 500000)) := by
  have h := reflection_log_13675_neg
  have he : Real.log (707067 / 500000) = -Real.log (500000 / 707067) := by
    rw [show ((707067 / 500000) : ℝ) = ((500000 / 707067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13676_neg : (66833023 / 125000000) ≤ -Real.log (292933 / 500000) ∧
    -Real.log (292933 / 500000) ≤ (106932837 / 200000000) := by
  have h := checkLog_sound (w := (207067 / 792933)) (n := 12)
    (lo := (66833023 / 125000000)) (hi := (106932837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292933) = 1/(292933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13676 : Bounds (-106932837 / 200000000) (-66833023 / 125000000) (Real.log (292933 / 500000)) := by
  have h := reflection_log_13676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13677_neg : (174238163 / 500000000) ≤ -Real.log (1000000 / 1416907) ∧
    -Real.log (1000000 / 1416907) ≤ (348476327 / 1000000000) := by
  have h := checkLog_sound (w := (416907 / 2416907)) (n := 12)
    (lo := (174238163 / 500000000)) (hi := (348476327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1416907 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1416907 / 1000000) = 1/(1000000 / 1416907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13677 : Bounds (174238163 / 500000000) (348476327 / 1000000000) (Real.log (1416907 / 1000000)) := by
  have h := reflection_log_13677_neg
  have he : Real.log (1416907 / 1000000) = -Real.log (1000000 / 1416907) := by
    rw [show ((1416907 / 1000000) : ℝ) = ((1000000 / 1416907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13678_neg : (107881717 / 200000000) ≤ -Real.log (583093 / 1000000) ∧
    -Real.log (583093 / 1000000) ≤ (269704293 / 500000000) := by
  have h := checkLog_sound (w := (416907 / 1583093)) (n := 12)
    (lo := (107881717 / 200000000)) (hi := (269704293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 583093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 583093) = 1/(583093 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13678 : Bounds (-269704293 / 500000000) (-107881717 / 200000000) (Real.log (583093 / 1000000)) := by
  have h := reflection_log_13678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13679_neg : (95466129 / 500000000) ≤ -Real.log (826188553351 / 1000000000000) ∧
    -Real.log (826188553351 / 1000000000000) ≤ (190932259 / 1000000000) := by
  have h := checkLog_sound (w := (173811446649 / 1826188553351)) (n := 12)
    (lo := (95466129 / 500000000)) (hi := (190932259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 826188553351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 826188553351) = 1/(826188553351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13679 : Bounds (-190932259 / 1000000000) (-95466129 / 500000000) (Real.log (826188553351 / 1000000000000)) := by
  have h := reflection_log_13679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13680_neg : (94073427 / 500000000) ≤ -Real.log (207123257511 / 250000000000) ∧
    -Real.log (207123257511 / 250000000000) ≤ (37629371 / 200000000) := by
  have h := checkLog_sound (w := (42876742489 / 457123257511)) (n := 12)
    (lo := (94073427 / 500000000)) (hi := (37629371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 207123257511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 207123257511) = 1/(207123257511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13680 : Bounds (-37629371 / 200000000) (-94073427 / 500000000) (Real.log (207123257511 / 250000000000)) := by
  have h := reflection_log_13680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13681_neg : (881181513 / 1000000000) ≤ -Real.log (500000000000 / 1206874950927) ∧
    -Real.log (500000000000 / 1206874950927) ≤ (176236303 / 200000000) := by
  have h := checkLog_sound (w := (206874950927 / 2206874950927)) (n := 12)
    (lo := (188034333 / 1000000000)) (hi := (94017167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206874950927 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1206874950927 / 1000000000000) = 1/(500000000000 / 1206874950927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13681 : Bounds (881181513 / 1000000000) (176236303 / 200000000) (Real.log (1206874950927 / 500000000000)) := by
  have h := reflection_log_13681_neg
  have he : Real.log (1206874950927 / 500000000000) = -Real.log (500000000000 / 1206874950927) := by
    rw [show ((1206874950927 / 500000000000) : ℝ) = ((500000000000 / 1206874950927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13682_neg : (55492807 / 62500000) ≤ -Real.log (50000000000 / 121499229111) ∧
    -Real.log (50000000000 / 121499229111) ≤ (443942457 / 500000000) := by
  have h := checkLog_sound (w := (21499229111 / 221499229111)) (n := 12)
    (lo := (48684433 / 250000000)) (hi := (194737733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121499229111 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121499229111 / 100000000000) = 1/(50000000000 / 121499229111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13682 : Bounds (55492807 / 62500000) (443942457 / 500000000) (Real.log (121499229111 / 50000000000)) := by
  have h := reflection_log_13682_neg
  have he : Real.log (121499229111 / 50000000000) = -Real.log (50000000000 / 121499229111) := by
    rw [show ((121499229111 / 50000000000) : ℝ) = ((50000000000 / 121499229111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13683_neg : (47523969 / 25000000) ≤ -Real.log (500000000000 / 3346153846153) ∧
    -Real.log (500000000000 / 3346153846153) ≤ (1900958763 / 1000000000) := by
  have h := checkLog_sound (w := (1346153846153 / 5346153846153)) (n := 12)
    (lo := (1286661 / 2500000)) (hi := (514664401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3346153846153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3346153846153 / 2000000000000) = 1/(500000000000 / 3346153846153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13683 : Bounds (47523969 / 25000000) (1900958763 / 1000000000) (Real.log (3346153846153 / 500000000000)) := by
  have h := reflection_log_13683_neg
  have he : Real.log (3346153846153 / 500000000000) = -Real.log (500000000000 / 3346153846153) := by
    rw [show ((3346153846153 / 500000000000) : ℝ) = ((500000000000 / 3346153846153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13684_neg : (1914286959 / 1000000000) ≤ -Real.log (250000000000 / 1695525291829) ∧
    -Real.log (250000000000 / 1695525291829) ≤ (957143481 / 500000000) := by
  have h := checkLog_sound (w := (695525291829 / 2695525291829)) (n := 12)
    (lo := (527992599 / 1000000000)) (hi := (2639963 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695525291829 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1695525291829 / 1000000000000) = 1/(250000000000 / 1695525291829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13684 : Bounds (1914286959 / 1000000000) (957143481 / 500000000) (Real.log (1695525291829 / 250000000000)) := by
  have h := reflection_log_13684_neg
  have he : Real.log (1695525291829 / 250000000000) = -Real.log (250000000000 / 1695525291829) := by
    rw [show ((1695525291829 / 250000000000) : ℝ) = ((250000000000 / 1695525291829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13685_neg : (557327457 / 1000000000) ≤ -Real.log (500 / 873) ∧
    -Real.log (500 / 873) ≤ (278663729 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1373)) (n := 12)
    (lo := (557327457 / 1000000000)) (hi := (278663729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 500) = 1/(500 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13685 : Bounds (557327457 / 1000000000) (278663729 / 500000000) (Real.log (873 / 500)) := by
  have h := reflection_log_13685_neg
  have he : Real.log (873 / 500) = -Real.log (500 / 873) := by
    rw [show ((873 / 500) : ℝ) = ((500 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13686_neg : (1370421011 / 1000000000) ≤ -Real.log (127 / 500) ∧
    -Real.log (127 / 500) ≤ (1370421013 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 377)) (n := 12)
    (lo := (677273831 / 1000000000)) (hi := (84659229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 127) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 127) = 1/(127 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13686 : Bounds (-1370421013 / 1000000000) (-1370421011 / 1000000000) (Real.log (127 / 500)) := by
  have h := reflection_log_13686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13687_neg : (745721 / 1000000000) ≤ -Real.log (500000 / 500373) ∧
    -Real.log (500000 / 500373) ≤ (372861 / 500000000) := by
  have h := checkLog_sound (w := (373 / 1000373)) (n := 12)
    (lo := (745721 / 1000000000)) (hi := (372861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500373 / 500000) = 1/(500000 / 500373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13687 : Bounds (745721 / 1000000000) (372861 / 500000000) (Real.log (500373 / 500000)) := by
  have h := reflection_log_13687_neg
  have he : Real.log (500373 / 500000) = -Real.log (500000 / 500373) := by
    rw [show ((500373 / 500000) : ℝ) = ((500000 / 500373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13688_neg : (373139 / 500000000) ≤ -Real.log (499627 / 500000) ∧
    -Real.log (499627 / 500000) ≤ (746279 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 999627)) (n := 12)
    (lo := (373139 / 500000000)) (hi := (746279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499627) = 1/(499627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13688 : Bounds (-746279 / 1000000000) (-373139 / 500000000) (Real.log (499627 / 500000)) := by
  have h := reflection_log_13688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13689_neg : (174012621 / 500000000) ≤ -Real.log (250000 / 354067) ∧
    -Real.log (250000 / 354067) ≤ (348025243 / 1000000000) := by
  have h := checkLog_sound (w := (104067 / 604067)) (n := 12)
    (lo := (174012621 / 500000000)) (hi := (348025243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354067 / 250000) = 1/(250000 / 354067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13689 : Bounds (174012621 / 500000000) (348025243 / 1000000000) (Real.log (354067 / 250000)) := by
  have h := reflection_log_13689_neg
  have he : Real.log (354067 / 250000) = -Real.log (250000 / 354067) := by
    rw [show ((354067 / 250000) : ℝ) = ((250000 / 354067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13690_neg : (107662661 / 200000000) ≤ -Real.log (145933 / 250000) ∧
    -Real.log (145933 / 250000) ≤ (269156653 / 500000000) := by
  have h := checkLog_sound (w := (104067 / 395933)) (n := 12)
    (lo := (107662661 / 200000000)) (hi := (269156653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145933) = 1/(145933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13690 : Bounds (-269156653 / 500000000) (-107662661 / 200000000) (Real.log (145933 / 250000)) := by
  have h := reflection_log_13690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13691_neg : (349987633 / 1000000000) ≤ -Real.log (20000 / 28381) ∧
    -Real.log (20000 / 28381) ≤ (174993817 / 500000000) := by
  have h := checkLog_sound (w := (8381 / 48381)) (n := 12)
    (lo := (349987633 / 1000000000)) (hi := (174993817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28381 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28381 / 20000) = 1/(20000 / 28381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13691 : Bounds (349987633 / 1000000000) (174993817 / 500000000) (Real.log (28381 / 20000)) := by
  have h := reflection_log_13691_neg
  have he : Real.log (28381 / 20000) = -Real.log (20000 / 28381) := by
    rw [show ((28381 / 20000) : ℝ) = ((20000 / 28381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13692_neg : (67886323 / 125000000) ≤ -Real.log (11619 / 20000) ∧
    -Real.log (11619 / 20000) ≤ (108618117 / 200000000) := by
  have h := checkLog_sound (w := (8381 / 31619)) (n := 12)
    (lo := (67886323 / 125000000)) (hi := (108618117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 11619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 11619) = 1/(11619 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13692 : Bounds (-108618117 / 200000000) (-67886323 / 125000000) (Real.log (11619 / 20000)) := by
  have h := reflection_log_13692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13693_neg : (3862059 / 20000000) ≤ -Real.log (329758839 / 400000000) ∧
    -Real.log (329758839 / 400000000) ≤ (193102951 / 1000000000) := by
  have h := checkLog_sound (w := (70241161 / 729758839)) (n := 12)
    (lo := (3862059 / 20000000)) (hi := (193102951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 329758839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 329758839) = 1/(329758839 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13693 : Bounds (-193102951 / 1000000000) (-3862059 / 20000000) (Real.log (329758839 / 400000000)) := by
  have h := reflection_log_13693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13694_neg : (95144031 / 500000000) ≤ -Real.log (51670059511 / 62500000000) ∧
    -Real.log (51670059511 / 62500000000) ≤ (190288063 / 1000000000) := by
  have h := checkLog_sound (w := (10829940489 / 114170059511)) (n := 12)
    (lo := (95144031 / 500000000)) (hi := (190288063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 51670059511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 51670059511) = 1/(51670059511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13694 : Bounds (-190288063 / 1000000000) (-95144031 / 500000000) (Real.log (51670059511 / 62500000000)) := by
  have h := reflection_log_13694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13695_neg : (886338547 / 1000000000) ≤ -Real.log (500000000000 / 1213114922601) ∧
    -Real.log (500000000000 / 1213114922601) ≤ (886338549 / 1000000000) := by
  have h := checkLog_sound (w := (213114922601 / 2213114922601)) (n := 12)
    (lo := (193191367 / 1000000000)) (hi := (24148921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213114922601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1213114922601 / 1000000000000) = 1/(500000000000 / 1213114922601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13695 : Bounds (886338547 / 1000000000) (886338549 / 1000000000) (Real.log (1213114922601 / 500000000000)) := by
  have h := reflection_log_13695_neg
  have he : Real.log (1213114922601 / 500000000000) = -Real.log (500000000000 / 1213114922601) := by
    rw [show ((1213114922601 / 500000000000) : ℝ) = ((500000000000 / 1213114922601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
