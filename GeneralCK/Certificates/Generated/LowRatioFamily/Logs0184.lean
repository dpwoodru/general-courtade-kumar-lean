import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11776_neg : (261593361 / 1000000000) ≤ -Real.log (24057 / 31250) ∧
    -Real.log (24057 / 31250) ≤ (130796681 / 500000000) := by
  have h := checkLog_sound (w := (7193 / 55307)) (n := 12)
    (lo := (261593361 / 1000000000)) (hi := (130796681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24057) = 1/(24057 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11776 : Bounds (-130796681 / 500000000) (-261593361 / 1000000000) (Real.log (24057 / 31250)) := by
  have h := reflection_log_11776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11777_neg : (207959251 / 1000000000) ≤ -Real.log (1000000 / 1231163) ∧
    -Real.log (1000000 / 1231163) ≤ (51989813 / 250000000) := by
  have h := checkLog_sound (w := (231163 / 2231163)) (n := 12)
    (lo := (207959251 / 1000000000)) (hi := (51989813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231163 / 1000000) = 1/(1000000 / 1231163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11777 : Bounds (207959251 / 1000000000) (51989813 / 250000000) (Real.log (1231163 / 1000000)) := by
  have h := reflection_log_11777_neg
  have he : Real.log (1231163 / 1000000) = -Real.log (1000000 / 1231163) := by
    rw [show ((1231163 / 1000000) : ℝ) = ((1000000 / 1231163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11778_neg : (52575259 / 200000000) ≤ -Real.log (768837 / 1000000) ∧
    -Real.log (768837 / 1000000) ≤ (32859537 / 125000000) := by
  have h := checkLog_sound (w := (231163 / 1768837)) (n := 12)
    (lo := (52575259 / 200000000)) (hi := (32859537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768837) = 1/(768837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11778 : Bounds (-32859537 / 125000000) (-52575259 / 200000000) (Real.log (768837 / 1000000)) := by
  have h := reflection_log_11778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11779_neg : (13729261 / 250000000) ≤ -Real.log (946563667431 / 1000000000000) ∧
    -Real.log (946563667431 / 1000000000000) ≤ (10983409 / 200000000) := by
  have h := checkLog_sound (w := (53436332569 / 1946563667431)) (n := 12)
    (lo := (13729261 / 250000000)) (hi := (10983409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 946563667431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 946563667431) = 1/(946563667431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11779 : Bounds (-10983409 / 200000000) (-13729261 / 250000000) (Real.log (946563667431 / 1000000000000)) := by
  have h := reflection_log_11779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11780_neg : (54436113 / 1000000000) ≤ -Real.log (924823251 / 976562500) ∧
    -Real.log (924823251 / 976562500) ≤ (27218057 / 500000000) := by
  have h := checkLog_sound (w := (51739249 / 1901385751)) (n := 12)
    (lo := (54436113 / 1000000000)) (hi := (27218057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 924823251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 924823251) = 1/(924823251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11780 : Bounds (-27218057 / 500000000) (-54436113 / 1000000000) (Real.log (924823251 / 976562500)) := by
  have h := reflection_log_11780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11781_neg : (46875061 / 100000000) ≤ -Real.log (250000000000 / 399499106289) ∧
    -Real.log (250000000000 / 399499106289) ≤ (468750611 / 1000000000) := by
  have h := checkLog_sound (w := (149499106289 / 649499106289)) (n := 12)
    (lo := (46875061 / 100000000)) (hi := (468750611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399499106289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399499106289 / 250000000000) = 1/(250000000000 / 399499106289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11781 : Bounds (46875061 / 100000000) (468750611 / 1000000000) (Real.log (399499106289 / 250000000000)) := by
  have h := reflection_log_11781_neg
  have he : Real.log (399499106289 / 250000000000) = -Real.log (250000000000 / 399499106289) := by
    rw [show ((399499106289 / 250000000000) : ℝ) = ((250000000000 / 399499106289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11782_neg : (235417773 / 500000000) ≤ -Real.log (500000000000 / 800665810829) ∧
    -Real.log (500000000000 / 800665810829) ≤ (470835547 / 1000000000) := by
  have h := checkLog_sound (w := (300665810829 / 1300665810829)) (n := 12)
    (lo := (235417773 / 500000000)) (hi := (470835547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800665810829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800665810829 / 500000000000) = 1/(500000000000 / 800665810829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11782 : Bounds (235417773 / 500000000) (470835547 / 1000000000) (Real.log (800665810829 / 500000000000)) := by
  have h := reflection_log_11782_neg
  have he : Real.log (800665810829 / 500000000000) = -Real.log (500000000000 / 800665810829) := by
    rw [show ((800665810829 / 500000000000) : ℝ) = ((500000000000 / 800665810829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11783_neg : (119300503 / 125000000) ≤ -Real.log (500000000000 / 1298561151079) ∧
    -Real.log (500000000000 / 1298561151079) ≤ (477202013 / 500000000) := by
  have h := checkLog_sound (w := (298561151079 / 2298561151079)) (n := 12)
    (lo := (65314211 / 250000000)) (hi := (52251369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298561151079 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1298561151079 / 1000000000000) = 1/(500000000000 / 1298561151079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11783 : Bounds (119300503 / 125000000) (477202013 / 500000000) (Real.log (1298561151079 / 500000000000)) := by
  have h := reflection_log_11783_neg
  have he : Real.log (1298561151079 / 500000000000) = -Real.log (500000000000 / 1298561151079) := by
    rw [show ((1298561151079 / 500000000000) : ℝ) = ((500000000000 / 1298561151079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11784_neg : (478448243 / 500000000) ≤ -Real.log (250000000000 / 650900900901) ∧
    -Real.log (250000000000 / 650900900901) ≤ (119612061 / 125000000) := by
  have h := checkLog_sound (w := (150900900901 / 1150900900901)) (n := 12)
    (lo := (131874653 / 500000000)) (hi := (263749307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650900900901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(650900900901 / 500000000000) = 1/(250000000000 / 650900900901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11784 : Bounds (478448243 / 500000000) (119612061 / 125000000) (Real.log (650900900901 / 250000000000)) := by
  have h := reflection_log_11784_neg
  have he : Real.log (650900900901 / 250000000000) = -Real.log (250000000000 / 650900900901) := by
    rw [show ((650900900901 / 250000000000) : ℝ) = ((250000000000 / 650900900901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11785_neg : (368801123 / 1000000000) ≤ -Real.log (500 / 723) ∧
    -Real.log (500 / 723) ≤ (92200281 / 250000000) := by
  have h := checkLog_sound (w := (223 / 1223)) (n := 12)
    (lo := (368801123 / 1000000000)) (hi := (92200281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 500) = 1/(500 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11785 : Bounds (368801123 / 1000000000) (92200281 / 250000000) (Real.log (723 / 500)) := by
  have h := reflection_log_11785_neg
  have he : Real.log (723 / 500) = -Real.log (500 / 723) := by
    rw [show ((723 / 500) : ℝ) = ((500 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11786_neg : (4613989 / 7812500) ≤ -Real.log (277 / 500) ∧
    -Real.log (277 / 500) ≤ (590590593 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 777)) (n := 12)
    (lo := (4613989 / 7812500)) (hi := (590590593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 277) = 1/(277 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11786 : Bounds (-590590593 / 1000000000) (-4613989 / 7812500) (Real.log (277 / 500)) := by
  have h := reflection_log_11786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11787_neg : (4459 / 10000000) ≤ -Real.log (500000 / 500223) ∧
    -Real.log (500000 / 500223) ≤ (445901 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 1000223)) (n := 12)
    (lo := (4459 / 10000000)) (hi := (445901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500223 / 500000) = 1/(500000 / 500223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11787 : Bounds (4459 / 10000000) (445901 / 1000000000) (Real.log (500223 / 500000)) := by
  have h := reflection_log_11787_neg
  have he : Real.log (500223 / 500000) = -Real.log (500000 / 500223) := by
    rw [show ((500223 / 500000) : ℝ) = ((500000 / 500223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11788_neg : (446099 / 1000000000) ≤ -Real.log (499777 / 500000) ∧
    -Real.log (499777 / 500000) ≤ (4461 / 10000000) := by
  have h := checkLog_sound (w := (223 / 999777)) (n := 12)
    (lo := (446099 / 1000000000)) (hi := (4461 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499777) = 1/(499777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11788 : Bounds (-4461 / 10000000) (-446099 / 1000000000) (Real.log (499777 / 500000)) := by
  have h := reflection_log_11788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11789_neg : (207611551 / 1000000000) ≤ -Real.log (200000 / 246147) ∧
    -Real.log (200000 / 246147) ≤ (6487861 / 31250000) := by
  have h := checkLog_sound (w := (46147 / 446147)) (n := 12)
    (lo := (207611551 / 1000000000)) (hi := (6487861 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246147 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246147 / 200000) = 1/(200000 / 246147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11789 : Bounds (207611551 / 1000000000) (6487861 / 31250000) (Real.log (246147 / 200000)) := by
  have h := reflection_log_11789_neg
  have he : Real.log (246147 / 200000) = -Real.log (200000 / 246147) := by
    rw [show ((246147 / 200000) : ℝ) = ((200000 / 246147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11790_neg : (52463953 / 200000000) ≤ -Real.log (153853 / 200000) ∧
    -Real.log (153853 / 200000) ≤ (131159883 / 500000000) := by
  have h := checkLog_sound (w := (46147 / 353853)) (n := 12)
    (lo := (52463953 / 200000000)) (hi := (131159883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153853) = 1/(153853 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11790 : Bounds (-131159883 / 500000000) (-52463953 / 200000000) (Real.log (153853 / 200000)) := by
  have h := reflection_log_11790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11791_neg : (104207001 / 500000000) ≤ -Real.log (1000000 / 1231723) ∧
    -Real.log (1000000 / 1231723) ≤ (208414003 / 1000000000) := by
  have h := checkLog_sound (w := (231723 / 2231723)) (n := 12)
    (lo := (104207001 / 500000000)) (hi := (208414003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231723 / 1000000) = 1/(1000000 / 1231723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11791 : Bounds (104207001 / 500000000) (208414003 / 1000000000) (Real.log (1231723 / 1000000)) := by
  have h := reflection_log_11791_neg
  have he : Real.log (1231723 / 1000000) = -Real.log (1000000 / 1231723) := by
    rw [show ((1231723 / 1000000) : ℝ) = ((1000000 / 1231723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11792_neg : (263604933 / 1000000000) ≤ -Real.log (768277 / 1000000) ∧
    -Real.log (768277 / 1000000) ≤ (131802467 / 500000000) := by
  have h := checkLog_sound (w := (231723 / 1768277)) (n := 12)
    (lo := (263604933 / 1000000000)) (hi := (131802467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768277) = 1/(768277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11792 : Bounds (-131802467 / 500000000) (-263604933 / 1000000000) (Real.log (768277 / 1000000)) := by
  have h := reflection_log_11792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11793_neg : (55190931 / 1000000000) ≤ -Real.log (946304451271 / 1000000000000) ∧
    -Real.log (946304451271 / 1000000000000) ≤ (13797733 / 250000000) := by
  have h := checkLog_sound (w := (53695548729 / 1946304451271)) (n := 12)
    (lo := (55190931 / 1000000000)) (hi := (13797733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 946304451271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 946304451271) = 1/(946304451271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11793 : Bounds (-13797733 / 250000000) (-55190931 / 1000000000) (Real.log (946304451271 / 1000000000000)) := by
  have h := reflection_log_11793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11794_neg : (54708213 / 1000000000) ≤ -Real.log (37870454391 / 40000000000) ∧
    -Real.log (37870454391 / 40000000000) ≤ (27354107 / 500000000) := by
  have h := checkLog_sound (w := (2129545609 / 77870454391)) (n := 12)
    (lo := (54708213 / 1000000000)) (hi := (27354107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37870454391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37870454391) = 1/(37870454391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11794 : Bounds (-27354107 / 500000000) (-54708213 / 1000000000) (Real.log (37870454391 / 40000000000)) := by
  have h := reflection_log_11794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11795_neg : (469931317 / 1000000000) ≤ -Real.log (250000000000 / 399971076287) ∧
    -Real.log (250000000000 / 399971076287) ≤ (234965659 / 500000000) := by
  have h := checkLog_sound (w := (149971076287 / 649971076287)) (n := 12)
    (lo := (469931317 / 1000000000)) (hi := (234965659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399971076287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399971076287 / 250000000000) = 1/(250000000000 / 399971076287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11795 : Bounds (469931317 / 1000000000) (234965659 / 500000000) (Real.log (399971076287 / 250000000000)) := by
  have h := reflection_log_11795_neg
  have he : Real.log (399971076287 / 250000000000) = -Real.log (250000000000 / 399971076287) := by
    rw [show ((399971076287 / 250000000000) : ℝ) = ((250000000000 / 399971076287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11796_neg : (94403787 / 200000000) ≤ -Real.log (500000000000 / 801613871039) ∧
    -Real.log (500000000000 / 801613871039) ≤ (59002367 / 125000000) := by
  have h := checkLog_sound (w := (301613871039 / 1301613871039)) (n := 12)
    (lo := (94403787 / 200000000)) (hi := (59002367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801613871039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801613871039 / 500000000000) = 1/(500000000000 / 801613871039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11796 : Bounds (94403787 / 200000000) (59002367 / 125000000) (Real.log (801613871039 / 500000000000)) := by
  have h := reflection_log_11796_neg
  have he : Real.log (801613871039 / 500000000000) = -Real.log (500000000000 / 801613871039) := by
    rw [show ((801613871039 / 500000000000) : ℝ) = ((500000000000 / 801613871039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11797_neg : (478448243 / 500000000) ≤ -Real.log (500000000000 / 1301801801801) ∧
    -Real.log (500000000000 / 1301801801801) ≤ (119612061 / 125000000) := by
  have h := checkLog_sound (w := (301801801801 / 2301801801801)) (n := 12)
    (lo := (131874653 / 500000000)) (hi := (263749307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301801801801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1301801801801 / 1000000000000) = 1/(500000000000 / 1301801801801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11797 : Bounds (478448243 / 500000000) (119612061 / 125000000) (Real.log (1301801801801 / 500000000000)) := by
  have h := reflection_log_11797_neg
  have he : Real.log (1301801801801 / 500000000000) = -Real.log (500000000000 / 1301801801801) := by
    rw [show ((1301801801801 / 500000000000) : ℝ) = ((500000000000 / 1301801801801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11798_neg : (191878343 / 200000000) ≤ -Real.log (4000000000 / 10440433213) ∧
    -Real.log (4000000000 / 10440433213) ≤ (959391717 / 1000000000) := by
  have h := checkLog_sound (w := (2440433213 / 18440433213)) (n := 12)
    (lo := (53248907 / 200000000)) (hi := (33280567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10440433213 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10440433213 / 8000000000) = 1/(4000000000 / 10440433213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11798 : Bounds (191878343 / 200000000) (959391717 / 1000000000) (Real.log (10440433213 / 4000000000)) := by
  have h := reflection_log_11798_neg
  have he : Real.log (10440433213 / 4000000000) = -Real.log (4000000000 / 10440433213) := by
    rw [show ((10440433213 / 4000000000) : ℝ) = ((4000000000 / 10440433213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11799_neg : (369492447 / 1000000000) ≤ -Real.log (1000 / 1447) ∧
    -Real.log (1000 / 1447) ≤ (11546639 / 31250000) := by
  have h := checkLog_sound (w := (447 / 2447)) (n := 12)
    (lo := (369492447 / 1000000000)) (hi := (11546639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1447 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1447 / 1000) = 1/(1000 / 1447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11799 : Bounds (369492447 / 1000000000) (11546639 / 31250000) (Real.log (1447 / 1000)) := by
  have h := reflection_log_11799_neg
  have he : Real.log (1447 / 1000) = -Real.log (1000 / 1447) := by
    rw [show ((1447 / 1000) : ℝ) = ((1000 / 1447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11800_neg : (592397277 / 1000000000) ≤ -Real.log (553 / 1000) ∧
    -Real.log (553 / 1000) ≤ (296198639 / 500000000) := by
  have h := checkLog_sound (w := (447 / 1553)) (n := 12)
    (lo := (592397277 / 1000000000)) (hi := (296198639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 553) = 1/(553 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11800 : Bounds (-296198639 / 500000000) (-592397277 / 1000000000) (Real.log (553 / 1000)) := by
  have h := reflection_log_11800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11801_neg : (4469 / 10000000) ≤ -Real.log (1000000 / 1000447) ∧
    -Real.log (1000000 / 1000447) ≤ (446901 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 2000447)) (n := 12)
    (lo := (4469 / 10000000)) (hi := (446901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000447 / 1000000) = 1/(1000000 / 1000447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11801 : Bounds (4469 / 10000000) (446901 / 1000000000) (Real.log (1000447 / 1000000)) := by
  have h := reflection_log_11801_neg
  have he : Real.log (1000447 / 1000000) = -Real.log (1000000 / 1000447) := by
    rw [show ((1000447 / 1000000) : ℝ) = ((1000000 / 1000447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11802_neg : (447099 / 1000000000) ≤ -Real.log (999553 / 1000000) ∧
    -Real.log (999553 / 1000000) ≤ (4471 / 10000000) := by
  have h := checkLog_sound (w := (447 / 1999553)) (n := 12)
    (lo := (447099 / 1000000000)) (hi := (4471 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999553) = 1/(999553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11802 : Bounds (-4471 / 10000000) (-447099 / 1000000000) (Real.log (999553 / 1000000)) := by
  have h := reflection_log_11802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11803_neg : (13004103 / 62500000) ≤ -Real.log (500000 / 615647) ∧
    -Real.log (500000 / 615647) ≤ (208065649 / 1000000000) := by
  have h := checkLog_sound (w := (115647 / 1115647)) (n := 12)
    (lo := (13004103 / 62500000)) (hi := (208065649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615647 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615647 / 500000) = 1/(500000 / 615647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11803 : Bounds (13004103 / 62500000) (208065649 / 1000000000) (Real.log (615647 / 500000)) := by
  have h := reflection_log_11803_neg
  have he : Real.log (615647 / 500000) = -Real.log (500000 / 615647) := by
    rw [show ((615647 / 500000) : ℝ) = ((500000 / 615647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11804_neg : (263046697 / 1000000000) ≤ -Real.log (384353 / 500000) ∧
    -Real.log (384353 / 500000) ≤ (131523349 / 500000000) := by
  have h := checkLog_sound (w := (115647 / 884353)) (n := 12)
    (lo := (263046697 / 1000000000)) (hi := (131523349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384353) = 1/(384353 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11804 : Bounds (-131523349 / 500000000) (-263046697 / 1000000000) (Real.log (384353 / 500000)) := by
  have h := reflection_log_11804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11805_neg : (104434679 / 500000000) ≤ -Real.log (250000 / 308071) ∧
    -Real.log (250000 / 308071) ≤ (208869359 / 1000000000) := by
  have h := checkLog_sound (w := (58071 / 558071)) (n := 12)
    (lo := (104434679 / 500000000)) (hi := (208869359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308071 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308071 / 250000) = 1/(250000 / 308071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11805 : Bounds (104434679 / 500000000) (208869359 / 1000000000) (Real.log (308071 / 250000)) := by
  have h := reflection_log_11805_neg
  have he : Real.log (308071 / 250000) = -Real.log (250000 / 308071) := by
    rw [show ((308071 / 250000) : ℝ) = ((250000 / 308071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11806_neg : (52867081 / 200000000) ≤ -Real.log (191929 / 250000) ∧
    -Real.log (191929 / 250000) ≤ (132167703 / 500000000) := by
  have h := checkLog_sound (w := (58071 / 441929)) (n := 12)
    (lo := (52867081 / 200000000)) (hi := (132167703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191929) = 1/(191929 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11806 : Bounds (-132167703 / 500000000) (-52867081 / 200000000) (Real.log (191929 / 250000)) := by
  have h := reflection_log_11806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11807_neg : (55466047 / 1000000000) ≤ -Real.log (59127758959 / 62500000000) ∧
    -Real.log (59127758959 / 62500000000) ≤ (866657 / 15625000) := by
  have h := checkLog_sound (w := (3372241041 / 121627758959)) (n := 12)
    (lo := (55466047 / 1000000000)) (hi := (866657 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59127758959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59127758959) = 1/(59127758959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11807 : Bounds (-866657 / 15625000) (-55466047 / 1000000000) (Real.log (59127758959 / 62500000000)) := by
  have h := reflection_log_11807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11808_neg : (6872631 / 125000000) ≤ -Real.log (236625771391 / 250000000000) ∧
    -Real.log (236625771391 / 250000000000) ≤ (54981049 / 1000000000) := by
  have h := checkLog_sound (w := (13374228609 / 486625771391)) (n := 12)
    (lo := (6872631 / 125000000)) (hi := (54981049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236625771391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236625771391) = 1/(236625771391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11808 : Bounds (-54981049 / 1000000000) (-6872631 / 125000000) (Real.log (236625771391 / 250000000000)) := by
  have h := reflection_log_11808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11809_neg : (235556173 / 500000000) ≤ -Real.log (125000000000 / 200221866357) ∧
    -Real.log (125000000000 / 200221866357) ≤ (471112347 / 1000000000) := by
  have h := checkLog_sound (w := (75221866357 / 325221866357)) (n := 12)
    (lo := (235556173 / 500000000)) (hi := (471112347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200221866357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200221866357 / 125000000000) = 1/(125000000000 / 200221866357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11809 : Bounds (235556173 / 500000000) (471112347 / 1000000000) (Real.log (200221866357 / 125000000000)) := by
  have h := reflection_log_11809_neg
  have he : Real.log (200221866357 / 125000000000) = -Real.log (125000000000 / 200221866357) := by
    rw [show ((200221866357 / 125000000000) : ℝ) = ((125000000000 / 200221866357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11810_neg : (473204763 / 1000000000) ≤ -Real.log (25000000000 / 40128250551) ∧
    -Real.log (25000000000 / 40128250551) ≤ (118301191 / 250000000) := by
  have h := checkLog_sound (w := (15128250551 / 65128250551)) (n := 12)
    (lo := (473204763 / 1000000000)) (hi := (118301191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40128250551 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40128250551 / 25000000000) = 1/(25000000000 / 40128250551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11810 : Bounds (473204763 / 1000000000) (118301191 / 250000000) (Real.log (40128250551 / 25000000000)) := by
  have h := reflection_log_11810_neg
  have he : Real.log (40128250551 / 25000000000) = -Real.log (25000000000 / 40128250551) := by
    rw [show ((40128250551 / 25000000000) : ℝ) = ((25000000000 / 40128250551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11811_neg : (191878343 / 200000000) ≤ -Real.log (62500000000 / 163131768953) ∧
    -Real.log (62500000000 / 163131768953) ≤ (959391717 / 1000000000) := by
  have h := checkLog_sound (w := (38131768953 / 288131768953)) (n := 12)
    (lo := (53248907 / 200000000)) (hi := (33280567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163131768953 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(163131768953 / 125000000000) = 1/(62500000000 / 163131768953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11811 : Bounds (191878343 / 200000000) (959391717 / 1000000000) (Real.log (163131768953 / 62500000000)) := by
  have h := reflection_log_11811_neg
  have he : Real.log (163131768953 / 62500000000) = -Real.log (62500000000 / 163131768953) := by
    rw [show ((163131768953 / 62500000000) : ℝ) = ((62500000000 / 163131768953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11812_neg : (240472431 / 250000000) ≤ -Real.log (100000000000 / 261663652803) ∧
    -Real.log (100000000000 / 261663652803) ≤ (480944863 / 500000000) := by
  have h := checkLog_sound (w := (61663652803 / 461663652803)) (n := 12)
    (lo := (16796409 / 62500000)) (hi := (53748509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261663652803 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(261663652803 / 200000000000) = 1/(100000000000 / 261663652803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11812 : Bounds (240472431 / 250000000) (480944863 / 500000000) (Real.log (261663652803 / 100000000000)) := by
  have h := reflection_log_11812_neg
  have he : Real.log (261663652803 / 100000000000) = -Real.log (100000000000 / 261663652803) := by
    rw [show ((261663652803 / 100000000000) : ℝ) = ((100000000000 / 261663652803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11813_neg : (370183293 / 1000000000) ≤ -Real.log (125 / 181) ∧
    -Real.log (125 / 181) ≤ (185091647 / 500000000) := by
  have h := checkLog_sound (w := (28 / 153)) (n := 12)
    (lo := (370183293 / 1000000000)) (hi := (185091647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 125) = 1/(125 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11813 : Bounds (370183293 / 1000000000) (185091647 / 500000000) (Real.log (181 / 125)) := by
  have h := reflection_log_11813_neg
  have he : Real.log (181 / 125) = -Real.log (125 / 181) := by
    rw [show ((181 / 125) : ℝ) = ((125 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11814_neg : (1160561 / 1953125) ≤ -Real.log (69 / 125) ∧
    -Real.log (69 / 125) ≤ (594207233 / 1000000000) := by
  have h := checkLog_sound (w := (28 / 97)) (n := 12)
    (lo := (1160561 / 1953125)) (hi := (594207233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 69) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 69) = 1/(69 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11814 : Bounds (-594207233 / 1000000000) (-1160561 / 1953125) (Real.log (69 / 125)) := by
  have h := reflection_log_11814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11815_neg : (447899 / 1000000000) ≤ -Real.log (15625 / 15632) ∧
    -Real.log (15625 / 15632) ≤ (4479 / 10000000) := by
  have h := checkLog_sound (w := (7 / 31257)) (n := 12)
    (lo := (447899 / 1000000000)) (hi := (4479 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15632 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15632 / 15625) = 1/(15625 / 15632) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11815 : Bounds (447899 / 1000000000) (4479 / 10000000) (Real.log (15632 / 15625)) := by
  have h := reflection_log_11815_neg
  have he : Real.log (15632 / 15625) = -Real.log (15625 / 15632) := by
    rw [show ((15632 / 15625) : ℝ) = ((15625 / 15632) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11816_neg : (4481 / 10000000) ≤ -Real.log (15618 / 15625) ∧
    -Real.log (15618 / 15625) ≤ (448101 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 31243)) (n := 12)
    (lo := (4481 / 10000000)) (hi := (448101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15618) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15618) = 1/(15618 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11816 : Bounds (-448101 / 1000000000) (-4481 / 10000000) (Real.log (15618 / 15625)) := by
  have h := reflection_log_11816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11817_neg : (208520351 / 1000000000) ≤ -Real.log (500000 / 615927) ∧
    -Real.log (500000 / 615927) ≤ (6516261 / 31250000) := by
  have h := checkLog_sound (w := (115927 / 1115927)) (n := 12)
    (lo := (208520351 / 1000000000)) (hi := (6516261 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615927 / 500000) = 1/(500000 / 615927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11817 : Bounds (208520351 / 1000000000) (6516261 / 31250000) (Real.log (615927 / 500000)) := by
  have h := reflection_log_11817_neg
  have he : Real.log (615927 / 500000) = -Real.log (500000 / 615927) := by
    rw [show ((615927 / 500000) : ℝ) = ((500000 / 615927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11818_neg : (263775459 / 1000000000) ≤ -Real.log (384073 / 500000) ∧
    -Real.log (384073 / 500000) ≤ (13188773 / 50000000) := by
  have h := checkLog_sound (w := (115927 / 884073)) (n := 12)
    (lo := (263775459 / 1000000000)) (hi := (13188773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384073) = 1/(384073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11818 : Bounds (-13188773 / 50000000) (-263775459 / 1000000000) (Real.log (384073 / 500000)) := by
  have h := reflection_log_11818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11819_neg : (41864739 / 200000000) ≤ -Real.log (250000 / 308211) ∧
    -Real.log (250000 / 308211) ≤ (13082731 / 62500000) := by
  have h := checkLog_sound (w := (58211 / 558211)) (n := 12)
    (lo := (41864739 / 200000000)) (hi := (13082731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308211 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308211 / 250000) = 1/(250000 / 308211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11819 : Bounds (41864739 / 200000000) (13082731 / 62500000) (Real.log (308211 / 250000)) := by
  have h := reflection_log_11819_neg
  have he : Real.log (308211 / 250000) = -Real.log (250000 / 308211) := by
    rw [show ((308211 / 250000) : ℝ) = ((250000 / 308211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11820_neg : (66266277 / 250000000) ≤ -Real.log (191789 / 250000) ∧
    -Real.log (191789 / 250000) ≤ (265065109 / 1000000000) := by
  have h := checkLog_sound (w := (58211 / 441789)) (n := 12)
    (lo := (66266277 / 250000000)) (hi := (265065109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191789) = 1/(191789 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11820 : Bounds (-265065109 / 1000000000) (-66266277 / 250000000) (Real.log (191789 / 250000)) := by
  have h := reflection_log_11820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11821_neg : (13935353 / 250000000) ≤ -Real.log (59111479479 / 62500000000) ∧
    -Real.log (59111479479 / 62500000000) ≤ (55741413 / 1000000000) := by
  have h := checkLog_sound (w := (3388520521 / 121611479479)) (n := 12)
    (lo := (13935353 / 250000000)) (hi := (55741413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59111479479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59111479479) = 1/(59111479479 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11821 : Bounds (-55741413 / 1000000000) (-13935353 / 250000000) (Real.log (59111479479 / 62500000000)) := by
  have h := reflection_log_11821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11822_neg : (13813777 / 250000000) ≤ -Real.log (236560930671 / 250000000000) ∧
    -Real.log (236560930671 / 250000000000) ≤ (55255109 / 1000000000) := by
  have h := checkLog_sound (w := (13439069329 / 486560930671)) (n := 12)
    (lo := (13813777 / 250000000)) (hi := (55255109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236560930671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236560930671) = 1/(236560930671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11822 : Bounds (-55255109 / 1000000000) (-13813777 / 250000000) (Real.log (236560930671 / 250000000000)) := by
  have h := reflection_log_11822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11823_neg : (472295811 / 1000000000) ≤ -Real.log (250000000000 / 400917924457) ∧
    -Real.log (250000000000 / 400917924457) ≤ (118073953 / 250000000) := by
  have h := checkLog_sound (w := (150917924457 / 650917924457)) (n := 12)
    (lo := (472295811 / 1000000000)) (hi := (118073953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400917924457 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400917924457 / 250000000000) = 1/(250000000000 / 400917924457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11823 : Bounds (472295811 / 1000000000) (118073953 / 250000000) (Real.log (400917924457 / 250000000000)) := by
  have h := reflection_log_11823_neg
  have he : Real.log (400917924457 / 250000000000) = -Real.log (250000000000 / 400917924457) := by
    rw [show ((400917924457 / 250000000000) : ℝ) = ((250000000000 / 400917924457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11824_neg : (474388803 / 1000000000) ≤ -Real.log (125000000000 / 200878960733) ∧
    -Real.log (125000000000 / 200878960733) ≤ (118597201 / 250000000) := by
  have h := checkLog_sound (w := (75878960733 / 325878960733)) (n := 12)
    (lo := (474388803 / 1000000000)) (hi := (118597201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200878960733 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200878960733 / 125000000000) = 1/(125000000000 / 200878960733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11824 : Bounds (474388803 / 1000000000) (118597201 / 250000000) (Real.log (200878960733 / 125000000000)) := by
  have h := reflection_log_11824_neg
  have he : Real.log (200878960733 / 125000000000) = -Real.log (125000000000 / 200878960733) := by
    rw [show ((200878960733 / 125000000000) : ℝ) = ((125000000000 / 200878960733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11825_neg : (240472431 / 250000000) ≤ -Real.log (250000000000 / 654159132007) ∧
    -Real.log (250000000000 / 654159132007) ≤ (480944863 / 500000000) := by
  have h := checkLog_sound (w := (154159132007 / 1154159132007)) (n := 12)
    (lo := (16796409 / 62500000)) (hi := (53748509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654159132007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(654159132007 / 500000000000) = 1/(250000000000 / 654159132007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11825 : Bounds (240472431 / 250000000) (480944863 / 500000000) (Real.log (654159132007 / 250000000000)) := by
  have h := reflection_log_11825_neg
  have he : Real.log (654159132007 / 250000000000) = -Real.log (250000000000 / 654159132007) := by
    rw [show ((654159132007 / 250000000000) : ℝ) = ((250000000000 / 654159132007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11826_neg : (482195263 / 500000000) ≤ -Real.log (500000000000 / 1311594202899) ∧
    -Real.log (500000000000 / 1311594202899) ≤ (7534301 / 7812500) := by
  have h := checkLog_sound (w := (311594202899 / 2311594202899)) (n := 12)
    (lo := (135621673 / 500000000)) (hi := (271243347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311594202899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1311594202899 / 1000000000000) = 1/(500000000000 / 1311594202899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11826 : Bounds (482195263 / 500000000) (7534301 / 7812500) (Real.log (1311594202899 / 500000000000)) := by
  have h := reflection_log_11826_neg
  have he : Real.log (1311594202899 / 500000000000) = -Real.log (500000000000 / 1311594202899) := by
    rw [show ((1311594202899 / 500000000000) : ℝ) = ((500000000000 / 1311594202899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11827_neg : (370873663 / 1000000000) ≤ -Real.log (1000 / 1449) ∧
    -Real.log (1000 / 1449) ≤ (5794901 / 15625000) := by
  have h := checkLog_sound (w := (449 / 2449)) (n := 12)
    (lo := (370873663 / 1000000000)) (hi := (5794901 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449 / 1000) = 1/(1000 / 1449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11827 : Bounds (370873663 / 1000000000) (5794901 / 15625000) (Real.log (1449 / 1000)) := by
  have h := reflection_log_11827_neg
  have he : Real.log (1449 / 1000) = -Real.log (1000 / 1449) := by
    rw [show ((1449 / 1000) : ℝ) = ((1000 / 1449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11828_neg : (596020469 / 1000000000) ≤ -Real.log (551 / 1000) ∧
    -Real.log (551 / 1000) ≤ (59602047 / 100000000) := by
  have h := checkLog_sound (w := (449 / 1551)) (n := 12)
    (lo := (596020469 / 1000000000)) (hi := (59602047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 551) = 1/(551 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11828 : Bounds (-59602047 / 100000000) (-596020469 / 1000000000) (Real.log (551 / 1000)) := by
  have h := reflection_log_11828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11829_neg : (448899 / 1000000000) ≤ -Real.log (1000000 / 1000449) ∧
    -Real.log (1000000 / 1000449) ≤ (4489 / 10000000) := by
  have h := checkLog_sound (w := (449 / 2000449)) (n := 12)
    (lo := (448899 / 1000000000)) (hi := (4489 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000449 / 1000000) = 1/(1000000 / 1000449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11829 : Bounds (448899 / 1000000000) (4489 / 10000000) (Real.log (1000449 / 1000000)) := by
  have h := reflection_log_11829_neg
  have he : Real.log (1000449 / 1000000) = -Real.log (1000000 / 1000449) := by
    rw [show ((1000449 / 1000000) : ℝ) = ((1000000 / 1000449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11830_neg : (4491 / 10000000) ≤ -Real.log (999551 / 1000000) ∧
    -Real.log (999551 / 1000000) ≤ (449101 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 1999551)) (n := 12)
    (lo := (4491 / 10000000)) (hi := (449101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999551) = 1/(999551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11830 : Bounds (-449101 / 1000000000) (-4491 / 10000000) (Real.log (999551 / 1000000)) := by
  have h := reflection_log_11830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11831_neg : (208974847 / 1000000000) ≤ -Real.log (500000 / 616207) ∧
    -Real.log (500000 / 616207) ≤ (408154 / 1953125) := by
  have h := checkLog_sound (w := (116207 / 1116207)) (n := 12)
    (lo := (208974847 / 1000000000)) (hi := (408154 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616207 / 500000) = 1/(500000 / 616207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11831 : Bounds (208974847 / 1000000000) (408154 / 1953125) (Real.log (616207 / 500000)) := by
  have h := reflection_log_11831_neg
  have he : Real.log (616207 / 500000) = -Real.log (500000 / 616207) := by
    rw [show ((616207 / 500000) : ℝ) = ((500000 / 616207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11832_neg : (264504753 / 1000000000) ≤ -Real.log (383793 / 500000) ∧
    -Real.log (383793 / 500000) ≤ (132252377 / 500000000) := by
  have h := checkLog_sound (w := (116207 / 883793)) (n := 12)
    (lo := (264504753 / 1000000000)) (hi := (132252377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383793) = 1/(383793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11832 : Bounds (-132252377 / 500000000) (-264504753 / 1000000000) (Real.log (383793 / 500000)) := by
  have h := reflection_log_11832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11833_neg : (209778637 / 1000000000) ≤ -Real.log (200000 / 246681) ∧
    -Real.log (200000 / 246681) ≤ (104889319 / 500000000) := by
  have h := checkLog_sound (w := (46681 / 446681)) (n := 12)
    (lo := (209778637 / 1000000000)) (hi := (104889319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246681 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246681 / 200000) = 1/(200000 / 246681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11833 : Bounds (209778637 / 1000000000) (104889319 / 500000000) (Real.log (246681 / 200000)) := by
  have h := reflection_log_11833_neg
  have he : Real.log (246681 / 200000) = -Real.log (200000 / 246681) := by
    rw [show ((246681 / 200000) : ℝ) = ((200000 / 246681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11834_neg : (33224581 / 125000000) ≤ -Real.log (153319 / 200000) ∧
    -Real.log (153319 / 200000) ≤ (265796649 / 1000000000) := by
  have h := checkLog_sound (w := (46681 / 353319)) (n := 12)
    (lo := (33224581 / 125000000)) (hi := (265796649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153319) = 1/(153319 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11834 : Bounds (-265796649 / 1000000000) (-33224581 / 125000000) (Real.log (153319 / 200000)) := by
  have h := reflection_log_11834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11835_neg : (5601801 / 100000000) ≤ -Real.log (37820884239 / 40000000000) ∧
    -Real.log (37820884239 / 40000000000) ≤ (56018011 / 1000000000) := by
  have h := checkLog_sound (w := (2179115761 / 77820884239)) (n := 12)
    (lo := (5601801 / 100000000)) (hi := (56018011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37820884239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37820884239) = 1/(37820884239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11835 : Bounds (-56018011 / 1000000000) (-5601801 / 100000000) (Real.log (37820884239 / 40000000000)) := by
  have h := reflection_log_11835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11836_neg : (27764953 / 500000000) ≤ -Real.log (236495933151 / 250000000000) ∧
    -Real.log (236495933151 / 250000000000) ≤ (55529907 / 1000000000) := by
  have h := checkLog_sound (w := (13504066849 / 486495933151)) (n := 12)
    (lo := (27764953 / 500000000)) (hi := (55529907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236495933151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236495933151) = 1/(236495933151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11836 : Bounds (-55529907 / 1000000000) (-27764953 / 500000000) (Real.log (236495933151 / 250000000000)) := by
  have h := reflection_log_11836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11837_neg : (473479601 / 1000000000) ≤ -Real.log (125000000000 / 200696404051) ∧
    -Real.log (125000000000 / 200696404051) ≤ (236739801 / 500000000) := by
  have h := checkLog_sound (w := (75696404051 / 325696404051)) (n := 12)
    (lo := (473479601 / 1000000000)) (hi := (236739801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200696404051 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200696404051 / 125000000000) = 1/(125000000000 / 200696404051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11837 : Bounds (473479601 / 1000000000) (236739801 / 500000000) (Real.log (200696404051 / 125000000000)) := by
  have h := reflection_log_11837_neg
  have he : Real.log (200696404051 / 125000000000) = -Real.log (125000000000 / 200696404051) := by
    rw [show ((200696404051 / 125000000000) : ℝ) = ((125000000000 / 200696404051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11838_neg : (95115057 / 200000000) ≤ -Real.log (500000000000 / 804469765653) ∧
    -Real.log (500000000000 / 804469765653) ≤ (237787643 / 500000000) := by
  have h := checkLog_sound (w := (304469765653 / 1304469765653)) (n := 12)
    (lo := (95115057 / 200000000)) (hi := (237787643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804469765653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804469765653 / 500000000000) = 1/(500000000000 / 804469765653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11838 : Bounds (95115057 / 200000000) (237787643 / 500000000) (Real.log (804469765653 / 500000000000)) := by
  have h := reflection_log_11838_neg
  have he : Real.log (804469765653 / 500000000000) = -Real.log (500000000000 / 804469765653) := by
    rw [show ((804469765653 / 500000000000) : ℝ) = ((500000000000 / 804469765653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11839_neg : (482195263 / 500000000) ≤ -Real.log (250000000000 / 655797101449) ∧
    -Real.log (250000000000 / 655797101449) ≤ (7534301 / 7812500) := by
  have h := checkLog_sound (w := (155797101449 / 1155797101449)) (n := 12)
    (lo := (135621673 / 500000000)) (hi := (271243347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655797101449 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(655797101449 / 500000000000) = 1/(250000000000 / 655797101449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11839 : Bounds (482195263 / 500000000) (7534301 / 7812500) (Real.log (655797101449 / 250000000000)) := by
  have h := reflection_log_11839_neg
  have he : Real.log (655797101449 / 250000000000) = -Real.log (250000000000 / 655797101449) := by
    rw [show ((655797101449 / 250000000000) : ℝ) = ((250000000000 / 655797101449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
