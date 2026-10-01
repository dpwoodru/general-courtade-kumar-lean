import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12736_neg : (541853 / 1000000000) ≤ -Real.log (500000 / 500271) ∧
    -Real.log (500000 / 500271) ≤ (270927 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1000271)) (n := 12)
    (lo := (541853 / 1000000000)) (hi := (270927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500271 / 500000) = 1/(500000 / 500271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12736 : Bounds (541853 / 1000000000) (270927 / 500000000) (Real.log (500271 / 500000)) := by
  have h := reflection_log_12736_neg
  have he : Real.log (500271 / 500000) = -Real.log (500000 / 500271) := by
    rw [show ((500271 / 500000) : ℝ) = ((500000 / 500271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12737_neg : (271073 / 500000000) ≤ -Real.log (499729 / 500000) ∧
    -Real.log (499729 / 500000) ≤ (542147 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 999729)) (n := 12)
    (lo := (271073 / 500000000)) (hi := (542147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499729) = 1/(499729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12737 : Bounds (-542147 / 1000000000) (-271073 / 500000000) (Real.log (499729 / 500000)) := by
  have h := reflection_log_12737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12738_neg : (50112051 / 200000000) ≤ -Real.log (200000 / 256949) ∧
    -Real.log (200000 / 256949) ≤ (978751 / 3906250) := by
  have h := checkLog_sound (w := (56949 / 456949)) (n := 12)
    (lo := (50112051 / 200000000)) (hi := (978751 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256949 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256949 / 200000) = 1/(200000 / 256949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12738 : Bounds (50112051 / 200000000) (978751 / 3906250) (Real.log (256949 / 200000)) := by
  have h := reflection_log_12738_neg
  have he : Real.log (256949 / 200000) = -Real.log (200000 / 256949) := by
    rw [show ((256949 / 200000) : ℝ) = ((200000 / 256949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12739_neg : (83779039 / 250000000) ≤ -Real.log (143051 / 200000) ∧
    -Real.log (143051 / 200000) ≤ (335116157 / 1000000000) := by
  have h := checkLog_sound (w := (56949 / 343051)) (n := 12)
    (lo := (83779039 / 250000000)) (hi := (335116157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 143051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 143051) = 1/(143051 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12739 : Bounds (-335116157 / 1000000000) (-83779039 / 250000000) (Real.log (143051 / 200000)) := by
  have h := reflection_log_12739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12740_neg : (50467603 / 200000000) ≤ -Real.log (1000000 / 1287031) ∧
    -Real.log (1000000 / 1287031) ≤ (7885563 / 31250000) := by
  have h := checkLog_sound (w := (287031 / 2287031)) (n := 12)
    (lo := (50467603 / 200000000)) (hi := (7885563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287031 / 1000000) = 1/(1000000 / 1287031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12740 : Bounds (50467603 / 200000000) (7885563 / 31250000) (Real.log (1287031 / 1000000)) := by
  have h := reflection_log_12740_neg
  have he : Real.log (1287031 / 1000000) = -Real.log (1000000 / 1287031) := by
    rw [show ((1287031 / 1000000) : ℝ) = ((1000000 / 1287031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12741_neg : (338317337 / 1000000000) ≤ -Real.log (712969 / 1000000) ∧
    -Real.log (712969 / 1000000) ≤ (169158669 / 500000000) := by
  have h := checkLog_sound (w := (287031 / 1712969)) (n := 12)
    (lo := (338317337 / 1000000000)) (hi := (169158669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 712969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 712969) = 1/(712969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12741 : Bounds (-169158669 / 500000000) (-338317337 / 1000000000) (Real.log (712969 / 1000000)) := by
  have h := reflection_log_12741_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12742_neg : (42989661 / 500000000) ≤ -Real.log (917613205039 / 1000000000000) ∧
    -Real.log (917613205039 / 1000000000000) ≤ (85979323 / 1000000000) := by
  have h := checkLog_sound (w := (82386794961 / 1917613205039)) (n := 12)
    (lo := (42989661 / 500000000)) (hi := (85979323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 917613205039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 917613205039) = 1/(917613205039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12742 : Bounds (-85979323 / 1000000000) (-42989661 / 500000000) (Real.log (917613205039 / 1000000000000)) := by
  have h := reflection_log_12742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12743_neg : (84555901 / 1000000000) ≤ -Real.log (36756811399 / 40000000000) ∧
    -Real.log (36756811399 / 40000000000) ≤ (42277951 / 500000000) := by
  have h := checkLog_sound (w := (3243188601 / 76756811399)) (n := 12)
    (lo := (84555901 / 1000000000)) (hi := (42277951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36756811399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36756811399) = 1/(36756811399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12743 : Bounds (-42277951 / 500000000) (-84555901 / 1000000000) (Real.log (36756811399 / 40000000000)) := by
  have h := reflection_log_12743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12744_neg : (585676411 / 1000000000) ≤ -Real.log (250000000000 / 449051387267) ∧
    -Real.log (250000000000 / 449051387267) ≤ (146419103 / 250000000) := by
  have h := checkLog_sound (w := (199051387267 / 699051387267)) (n := 12)
    (lo := (585676411 / 1000000000)) (hi := (146419103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449051387267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449051387267 / 250000000000) = 1/(250000000000 / 449051387267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12744 : Bounds (585676411 / 1000000000) (146419103 / 250000000) (Real.log (449051387267 / 250000000000)) := by
  have h := reflection_log_12744_neg
  have he : Real.log (449051387267 / 250000000000) = -Real.log (250000000000 / 449051387267) := by
    rw [show ((449051387267 / 250000000000) : ℝ) = ((250000000000 / 449051387267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12745_neg : (590655353 / 1000000000) ≤ -Real.log (500000000000 / 902585526159) ∧
    -Real.log (500000000000 / 902585526159) ≤ (295327677 / 500000000) := by
  have h := checkLog_sound (w := (402585526159 / 1402585526159)) (n := 12)
    (lo := (590655353 / 1000000000)) (hi := (295327677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902585526159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902585526159 / 500000000000) = 1/(500000000000 / 902585526159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12745 : Bounds (590655353 / 1000000000) (295327677 / 500000000) (Real.log (902585526159 / 500000000000)) := by
  have h := reflection_log_12745_neg
  have he : Real.log (902585526159 / 500000000000) = -Real.log (500000000000 / 902585526159) := by
    rw [show ((902585526159 / 500000000000) : ℝ) = ((500000000000 / 902585526159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12746_neg : (120549009 / 100000000) ≤ -Real.log (500000000000 / 1669197396963) ∧
    -Real.log (500000000000 / 1669197396963) ≤ (301372523 / 250000000) := by
  have h := checkLog_sound (w := (669197396963 / 2669197396963)) (n := 12)
    (lo := (51234291 / 100000000)) (hi := (512342911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1669197396963 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1669197396963 / 1000000000000) = 1/(500000000000 / 1669197396963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12746 : Bounds (120549009 / 100000000) (301372523 / 250000000) (Real.log (1669197396963 / 500000000000)) := by
  have h := reflection_log_12746_neg
  have he : Real.log (1669197396963 / 500000000000) = -Real.log (500000000000 / 1669197396963) := by
    rw [show ((1669197396963 / 500000000000) : ℝ) = ((500000000000 / 1669197396963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12747_neg : (1213966369 / 1000000000) ≤ -Real.log (250000000000 / 841703056769) ∧
    -Real.log (250000000000 / 841703056769) ≤ (1213966371 / 1000000000) := by
  have h := checkLog_sound (w := (341703056769 / 1341703056769)) (n := 12)
    (lo := (520819189 / 1000000000)) (hi := (52081919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841703056769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(841703056769 / 500000000000) = 1/(250000000000 / 841703056769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12747 : Bounds (1213966369 / 1000000000) (1213966371 / 1000000000) (Real.log (841703056769 / 250000000000)) := by
  have h := reflection_log_12747_neg
  have he : Real.log (841703056769 / 250000000000) = -Real.log (250000000000 / 841703056769) := by
    rw [show ((841703056769 / 250000000000) : ℝ) = ((250000000000 / 841703056769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12748_neg : (43502391 / 100000000) ≤ -Real.log (200 / 309) ∧
    -Real.log (200 / 309) ≤ (435023911 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 509)) (n := 12)
    (lo := (43502391 / 100000000)) (hi := (435023911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 200) = 1/(200 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12748 : Bounds (43502391 / 100000000) (435023911 / 1000000000) (Real.log (309 / 200)) := by
  have h := reflection_log_12748_neg
  have he : Real.log (309 / 200) = -Real.log (200 / 309) := by
    rw [show ((309 / 200) : ℝ) = ((200 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12749_neg : (787457859 / 1000000000) ≤ -Real.log (91 / 200) ∧
    -Real.log (91 / 200) ≤ (787457861 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 191)) (n := 12)
    (lo := (94310679 / 1000000000)) (hi := (2357767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 91) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 91) = 1/(91 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12749 : Bounds (-787457861 / 1000000000) (-787457859 / 1000000000) (Real.log (91 / 200)) := by
  have h := reflection_log_12749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12750_neg : (544851 / 1000000000) ≤ -Real.log (200000 / 200109) ∧
    -Real.log (200000 / 200109) ≤ (136213 / 250000000) := by
  have h := checkLog_sound (w := (109 / 400109)) (n := 12)
    (lo := (544851 / 1000000000)) (hi := (136213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200109 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200109 / 200000) = 1/(200000 / 200109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12750 : Bounds (544851 / 1000000000) (136213 / 250000000) (Real.log (200109 / 200000)) := by
  have h := reflection_log_12750_neg
  have he : Real.log (200109 / 200000) = -Real.log (200000 / 200109) := by
    rw [show ((200109 / 200000) : ℝ) = ((200000 / 200109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12751_neg : (136287 / 250000000) ≤ -Real.log (199891 / 200000) ∧
    -Real.log (199891 / 200000) ≤ (545149 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 399891)) (n := 12)
    (lo := (136287 / 250000000)) (hi := (545149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199891) = 1/(199891 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12751 : Bounds (-545149 / 1000000000) (-136287 / 250000000) (Real.log (199891 / 200000)) := by
  have h := reflection_log_12751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12752_neg : (251942453 / 1000000000) ≤ -Real.log (500000 / 643261) ∧
    -Real.log (500000 / 643261) ≤ (125971227 / 500000000) := by
  have h := checkLog_sound (w := (143261 / 1143261)) (n := 12)
    (lo := (251942453 / 1000000000)) (hi := (125971227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643261 / 500000) = 1/(500000 / 643261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12752 : Bounds (251942453 / 1000000000) (125971227 / 500000000) (Real.log (643261 / 500000)) := by
  have h := reflection_log_12752_neg
  have he : Real.log (643261 / 500000) = -Real.log (500000 / 643261) := by
    rw [show ((643261 / 500000) : ℝ) = ((500000 / 643261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12753_neg : (84400919 / 250000000) ≤ -Real.log (356739 / 500000) ∧
    -Real.log (356739 / 500000) ≤ (337603677 / 1000000000) := by
  have h := checkLog_sound (w := (143261 / 856739)) (n := 12)
    (lo := (84400919 / 250000000)) (hi := (337603677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 356739) = 1/(356739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12753 : Bounds (-337603677 / 1000000000) (-84400919 / 250000000) (Real.log (356739 / 500000)) := by
  have h := reflection_log_12753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12754_neg : (50744483 / 200000000) ≤ -Real.log (500000 / 644407) ∧
    -Real.log (500000 / 644407) ≤ (15857651 / 62500000) := by
  have h := checkLog_sound (w := (144407 / 1144407)) (n := 12)
    (lo := (50744483 / 200000000)) (hi := (15857651 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((644407 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(644407 / 500000) = 1/(500000 / 644407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12754 : Bounds (50744483 / 200000000) (15857651 / 62500000) (Real.log (644407 / 500000)) := by
  have h := reflection_log_12754_neg
  have he : Real.log (644407 / 500000) = -Real.log (500000 / 644407) := by
    rw [show ((644407 / 500000) : ℝ) = ((500000 / 644407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12755_neg : (2130133 / 6250000) ≤ -Real.log (355593 / 500000) ∧
    -Real.log (355593 / 500000) ≤ (340821281 / 1000000000) := by
  have h := checkLog_sound (w := (144407 / 855593)) (n := 12)
    (lo := (2130133 / 6250000)) (hi := (340821281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 355593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 355593) = 1/(355593 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12755 : Bounds (-340821281 / 1000000000) (-2130133 / 6250000) (Real.log (355593 / 500000)) := by
  have h := reflection_log_12755_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12756_neg : (5443679 / 62500000) ≤ -Real.log (229146618351 / 250000000000) ∧
    -Real.log (229146618351 / 250000000000) ≤ (17419773 / 200000000) := by
  have h := checkLog_sound (w := (20853381649 / 479146618351)) (n := 12)
    (lo := (5443679 / 62500000)) (hi := (17419773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 229146618351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 229146618351) = 1/(229146618351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12756 : Bounds (-17419773 / 200000000) (-5443679 / 62500000) (Real.log (229146618351 / 250000000000)) := by
  have h := reflection_log_12756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12757_neg : (85661223 / 1000000000) ≤ -Real.log (229476285879 / 250000000000) ∧
    -Real.log (229476285879 / 250000000000) ≤ (10707653 / 125000000) := by
  have h := checkLog_sound (w := (20523714121 / 479476285879)) (n := 12)
    (lo := (85661223 / 1000000000)) (hi := (10707653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 229476285879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 229476285879) = 1/(229476285879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12757 : Bounds (-10707653 / 125000000) (-85661223 / 1000000000) (Real.log (229476285879 / 250000000000)) := by
  have h := reflection_log_12757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12758_neg : (589546129 / 1000000000) ≤ -Real.log (250000000000 / 450792456109) ∧
    -Real.log (250000000000 / 450792456109) ≤ (58954613 / 100000000) := by
  have h := checkLog_sound (w := (200792456109 / 700792456109)) (n := 12)
    (lo := (589546129 / 1000000000)) (hi := (58954613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450792456109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450792456109 / 250000000000) = 1/(250000000000 / 450792456109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12758 : Bounds (589546129 / 1000000000) (58954613 / 100000000) (Real.log (450792456109 / 250000000000)) := by
  have h := reflection_log_12758_neg
  have he : Real.log (450792456109 / 250000000000) = -Real.log (250000000000 / 450792456109) := by
    rw [show ((450792456109 / 250000000000) : ℝ) = ((250000000000 / 450792456109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12759_neg : (118908739 / 200000000) ≤ -Real.log (125000000000 / 226525479973) ∧
    -Real.log (125000000000 / 226525479973) ≤ (37158981 / 62500000) := by
  have h := checkLog_sound (w := (101525479973 / 351525479973)) (n := 12)
    (lo := (118908739 / 200000000)) (hi := (37158981 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226525479973 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226525479973 / 125000000000) = 1/(125000000000 / 226525479973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12759 : Bounds (118908739 / 200000000) (37158981 / 62500000) (Real.log (226525479973 / 125000000000)) := by
  have h := reflection_log_12759_neg
  have he : Real.log (226525479973 / 125000000000) = -Real.log (125000000000 / 226525479973) := by
    rw [show ((226525479973 / 125000000000) : ℝ) = ((125000000000 / 226525479973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12760_neg : (1213966369 / 1000000000) ≤ -Real.log (500000000000 / 1683406113537) ∧
    -Real.log (500000000000 / 1683406113537) ≤ (1213966371 / 1000000000) := by
  have h := checkLog_sound (w := (683406113537 / 2683406113537)) (n := 12)
    (lo := (520819189 / 1000000000)) (hi := (52081919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683406113537 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1683406113537 / 1000000000000) = 1/(500000000000 / 1683406113537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12760 : Bounds (1213966369 / 1000000000) (1213966371 / 1000000000) (Real.log (1683406113537 / 500000000000)) := by
  have h := reflection_log_12760_neg
  have he : Real.log (1683406113537 / 500000000000) = -Real.log (500000000000 / 1683406113537) := by
    rw [show ((1683406113537 / 500000000000) : ℝ) = ((500000000000 / 1683406113537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12761_neg : (1222481769 / 1000000000) ≤ -Real.log (500000000000 / 1697802197803) ∧
    -Real.log (500000000000 / 1697802197803) ≤ (1222481771 / 1000000000) := by
  have h := checkLog_sound (w := (697802197803 / 2697802197803)) (n := 12)
    (lo := (529334589 / 1000000000)) (hi := (52933459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697802197803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1697802197803 / 1000000000000) = 1/(500000000000 / 1697802197803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12761 : Bounds (1222481769 / 1000000000) (1222481771 / 1000000000) (Real.log (1697802197803 / 500000000000)) := by
  have h := reflection_log_12761_neg
  have he : Real.log (1697802197803 / 500000000000) = -Real.log (500000000000 / 1697802197803) := by
    rw [show ((1697802197803 / 500000000000) : ℝ) = ((500000000000 / 1697802197803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12762_neg : (17478551 / 40000000) ≤ -Real.log (250 / 387) ∧
    -Real.log (250 / 387) ≤ (6827559 / 15625000) := by
  have h := checkLog_sound (w := (137 / 637)) (n := 12)
    (lo := (17478551 / 40000000)) (hi := (6827559 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 250) = 1/(250 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12762 : Bounds (17478551 / 40000000) (6827559 / 15625000) (Real.log (387 / 250)) := by
  have h := reflection_log_12762_neg
  have he : Real.log (387 / 250) = -Real.log (250 / 387) := by
    rw [show ((387 / 250) : ℝ) = ((250 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12763_neg : (397036549 / 500000000) ≤ -Real.log (113 / 250) ∧
    -Real.log (113 / 250) ≤ (7940731 / 10000000) := by
  have h := checkLog_sound (w := (6 / 119)) (n := 12)
    (lo := (50462959 / 500000000)) (hi := (100925919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 113) = 1/(113 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12763 : Bounds (-7940731 / 10000000) (-397036549 / 500000000) (Real.log (113 / 250)) := by
  have h := reflection_log_12763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12764_neg : (547849 / 1000000000) ≤ -Real.log (250000 / 250137) ∧
    -Real.log (250000 / 250137) ≤ (10957 / 20000000) := by
  have h := checkLog_sound (w := (137 / 500137)) (n := 12)
    (lo := (547849 / 1000000000)) (hi := (10957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250137 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250137 / 250000) = 1/(250000 / 250137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12764 : Bounds (547849 / 1000000000) (10957 / 20000000) (Real.log (250137 / 250000)) := by
  have h := reflection_log_12764_neg
  have he : Real.log (250137 / 250000) = -Real.log (250000 / 250137) := by
    rw [show ((250137 / 250000) : ℝ) = ((250000 / 250137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12765_neg : (10963 / 20000000) ≤ -Real.log (249863 / 250000) ∧
    -Real.log (249863 / 250000) ≤ (548151 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 499863)) (n := 12)
    (lo := (10963 / 20000000)) (hi := (548151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249863) = 1/(249863 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12765 : Bounds (-548151 / 1000000000) (-10963 / 20000000) (Real.log (249863 / 250000)) := by
  have h := reflection_log_12765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12766_neg : (31665731 / 125000000) ≤ -Real.log (1000000 / 1288303) ∧
    -Real.log (1000000 / 1288303) ≤ (253325849 / 1000000000) := by
  have h := checkLog_sound (w := (288303 / 2288303)) (n := 12)
    (lo := (31665731 / 125000000)) (hi := (253325849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288303 / 1000000) = 1/(1000000 / 1288303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12766 : Bounds (31665731 / 125000000) (253325849 / 1000000000) (Real.log (1288303 / 1000000)) := by
  have h := reflection_log_12766_neg
  have he : Real.log (1288303 / 1000000) = -Real.log (1000000 / 1288303) := by
    rw [show ((1288303 / 1000000) : ℝ) = ((1000000 / 1288303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12767_neg : (340103019 / 1000000000) ≤ -Real.log (711697 / 1000000) ∧
    -Real.log (711697 / 1000000) ≤ (17005151 / 50000000) := by
  have h := checkLog_sound (w := (288303 / 1711697)) (n := 12)
    (lo := (340103019 / 1000000000)) (hi := (17005151 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711697) = 1/(711697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12767 : Bounds (-17005151 / 50000000) (-340103019 / 1000000000) (Real.log (711697 / 1000000)) := by
  have h := reflection_log_12767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12768_neg : (255108001 / 1000000000) ≤ -Real.log (1000000 / 1290601) ∧
    -Real.log (1000000 / 1290601) ≤ (127554001 / 500000000) := by
  have h := checkLog_sound (w := (290601 / 2290601)) (n := 12)
    (lo := (255108001 / 1000000000)) (hi := (127554001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290601 / 1000000) = 1/(1000000 / 1290601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12768 : Bounds (255108001 / 1000000000) (127554001 / 500000000) (Real.log (1290601 / 1000000)) := by
  have h := reflection_log_12768_neg
  have he : Real.log (1290601 / 1000000) = -Real.log (1000000 / 1290601) := by
    rw [show ((1290601 / 1000000) : ℝ) = ((1000000 / 1290601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12769_neg : (171668573 / 500000000) ≤ -Real.log (709399 / 1000000) ∧
    -Real.log (709399 / 1000000) ≤ (343337147 / 1000000000) := by
  have h := checkLog_sound (w := (290601 / 1709399)) (n := 12)
    (lo := (171668573 / 500000000)) (hi := (343337147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709399) = 1/(709399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12769 : Bounds (-343337147 / 1000000000) (-171668573 / 500000000) (Real.log (709399 / 1000000)) := by
  have h := reflection_log_12769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12770_neg : (11028643 / 125000000) ≤ -Real.log (915551058799 / 1000000000000) ∧
    -Real.log (915551058799 / 1000000000000) ≤ (17645829 / 200000000) := by
  have h := checkLog_sound (w := (84448941201 / 1915551058799)) (n := 12)
    (lo := (11028643 / 125000000)) (hi := (17645829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 915551058799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 915551058799) = 1/(915551058799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12770 : Bounds (-17645829 / 200000000) (-11028643 / 125000000) (Real.log (915551058799 / 1000000000000)) := by
  have h := reflection_log_12770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12771_neg : (86777171 / 1000000000) ≤ -Real.log (916881380191 / 1000000000000) ∧
    -Real.log (916881380191 / 1000000000000) ≤ (21694293 / 250000000) := by
  have h := checkLog_sound (w := (83118619809 / 1916881380191)) (n := 12)
    (lo := (86777171 / 1000000000)) (hi := (21694293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 916881380191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 916881380191) = 1/(916881380191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12771 : Bounds (-21694293 / 250000000) (-86777171 / 1000000000) (Real.log (916881380191 / 1000000000000)) := by
  have h := reflection_log_12771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12772_neg : (148357217 / 250000000) ≤ -Real.log (250000000000 / 452546167821) ∧
    -Real.log (250000000000 / 452546167821) ≤ (593428869 / 1000000000) := by
  have h := checkLog_sound (w := (202546167821 / 702546167821)) (n := 12)
    (lo := (148357217 / 250000000)) (hi := (593428869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452546167821 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452546167821 / 250000000000) = 1/(250000000000 / 452546167821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12772 : Bounds (148357217 / 250000000) (593428869 / 1000000000) (Real.log (452546167821 / 250000000000)) := by
  have h := reflection_log_12772_neg
  have he : Real.log (452546167821 / 250000000000) = -Real.log (250000000000 / 452546167821) := by
    rw [show ((452546167821 / 250000000000) : ℝ) = ((250000000000 / 452546167821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12773_neg : (598445147 / 1000000000) ≤ -Real.log (250000000000 / 454821969019) ∧
    -Real.log (250000000000 / 454821969019) ≤ (149611287 / 250000000) := by
  have h := checkLog_sound (w := (204821969019 / 704821969019)) (n := 12)
    (lo := (598445147 / 1000000000)) (hi := (149611287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454821969019 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454821969019 / 250000000000) = 1/(250000000000 / 454821969019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12773 : Bounds (598445147 / 1000000000) (149611287 / 250000000) (Real.log (454821969019 / 250000000000)) := by
  have h := reflection_log_12773_neg
  have he : Real.log (454821969019 / 250000000000) = -Real.log (250000000000 / 454821969019) := by
    rw [show ((454821969019 / 250000000000) : ℝ) = ((250000000000 / 454821969019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12774_neg : (1222481769 / 1000000000) ≤ -Real.log (250000000000 / 848901098901) ∧
    -Real.log (250000000000 / 848901098901) ≤ (1222481771 / 1000000000) := by
  have h := checkLog_sound (w := (348901098901 / 1348901098901)) (n := 12)
    (lo := (529334589 / 1000000000)) (hi := (52933459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848901098901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(848901098901 / 500000000000) = 1/(250000000000 / 848901098901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12774 : Bounds (1222481769 / 1000000000) (1222481771 / 1000000000) (Real.log (848901098901 / 250000000000)) := by
  have h := reflection_log_12774_neg
  have he : Real.log (848901098901 / 250000000000) = -Real.log (250000000000 / 848901098901) := by
    rw [show ((848901098901 / 250000000000) : ℝ) = ((250000000000 / 848901098901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12775_neg : (1231036873 / 1000000000) ≤ -Real.log (500000000000 / 1712389380531) ∧
    -Real.log (500000000000 / 1712389380531) ≤ (1969659 / 1600000) := by
  have h := checkLog_sound (w := (712389380531 / 2712389380531)) (n := 12)
    (lo := (537889693 / 1000000000)) (hi := (268944847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1712389380531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1712389380531 / 1000000000000) = 1/(500000000000 / 1712389380531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12775 : Bounds (1231036873 / 1000000000) (1969659 / 1600000) (Real.log (1712389380531 / 500000000000)) := by
  have h := reflection_log_12775_neg
  have he : Real.log (1712389380531 / 500000000000) = -Real.log (500000000000 / 1712389380531) := by
    rw [show ((1712389380531 / 500000000000) : ℝ) = ((500000000000 / 1712389380531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12776_neg : (109724971 / 250000000) ≤ -Real.log (1000 / 1551) ∧
    -Real.log (1000 / 1551) ≤ (87779977 / 200000000) := by
  have h := checkLog_sound (w := (551 / 2551)) (n := 12)
    (lo := (109724971 / 250000000)) (hi := (87779977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1000) = 1/(1000 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12776 : Bounds (109724971 / 250000000) (87779977 / 200000000) (Real.log (1551 / 1000)) := by
  have h := reflection_log_12776_neg
  have he : Real.log (1551 / 1000) = -Real.log (1000 / 1551) := by
    rw [show ((1551 / 1000) : ℝ) = ((1000 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12777_neg : (80073239 / 100000000) ≤ -Real.log (449 / 1000) ∧
    -Real.log (449 / 1000) ≤ (100091549 / 125000000) := by
  have h := checkLog_sound (w := (51 / 949)) (n := 12)
    (lo := (10758521 / 100000000)) (hi := (107585211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 449) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 449) = 1/(449 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12777 : Bounds (-100091549 / 125000000) (-80073239 / 100000000) (Real.log (449 / 1000)) := by
  have h := reflection_log_12777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12778_neg : (8607 / 15625000) ≤ -Real.log (1000000 / 1000551) ∧
    -Real.log (1000000 / 1000551) ≤ (550849 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 2000551)) (n := 12)
    (lo := (8607 / 15625000)) (hi := (550849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000551 / 1000000) = 1/(1000000 / 1000551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12778 : Bounds (8607 / 15625000) (550849 / 1000000000) (Real.log (1000551 / 1000000)) := by
  have h := reflection_log_12778_neg
  have he : Real.log (1000551 / 1000000) = -Real.log (1000000 / 1000551) := by
    rw [show ((1000551 / 1000000) : ℝ) = ((1000000 / 1000551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12779_neg : (551151 / 1000000000) ≤ -Real.log (999449 / 1000000) ∧
    -Real.log (999449 / 1000000) ≤ (34447 / 62500000) := by
  have h := checkLog_sound (w := (551 / 1999449)) (n := 12)
    (lo := (551151 / 1000000000)) (hi := (34447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999449) = 1/(999449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12779 : Bounds (-34447 / 62500000) (-551151 / 1000000000) (Real.log (999449 / 1000000)) := by
  have h := reflection_log_12779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12780_neg : (254709657 / 1000000000) ≤ -Real.log (1000000 / 1290087) ∧
    -Real.log (1000000 / 1290087) ≤ (127354829 / 500000000) := by
  have h := checkLog_sound (w := (290087 / 2290087)) (n := 12)
    (lo := (254709657 / 1000000000)) (hi := (127354829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290087 / 1000000) = 1/(1000000 / 1290087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12780 : Bounds (254709657 / 1000000000) (127354829 / 500000000) (Real.log (1290087 / 1000000)) := by
  have h := reflection_log_12780_neg
  have he : Real.log (1290087 / 1000000) = -Real.log (1000000 / 1290087) := by
    rw [show ((1290087 / 1000000) : ℝ) = ((1000000 / 1290087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12781_neg : (342612851 / 1000000000) ≤ -Real.log (709913 / 1000000) ∧
    -Real.log (709913 / 1000000) ≤ (85653213 / 250000000) := by
  have h := checkLog_sound (w := (290087 / 1709913)) (n := 12)
    (lo := (342612851 / 1000000000)) (hi := (85653213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709913) = 1/(709913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12781 : Bounds (-85653213 / 250000000) (-342612851 / 1000000000) (Real.log (709913 / 1000000)) := by
  have h := reflection_log_12781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12782_neg : (64123691 / 250000000) ≤ -Real.log (125000 / 161549) ∧
    -Real.log (125000 / 161549) ≤ (51298953 / 200000000) := by
  have h := checkLog_sound (w := (36549 / 286549)) (n := 12)
    (lo := (64123691 / 250000000)) (hi := (51298953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161549 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161549 / 125000) = 1/(125000 / 161549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12782 : Bounds (64123691 / 250000000) (51298953 / 200000000) (Real.log (161549 / 125000)) := by
  have h := reflection_log_12782_neg
  have he : Real.log (161549 / 125000) = -Real.log (125000 / 161549) := by
    rw [show ((161549 / 125000) : ℝ) = ((125000 / 161549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12783_neg : (34586501 / 100000000) ≤ -Real.log (88451 / 125000) ∧
    -Real.log (88451 / 125000) ≤ (345865011 / 1000000000) := by
  have h := checkLog_sound (w := (36549 / 213451)) (n := 12)
    (lo := (34586501 / 100000000)) (hi := (345865011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88451) = 1/(88451 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12783 : Bounds (-345865011 / 1000000000) (-34586501 / 100000000) (Real.log (88451 / 125000)) := by
  have h := reflection_log_12783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12784_neg : (44685123 / 500000000) ≤ -Real.log (14289170599 / 15625000000) ∧
    -Real.log (14289170599 / 15625000000) ≤ (89370247 / 1000000000) := by
  have h := checkLog_sound (w := (1335829401 / 29914170599)) (n := 12)
    (lo := (44685123 / 500000000)) (hi := (89370247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14289170599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14289170599) = 1/(14289170599 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12784 : Bounds (-89370247 / 1000000000) (-44685123 / 500000000) (Real.log (14289170599 / 15625000000)) := by
  have h := reflection_log_12784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12785_neg : (87903193 / 1000000000) ≤ -Real.log (915849532431 / 1000000000000) ∧
    -Real.log (915849532431 / 1000000000000) ≤ (43951597 / 500000000) := by
  have h := checkLog_sound (w := (84150467569 / 1915849532431)) (n := 12)
    (lo := (87903193 / 1000000000)) (hi := (43951597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 915849532431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 915849532431) = 1/(915849532431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12785 : Bounds (-43951597 / 500000000) (-87903193 / 1000000000) (Real.log (915849532431 / 1000000000000)) := by
  have h := reflection_log_12785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12786_neg : (597322509 / 1000000000) ≤ -Real.log (25000000000 / 45431165509) ∧
    -Real.log (25000000000 / 45431165509) ≤ (59732251 / 100000000) := by
  have h := checkLog_sound (w := (20431165509 / 70431165509)) (n := 12)
    (lo := (597322509 / 1000000000)) (hi := (59732251 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45431165509 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45431165509 / 25000000000) = 1/(25000000000 / 45431165509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12786 : Bounds (597322509 / 1000000000) (59732251 / 100000000) (Real.log (45431165509 / 25000000000)) := by
  have h := reflection_log_12786_neg
  have he : Real.log (45431165509 / 25000000000) = -Real.log (25000000000 / 45431165509) := by
    rw [show ((45431165509 / 25000000000) : ℝ) = ((25000000000 / 45431165509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12787_neg : (24094391 / 40000000) ≤ -Real.log (250000000000 / 456605917401) ∧
    -Real.log (250000000000 / 456605917401) ≤ (18823743 / 31250000) := by
  have h := checkLog_sound (w := (206605917401 / 706605917401)) (n := 12)
    (lo := (24094391 / 40000000)) (hi := (18823743 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456605917401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456605917401 / 250000000000) = 1/(250000000000 / 456605917401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12787 : Bounds (24094391 / 40000000) (18823743 / 31250000) (Real.log (456605917401 / 250000000000)) := by
  have h := reflection_log_12787_neg
  have he : Real.log (456605917401 / 250000000000) = -Real.log (250000000000 / 456605917401) := by
    rw [show ((456605917401 / 250000000000) : ℝ) = ((250000000000 / 456605917401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12788_neg : (1231036873 / 1000000000) ≤ -Real.log (50000000000 / 171238938053) ∧
    -Real.log (50000000000 / 171238938053) ≤ (1969659 / 1600000) := by
  have h := checkLog_sound (w := (71238938053 / 271238938053)) (n := 12)
    (lo := (537889693 / 1000000000)) (hi := (268944847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171238938053 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171238938053 / 100000000000) = 1/(50000000000 / 171238938053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12788 : Bounds (1231036873 / 1000000000) (1969659 / 1600000) (Real.log (171238938053 / 50000000000)) := by
  have h := reflection_log_12788_neg
  have he : Real.log (171238938053 / 50000000000) = -Real.log (50000000000 / 171238938053) := by
    rw [show ((171238938053 / 50000000000) : ℝ) = ((50000000000 / 171238938053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12789_neg : (619816137 / 500000000) ≤ -Real.log (100000000000 / 345434298441) ∧
    -Real.log (100000000000 / 345434298441) ≤ (309908069 / 250000000) := by
  have h := checkLog_sound (w := (145434298441 / 545434298441)) (n := 12)
    (lo := (273242547 / 500000000)) (hi := (109297019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345434298441 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(345434298441 / 200000000000) = 1/(100000000000 / 345434298441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12789 : Bounds (619816137 / 500000000) (309908069 / 250000000) (Real.log (345434298441 / 100000000000)) := by
  have h := reflection_log_12789_neg
  have he : Real.log (345434298441 / 100000000000) = -Real.log (100000000000 / 345434298441) := by
    rw [show ((345434298441 / 100000000000) : ℝ) = ((100000000000 / 345434298441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12790_neg : (440832251 / 1000000000) ≤ -Real.log (500 / 777) ∧
    -Real.log (500 / 777) ≤ (110208063 / 250000000) := by
  have h := checkLog_sound (w := (277 / 1277)) (n := 12)
    (lo := (440832251 / 1000000000)) (hi := (110208063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 500) = 1/(500 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12790 : Bounds (440832251 / 1000000000) (110208063 / 250000000) (Real.log (777 / 500)) := by
  have h := reflection_log_12790_neg
  have he : Real.log (777 / 500) = -Real.log (500 / 777) := by
    rw [show ((777 / 500) : ℝ) = ((500 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12791_neg : (403718163 / 500000000) ≤ -Real.log (223 / 500) ∧
    -Real.log (223 / 500) ≤ (100929541 / 125000000) := by
  have h := checkLog_sound (w := (27 / 473)) (n := 12)
    (lo := (57144573 / 500000000)) (hi := (114289147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 223) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 223) = 1/(223 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12791 : Bounds (-100929541 / 125000000) (-403718163 / 500000000) (Real.log (223 / 500)) := by
  have h := reflection_log_12791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12792_neg : (276923 / 500000000) ≤ -Real.log (500000 / 500277) ∧
    -Real.log (500000 / 500277) ≤ (553847 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1000277)) (n := 12)
    (lo := (276923 / 500000000)) (hi := (553847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500277 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500277 / 500000) = 1/(500000 / 500277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12792 : Bounds (276923 / 500000000) (553847 / 1000000000) (Real.log (500277 / 500000)) := by
  have h := reflection_log_12792_neg
  have he : Real.log (500277 / 500000) = -Real.log (500000 / 500277) := by
    rw [show ((500277 / 500000) : ℝ) = ((500000 / 500277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12793_neg : (554153 / 1000000000) ≤ -Real.log (499723 / 500000) ∧
    -Real.log (499723 / 500000) ≤ (277077 / 500000000) := by
  have h := checkLog_sound (w := (277 / 999723)) (n := 12)
    (lo := (554153 / 1000000000)) (hi := (277077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499723) = 1/(499723 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12793 : Bounds (-277077 / 500000000) (-554153 / 1000000000) (Real.log (499723 / 500000)) := by
  have h := reflection_log_12793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12794_neg : (10243817 / 40000000) ≤ -Real.log (250000 / 322969) ∧
    -Real.log (250000 / 322969) ≤ (128047713 / 500000000) := by
  have h := checkLog_sound (w := (72969 / 572969)) (n := 12)
    (lo := (10243817 / 40000000)) (hi := (128047713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322969 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322969 / 250000) = 1/(250000 / 322969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12794 : Bounds (10243817 / 40000000) (128047713 / 500000000) (Real.log (322969 / 250000)) := by
  have h := reflection_log_12794_neg
  have he : Real.log (322969 / 250000) = -Real.log (250000 / 322969) := by
    rw [show ((322969 / 250000) : ℝ) = ((250000 / 322969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12795_neg : (345136059 / 1000000000) ≤ -Real.log (177031 / 250000) ∧
    -Real.log (177031 / 250000) ≤ (17256803 / 50000000) := by
  have h := checkLog_sound (w := (72969 / 427031)) (n := 12)
    (lo := (345136059 / 1000000000)) (hi := (17256803 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 177031) = 1/(177031 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12795 : Bounds (-17256803 / 50000000) (-345136059 / 1000000000) (Real.log (177031 / 250000)) := by
  have h := reflection_log_12795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12796_neg : (128940963 / 500000000) ≤ -Real.log (500000 / 647093) ∧
    -Real.log (500000 / 647093) ≤ (257881927 / 1000000000) := by
  have h := checkLog_sound (w := (147093 / 1147093)) (n := 12)
    (lo := (128940963 / 500000000)) (hi := (257881927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647093 / 500000) = 1/(500000 / 647093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12796 : Bounds (128940963 / 500000000) (257881927 / 1000000000) (Real.log (647093 / 500000)) := by
  have h := reflection_log_12796_neg
  have he : Real.log (647093 / 500000) = -Real.log (500000 / 647093) := by
    rw [show ((647093 / 500000) : ℝ) = ((500000 / 647093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12797_neg : (87100883 / 250000000) ≤ -Real.log (352907 / 500000) ∧
    -Real.log (352907 / 500000) ≤ (348403533 / 1000000000) := by
  have h := checkLog_sound (w := (147093 / 852907)) (n := 12)
    (lo := (87100883 / 250000000)) (hi := (348403533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352907) = 1/(352907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12797 : Bounds (-348403533 / 1000000000) (-87100883 / 250000000) (Real.log (352907 / 500000)) := by
  have h := reflection_log_12797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12798_neg : (45260803 / 500000000) ≤ -Real.log (228363649351 / 250000000000) ∧
    -Real.log (228363649351 / 250000000000) ≤ (90521607 / 1000000000) := by
  have h := checkLog_sound (w := (21636350649 / 478363649351)) (n := 12)
    (lo := (45260803 / 500000000)) (hi := (90521607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 228363649351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 228363649351) = 1/(228363649351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12798 : Bounds (-90521607 / 1000000000) (-45260803 / 500000000) (Real.log (228363649351 / 250000000000)) := by
  have h := reflection_log_12798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12799_neg : (89040633 / 1000000000) ≤ -Real.log (57175525039 / 62500000000) ∧
    -Real.log (57175525039 / 62500000000) ≤ (44520317 / 500000000) := by
  have h := checkLog_sound (w := (5324474961 / 119675525039)) (n := 12)
    (lo := (89040633 / 1000000000)) (hi := (44520317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57175525039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57175525039) = 1/(57175525039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12799 : Bounds (-44520317 / 500000000) (-89040633 / 1000000000) (Real.log (57175525039 / 62500000000)) := by
  have h := reflection_log_12799_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
